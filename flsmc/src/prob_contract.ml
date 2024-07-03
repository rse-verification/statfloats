open Cil_types
open Logic_typing
open Mpfr_utils
open Logic_const
open Cil
open Selfplugin

let type_distribution type_ctxt loc l =
  let res = List.map (type_ctxt.type_term type_ctxt (Lenv.empty())) l in
  Ext_terms res
  (* Ext_annot ("Distribution", res) *)

(* let foo () = () *)
let type_probContract type_ctxt loc [prob; conf; pred] =
  Self.debug "before creating old";
  (* let env_with_old = enter_post_state (Lenv.empty ()) Normal in *)
  (* let env_with_old = enter_post_state
    (Lenv.add_logic_label "Old" Logic_const.old_label (Lenv.empty ())) Normal in *)
  let env_with_old = post_state_env Normal Lreal in
  Self.debug "after old'";
  let prob' = type_ctxt.type_term type_ctxt env_with_old prob in
  let conf' = type_ctxt.type_term type_ctxt env_with_old conf in
  Self.debug "after årp'";
  let pred' = type_ctxt.type_predicate type_ctxt env_with_old pred in
  Self.debug "after åred'";
  let ext_prob = new_acsl_extension "prob" unknown_loc false (Ext_terms [prob']) in
  let ext_conf = new_acsl_extension "confLevel" unknown_loc false (Ext_terms [conf']) in
  let ext_pred = new_acsl_extension "probPred" unknown_loc false (Ext_preds [pred']) in
  Ext_annot ("ProbClause", [ext_prob; ext_conf; ext_pred])



let type_prob type_ctxt loc [prob] =
  Ext_terms [type_ctxt.type_term type_ctxt (Lenv.empty ()) prob]
let type_probPred type_ctxt loc [pred] =
  Ext_preds [type_ctxt.type_predicate type_ctxt (Lenv.empty ()) pred]
let type_conf type_ctxt loc [conf] =
  Ext_terms [type_ctxt.type_term type_ctxt (Lenv.empty ()) conf]



let unfold_one_elem = function
  | [x] -> x
  | _ -> Kernel.fatal "tried to extract one element from non-singleton list"

let get_nearest_float_from_lreal_constant t = match t with
  | {term_node = TConst (LReal lr); _} ->
    lr.r_nearest
  | _ -> Kernel.fatal "not lreal constant term"


let get_l_info_name li = li.l_var_info.lv_name

let is_dummy_stmt s = match s.skind with
  (* | Instr (Asm _) -> true *)
  | Instr (Asm (_, ["dummy statement!!"], _, _)) -> true
  | _ -> false


type dist =  {
  dvar: term; (*var as term as can be e.g. struct member*)
  dname: string;
  dparams: logic_real list;
}

let get_dist_var {dvar=t;_} = t
let is_uniform {dname=n; _} = (n = "Uniform")
let get_uniform_params {dname="Uniform";dparams=[lo;hi];_} = (lo,hi)
let logic_real_to_exp lr = Cil.kfloat FFloat lr.r_nearest ~loc:unknown_loc

(*checks last is pred and all prrevious ones are dists*)
let split_into_dist_and_pred l =
  let rev_l = List.rev l in
  let pred = match (List.hd rev_l).ext_kind with
    | Ext_annot ("ProbClause", _) as p -> List.hd rev_l
    |  _ -> Kernel.fatal "last is not prob_ensures"
  in
  let dists = List.rev (List.tl rev_l) in
  List.iter (fun x -> match x with
    | {ext_name="distribution";_} -> ()
    | _ -> Kernel.fatal "Not a distribution where expected one")
    dists;
  (dists, pred)

(*
  Class which parses the contract of the entry-function, and converts it into
  the sequence of statements in MPFR-mode by replacing the "dummy statement"
  place holder in the main function
*)
class mpfr_contracts_parser mpfr_funcs_names mpfr_structs_map entry_name = object (self)
  inherit (Flosmc_visitor.flosmc_transformer mpfr_funcs_names mpfr_structs_map)

  val mutable diff = 0.1
  val mutable prob = 0.1
  val mutable conf_level = 0.95
  val mutable pred = None
  val mutable entry_vi = None

  val mutable dists = []

  val mutable is_in_old = false

  val mutable diff_var = None
  val mutable outfile_vi = None

  method enter_old = is_in_old <- true
  method exit_old = is_in_old <- false

  method get_diff () = diff
  method set_diff_from_term t =
    diff <- match t.term_node with
      | TConst (LReal lr) -> lr.r_nearest
      | _ -> Kernel.fatal "only constants in float for flteq supported"

  method add_dist d = dists <- d::dists

  method init_from_transformer (vis:Flosmc_visitor.flosmc_transformer): unit =
    self#set_tmp_var_queue (vis#get_tmp_var_queue ());
    self#set_res_vars (vis#get_res_vars ());
    self#set_loc_mpfr_vars (vis#get_loc_mpfr_vars ());
    self#set_glob_mpfr_vars (vis#get_glob_mpfr_vars ());
    self#set_fn_mpfr_names_to_vis (vis#get_fn_mpfr_names_to_vis ())

  method logic_var_to_mpfr_vi lv =
    match lv.lv_origin with
      | Some vi ->
        Self.feedback "x: %a x2: %a" Printer.pp_logic_var lv Printer.pp_varinfo vi;
        self#get_global_mpfr vi
      | None -> Kernel.fatal "only c-logic vars supperted yet"

  method term_to_instrs t =
    match t.term_node with
      | TConst (LReal ({r_nearest=fl; r_literal=fl_str;_})) ->
          var_to_exp @@ self#vconst_any fl (Some fl_str)
      | TCast (true, _, t) -> self#term_to_instrs t
      | TLval (TVar lv, _) ->
        var_to_exp @@ self#logic_var_to_mpfr_vi lv
      | TBinOp (oper, t1, t2) ->
        let a = (self#term_to_instrs t1) in
        let b = (self#term_to_instrs t2) in
        self#vbinop_any a b oper
      | Tat (t, BuiltinLabel Old) ->
        self#enter_old;
        let vexp = self#term_to_instrs t in
        self#exit_old;
        vexp
      | _ -> Kernel.fatal "not const term"


  method get_mpfr_entry_call_instr () =
    let vi = Option.get (self#get_mpfr_fn_vi entry_name) in
    Call (None, var_to_exp vi, [], unknown_loc)

  method get_entry_call_instr () =
    match entry_vi with
      | Some vi' -> Call (None, var_to_exp vi', [], unknown_loc)
      | None -> Kernel.fatal "no entry vi defined"


  method lval_to_mpfr_exp = function
    | (Var vi, off) ->
        let kf = Option.get self#current_kf in
        lval_to_exp (Var (self#get_local_or_glob_mpfr vi kf), off)
    | _ -> Kernel.fatal "Not supported yet with non-var dist vars"

  method add_dist_instrs () =
    let kf = Option.get (self#current_kf) in
    let dist_to_instr d =
      Self.feedback "%s" d.dname;
      if is_uniform d then
        let args = [("lo", Cil.floatType, []); ("hi", Cil.floatType, [])] in
        let fn_vi = Cil.findOrCreateFunc (Ast.get ()) "uniform"
                      (TFun(Cil.floatType, Some args, false, []))
        in
        let lval_dvar = Logic_to_c.term_to_lval d.dvar in
        [Call (
          Some lval_dvar,
          var_to_exp fn_vi,
          List.map logic_real_to_exp d.dparams,
          unknown_loc
        )
        ;
         mpfr_set_const_instr
          (lval_to_exp lval_dvar)
            (self#lval_to_mpfr_exp lval_dvar) rnd_exp
        ]
      else Kernel.fatal "only uniform dist supported"
    in
    self#queueInstr @@ List.concat @@ List.map dist_to_instr dists

  method term_to_expr t =
    Self.feedback "term: %a" Printer.pp_term t;
    match t.term_node with
      | TLval (TVar lv, _) ->
        var_to_exp @@ Option.get lv.lv_origin
      | TCast (_, Lreal, t') -> self#term_to_expr t'
      | _ -> Kernel.fatal "not implemented yet term_to_expr"

  method pred_to_spec pred =
    let kf = Option.get self#current_kf in
    Self.feedback "starting pred_to_spec";
    match pred.pred_content with
      | Papp (li, _, [t1; _; d]) when get_l_info_name li = "flteq" ->
        self#set_diff_from_term d;
        let t1_rvi = self#term_to_instrs t1 in
        (* let t2_vi = self#term_to_instrs t2 in *)
        (* self#return_tmp_var kf t1_vi; *)
        let t1_flexp = self#term_to_expr t1 in
        let t1_flvi = self#fetch_tmp_var kf in
        self#queueOneInstr @@ mpfr_set_const_instr t1_flexp
          (var_to_exp t1_flvi) rnd_exp;
        let r_vi = self#fetch_tmp_var kf in
        let sub_inst = make_binop_mpfr
          (t1_rvi) (var_to_exp t1_flvi)
          (var_to_exp r_vi) MinusA rnd_exp
        in
        let to_vi = Option.get diff_var in
        let set_d_inst = mpfr_get_d_instr to_vi r_vi rnd_exp in
        self#return_tmp_var kf r_vi;
        self#return_tmp_var kf t1_flvi;
        self#return_tmp_var_exp kf t1_rvi;
        self#queueInstr [sub_inst; set_d_inst];
        (t1_flvi, t1_rvi, r_vi)
        (* match tl with {}  *)
      | _ -> Kernel.fatal "not implemented yet other preds"



  method get_prob () = prob
  method set_prob p_ext =
    let p = match p_ext.ext_kind with
      (* | Ext_annot ("prob", [{ext_kind=Ext_terms [t];_}]) ->
        0.99 *)
        (* get_nearest_float_from_lreal_constant t *)
      | Ext_terms [t] -> get_nearest_float_from_lreal_constant t
      | _ -> Kernel.fatal "not a single term"
    in
    Self.debug "conf: %f" p;
    prob <- p

  method get_conf_level () = conf_level
  method set_conf_level c_ext =
  let c = match c_ext.ext_kind with
    | Ext_terms [t] ->
      get_nearest_float_from_lreal_constant t
    | _ -> Kernel.fatal "not a single term"
  in
  Self.debug "conf: %f" c;
  conf_level <- c

  method get_pred () = Option.get pred
  method get_option_pred () = pred
  method set_pred pred_ext =
    let p = match pred_ext.ext_kind with
      | Ext_preds [p'] -> p'
      | _ -> Kernel.fatal "nor pred in here"
    in
    pred <- Some p

  method get_mpfr_print_stmt flvi rvi diffvi =
    let str = "%.32Rf, %.32Rf, %.32Rf\n" in
    let str_exp = new_exp ~loc:unknown_loc (Const (CStr str)) in
    let instr = mpfr_fprintf_diff_instr
      (Option.get outfile_vi) str_exp flvi rvi diffvi rnd_exp
    in
    Cil.mkStmtOneInstr instr


  method! vfile _ = Cil.DoChildren

  method! vinst _ = Cil.SkipChildren
  method! vvrbl _ = Cil.SkipChildren

  method! vglob_aux g = match g with
    | GFun _ -> Cil.DoChildren
    | _ -> Cil.SkipChildren

  method parse_spec f =
    Visitor.visitFramacFileCopy
              ((self) :> Visitor.frama_c_copy)
              f
  method is_in_entry_func () =
    match self#current_kf with
      | None -> false
      | Some kf ->
        Self.debug "%s :: %s" (Kernel_function.get_name kf) entry_name;
        Kernel_function.get_name kf = entry_name

  method! vfunc f =
    if self#is_in_entry_func ()
    then (entry_vi <- Some f.svar; Cil.DoChildren)
    else
      if Kernel_function.is_main (Option.get self#current_kf) then
        (outfile_vi <- List.find_opt (fun vi -> vi.vorig_name = "fp" ) f.slocals;
        let fun' = self#add_mpfr_stuff_to_func "main" in
        diff_var <- List.find_opt (fun vi -> vi.vorig_name = "diff" ) f.slocals;
        Cil.DoChildrenPost fun')
      else
        Cil.SkipChildren (*Avoid traversing other funcs*)



  method! vstmt_aux s =
      if not (is_dummy_stmt s)
      then Cil.DoChildren
      else
        (* let instrs = self#pred_to_spec (self#get_pred ()) in
        self#queueInstr instrs; *)
        (
          self#add_dist_instrs ();
          let mpfr_call_instr = self#get_mpfr_entry_call_instr () in
          let call_instr =(self#get_entry_call_instr ()) in
          self#queueInstr [mpfr_call_instr;call_instr];
          let (flvi, rexp, diffvi) = self#pred_to_spec (self#get_pred ()) in
          let stmt = self#get_mpfr_print_stmt flvi (exp_to_vi rexp) diffvi in
          Cil.ChangeTo stmt
        )

  method! vspec s =
    let kf = Option.get self#current_kf in
    if self#is_in_entry_func () |> not then
      Cil.SkipChildren
    else
      (Self.debug "what here: %a" Cil_printer.pp_funspec s;
      match s.spec_behavior with
        | [] ->
          Kernel.fatal "no spec for main func"
        | [{b_extended=l; _}] ->
          let dists, prpred = split_into_dist_and_pred l in
          (match prpred.ext_kind with
            | Ext_annot ("ProbClause", [prob_ext;conf_ext;pred_ext]) ->
              self#set_prob prob_ext;
              self#set_conf_level conf_ext;
              self#set_pred pred_ext
            | _ -> Kernel.fatal "not a prob clause extension"
          );
          List.iter
            (fun dist -> match dist.ext_kind with
              | Ext_terms
                  [var_term;
                   {term_node=TConst (LStr "Uniform"); _};
                   {term_node=TConst (LReal (lo_lr)); _};
                   {term_node=TConst (LReal (hi_lr)); _}]
                  ->
                    self#add_dist {dvar=var_term;dname="Uniform";dparams=[lo_lr;hi_lr]}
              | ext -> Kernel.fatal "Not a correct distribution %a" Printer.pp_extended dist
            )
            dists;
          Cil.DoChildren
        | _ -> Kernel.fatal "multiple behaviors not supported"
        )
end


(* class mpfr_spec_adder entry_name = object (self)
  inherit Visitor.frama_c_inplace
  val mutable entry_point_spec = None
  val mutable input_vars = []

  val mutable main_argc = None
  val mutable main_argv = None

  method add_spec f =
    input_vars <-
      List.filter_map
        ( fun g ->
            match g with
              | GVar (vi, _, _) -> Some vi
              | _ -> None
        )
        f.globals;
    Visitor.visitFramacFileCopy
              ((self) :> Visitor.frama_c_copy)
              f
  method queueOneInstr i = self#queueInstr [i]



  method! vfile f =
    List.iter
      (fun g -> match g with
        | GFun (fd, _) when fd.svar.vorig_name = entry_name ->
            entry_point_spec <- Some fd.sspec
        | _ -> ()
      )
     f.globals;
     if not (Option.is_some entry_point_spec)
     then Kernel.fatal "no entry point spec found"
     else Cil.DoChildren

  method ensures_help (_,id_pred) =
    let _ = extract_from_flt_eq id_pred.ip_content.tp_statement.pred_content in
    id_pred

  method! vfunc f =
    if not (Kernel_function.is_main (Option.get self#current_kf))
    then Cil.SkipChildren
    else
      (
        let () = match f.sformals with
          | [argc; argv] when (is_int argc && is_char_ptr_ptr argv) ->
              main_argc <- Some argc;
              main_argv <- Some argv;
          | _ -> Kernel.fatal "main does not have argc, **argv as params"
        in
        Cil.DoChildren
      )
  (* method! vstmt_aux s =
    if not (s = Cil.dummyStmt)
    then Cil.SkipChildren
    else
      let read_inputs_instrs = self#get_read_input_instrs () in
      (self#queueOneInstr Cil.dummyInstr;
      self#queueOneInstr Cil.dummyInstr;
      Cil.SkipChildren) *)


  method! vbehavior be =
    if Kernel_function.is_entry_point (Option.get self#current_kf) then
      (match be.b_post_cond with
        | [] ->
          Self.debug "spec has no post condition";
          Cil.DoChildren
        | post_li ->
          let new_post = List.map self#ensures_help post_li in
          Cil.DoChildren)
    else
      Cil.DoChildren
end *)
