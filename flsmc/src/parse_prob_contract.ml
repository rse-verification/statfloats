open Cil_types
open Logic_typing
open Mpfr_utils
open Logic_const
open Cil
open Selfplugin
open Prob_contract

let type_distribution type_ctxt loc l =
  let res = List.map (type_ctxt.type_term type_ctxt (Lenv.empty())) l in
  Ext_terms res
  (* Ext_annot ("Distribution", res) *)



(* let foo () = () *)
let type_probContract type_ctxt loc [prob; conf; pred] =
  Logic_builtin.add flteq_builtin;
  Self.debug "before creating old";
  (* let env_with_old = enter_post_state (Lenv.empty ()) Normal in *)
  (* let env_with_old = enter_post_state
    (Lenv.add_logic_label "Old" Logic_const.old_label (Lenv.empty ())) Normal in *)
  let env_with_old = type_ctxt.post_state [Normal] in
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



let is_dummy_stmt s = match s.skind with
  (* | Instr (Asm _) -> true *)
  | Instr (Asm (_, ["dummy statement!!"], _, _)) -> true
  | _ -> false



let logic_real_to_exp lr = Cil.kfloat FFloat lr.r_nearest ~loc:unknown_loc




(*
  Class which parses the contract of the entry-function, and converts it into
  the sequence of statements in MPFR-mode by replacing the "dummy statement"
  place holder in the main function
*)
class mpfr_contracts_parser
  mpfr_funcs_names mpfr_structs_map entry_name fmgr =
    object (self)
    inherit (Flosmc_visitor.flosmc_transformer mpfr_funcs_names mpfr_structs_map)

  val mutable diff = 0.1
  val mutable prob = 0.1
  val mutable conf_level = 0.95
  val mutable pred = None
  val mutable entry_vi = None

  val mutable dists = []

  val mutable is_in_old = false

  method make_flteq_contract () =
    if Option.is_none pred then Kernel.fatal "Creating contract with not pred"
    else
      let pc = new flteq_contract in
      pc#set_dists dists;
      let () = match (Option.get pred).pred_content with
        | Papp (li, _, [t1; t2; d]) when li.l_var_info.lv_name = "\\flteq" ->
          pc#set_prob_and_pred t1 t2 d prob;
          pc#set_confLevel conf_level
        | _ -> Kernel.fatal "only flteq expected here"
      in
      pc

  method enter_old = is_in_old <- true
  method exit_old = is_in_old <- false

  method get_diff () = diff

  method set_diff_from_term t = diff <- term_to_fl_const t

    (* prob_contract#set_diff () t *)

  method add_dist d = dists <- d::dists
  method get_dists () = dists

  method init_from_transformer (vis:Flosmc_visitor.flosmc_transformer): unit =
    self#set_tmp_var_queue (vis#get_tmp_var_queue ());
    self#set_res_vars (vis#get_res_vars ());
    self#set_loc_mpfr_vars (vis#get_loc_mpfr_vars ());
    self#set_glob_mpfr_vars (vis#get_glob_mpfr_vars ());
    self#set_fn_mpfr_names_to_vis (vis#get_fn_mpfr_names_to_vis ())

  method logic_var_to_mpfr_vi lv =
    match lv.lv_origin with
      | Some vi ->
        Self.debug ~level:3 "x: %a x2: %a" Printer.pp_logic_var lv Printer.pp_varinfo vi;
        self#get_global_mpfr vi
      | None -> Kernel.fatal "only c-logic vars supperted yet"

  method term_to_instrs ?(res_vi=None) t =
    match t.term_node with
      | TConst (LReal ({r_nearest=fl; r_literal=fl_str;_})) ->
          var_to_exp @@ self#vconst_any fl (Some fl_str)
      | TCast (true, _, t) -> self#term_to_instrs ~res_vi t
      | TLval (th, TNoOffset) ->
        (match th with
          | TVar (lv) -> var_to_exp @@ self#logic_var_to_mpfr_vi lv
          | TResult ty -> var_to_exp (Option.get res_vi)
        )
      | TLval _ -> Kernel.fatal "only nooffset yet implemented"
      | TBinOp (oper, t1, t2) ->
        let a = (self#term_to_instrs ~res_vi t1) in
        let b = (self#term_to_instrs ~res_vi t2) in
        self#vbinop_any a b oper
      | Tat (t, BuiltinLabel Old) ->
        self#enter_old;
        let vexp = self#term_to_instrs ~res_vi t in
        self#exit_old;
        vexp
      | _ -> Kernel.fatal "not const term: %a" Printer.pp_term t


  method get_mpfr_entry_call_instr rvi_option args =
    (* let make_fun_call_instr ?res:(res_vi_lval = None) fn_vi args = *)
    let fn_vi = Option.get (self#get_mpfr_fn_vi entry_name) in
    let args_exp =
        let l = if Option.is_none rvi_option then args
                else args @ [Option.get rvi_option]
        in List.map var_to_exp l
    in
    make_fun_call_instr fn_vi args_exp
    (* Call (Option.map vi_to_varlval rvi_option, var_to_exp vi, [], unknown_loc) *)

  method get_entry_call_instr rvi_option args =
    match entry_vi with
      | Some vi' ->
        make_fun_call_instr
          ~res:(Option.map vi_to_varlval rvi_option)
          vi'
          (List.map var_to_exp args)
      | None -> Kernel.fatal "no entry vi defined"



  method lval_to_mpfr_exp = function
    | (Var vi, off) ->
        let kf = Option.get self#current_kf in
        lval_to_exp (Var (self#get_local_or_glob_mpfr vi kf), off)
    | _ -> Kernel.fatal "Not supported yet with non-var dist vars"

  (* method get_dist_instrs () =
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
         mpfr_set_flt_instr
          (lval_to_exp lval_dvar)
            (self#lval_to_mpfr_exp lval_dvar) rnd_exp
        ]
      else Kernel.fatal "only uniform dist supported"
    in
    List.concat @@ List.map dist_to_instr dists *)

  method term_to_expr ?(res_vi=None) t =
    Self.debug ~level:3 "term: %a" Printer.pp_term t;
    match t.term_node with
      | TLval (tlh, TNoOffset) ->
        (match tlh with
          | TVar lv -> var_to_exp @@ Option.get lv.lv_origin
          | TResult t -> var_to_exp (Option.get res_vi)
          | _ -> Kernel.fatal "not impl yet: %a" Printer.pp_term t)
      | TCast (_, Lreal, t') -> self#term_to_expr ~res_vi t'
      | _ -> Kernel.fatal "not implemented yet term_to_expr"

  method pred_to_spec fl_res_vi mpfr_res_vi dfp sfp =
    let pred = self#get_pred () in
    let kf = Option.get self#current_kf in
    Self.debug ~level:3 "starting pred_to_spec";

    match pred.pred_content with
      | Papp (li, _, [t1; _; d]) when li.l_var_info.lv_name = "\\flteq" ->
        self#set_diff_from_term d;
        let lval_dists = List.map (fun x -> Logic_to_c.term_to_lval x.dvar) dists in
        (*Read samples*)
        let pre1 = make_fscanf_instr (var_to_exp sfp) lval_dists in
        let pres2 = List.map
          (fun lv -> mpfr_set_flt_instr (lval_to_exp lv)
            (self#lval_to_mpfr_exp lv) rnd_exp)
          lval_dists
        in
        (*Get expression to check round-off error for*)
        let t1_mexp_vi = self#term_to_instrs ~res_vi:mpfr_res_vi t1 in
        let t1_flexp = self#term_to_expr ~res_vi:fl_res_vi t1 in
        let t1_fl_mvi = self#fetch_tmp_var kf in
        let post1 = mpfr_set_flt_instr t1_flexp
            (var_to_exp t1_fl_mvi) rnd_exp
        in
        (*Calculate error*)
        let r_vi = self#fetch_tmp_var kf in
        let post2 = make_binop_mpfr
          (t1_mexp_vi) (var_to_exp t1_fl_mvi)
          (var_to_exp r_vi) MinusA rnd_exp
        in
        self#return_tmp_var kf r_vi;
        self#return_tmp_var kf t1_fl_mvi;
        self#return_tmp_var_exp kf t1_mexp_vi;
        (*Print the result*)
        let post3 = self#get_mpfr_print_instr t1_fl_mvi (exp_to_vi t1_mexp_vi) r_vi dfp in
        pre1::pres2, [post1;post2;post3]

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

  method get_mpfr_print_instr flvi rvi diffvi fp_vi =
    let str = "%.32Rf, %.32Rf, %.32Rf\n" in
    let str_exp = new_exp ~loc:unknown_loc (Const (CStr str)) in
    let instr = mpfr_fprintf_diff_instr
      fp_vi str_exp flvi rvi diffvi rnd_exp
    in instr


  method! vfile _ = Cil.DoChildren

  method! vinst _ = Cil.SkipChildren
  method! vvrbl _ = Cil.SkipChildren

  method! vglob_aux g = match g with
    | GFun _ -> Cil.DoChildren
    | _ -> Cil.SkipChildren

  method parse_spec f =
    let f' = Visitor.visitFramacFileCopy
              ((self) :> Visitor.frama_c_copy)
              f
    in
    f'

  method is_in_entry_func () =
    match self#current_kf with
      | None -> false
      | Some kf ->
        Self.debug ~level:3 "%s :: %s" (Kernel_function.get_name kf) entry_name;
        Kernel_function.get_name kf = entry_name

  method! vfunc f =
    let kf = Option.get self#current_kf in
    if self#is_in_entry_func ()
    then (entry_vi <- Some f.svar; Cil.SkipChildren)
    else
      if Kernel_function.get_name kf = "main" then
        (* Self.debug ~level:3 "%s :: %s" (Kernel_function.get_name kf) entry_name; *)
        let fun' = (fun f' -> let f'' = self#add_main_stuff f'  in f'')
                            (* self#add_mpfr_stuff_to_func "main" f'') *)
        in
        (* diff_var <- List.find_opt (fun vi -> vi.vorig_name = "diff" ) f.slocals; *)
        Cil.DoChildrenPost fun'
      else
        Cil.SkipChildren (*Avoid traversing other funcs*)



  method add_main_stuff f =
    let kf = Option.get self#current_kf in
    (*add local vars*)
    let argv_vi = List.find (fun vi -> vi.vorig_name = "argv") f.sformals in
    let dfp = Cil.makeLocalVar f "dfp" file_ptr_type in
    let sfp = Cil.makeLocalVar f "sfp" file_ptr_type in
    let diff = Cil.makeLocalVar f "diff" Cil.doubleType in
    let n = Cil.makeLocalVar f "N" Cil.intType in
    let i = Cil.makeLocalVar f "i" Cil.intType in
    let fl_args = List.map (fun vi -> Cil.makeLocalVar f vi.vorig_name vi.vtype)
        (Cil.getFormalsDecl (Option.get entry_vi))
    in
    let mpfr_args = List.map (self#get_local_mpfr kf) fl_args in
    let entry_type = (Option.get entry_vi).vtype in
    let res_vi = if Cil.isVoidType (Cil.getReturnType entry_type) then None
        else Some (Cil.makeLocalVar f "res" (Cil.getReturnType entry_type))
    in
    let mpfr_res_vi = Option.map (self#get_local_mpfr kf) res_vi in
    let open_file_instr fp fname mode =
      make_fun_call_instr
        ~res:(Some (vi_to_varlval fp))
        (fopen_fn_vi ())
        [Cil.mkString ~loc:unknown_loc fname;
        Cil.mkString ~loc:unknown_loc mode]
    in
    (*Open samples files*)
    let open_sample_file_instr = open_file_instr sfp
      (fmgr#get_samples_path ()) "r" in
    (*Open diff file*)
    let open_diff_file_instr = open_file_instr dfp
      (fmgr#get_diff_path ()) "w" in
    let fprintf_instr =
      make_fun_call_instr
        ~res:None
        (fprintf_fn_vi ())
        [var_to_exp dfp;Cil.mkString ~loc:unknown_loc "float_res, real_res, diff\n"]
    in
    (*Read loop guard, N= atoi(argv[1])*)
    let read_N_instr =
      make_fun_call_instr ~res:(Some (vi_to_varlval n)) (atoi_fn_vi ())
        [Cil.new_exp ~loc:unknown_loc
          (Lval (Var argv_vi, Index (Cil.one ~loc:unknown_loc, NoOffset)))]
    in
    let before_loop_stmts = List.map Cil.mkStmtOneInstr
      [open_sample_file_instr; open_diff_file_instr; fprintf_instr; read_N_instr]
    in
    (*Make loop body*)
    let mpfr_call_instr = self#get_mpfr_entry_call_instr mpfr_res_vi mpfr_args in
    let call_instr = self#get_entry_call_instr res_vi fl_args in
    let pre_instrs, post_instrs =
      self#pred_to_spec res_vi mpfr_res_vi dfp sfp in
    let body = List.map Cil.mkStmtOneInstr
        (pre_instrs @ [mpfr_call_instr;call_instr] @ post_instrs)
    in
    (*Make loop*)
    let loop_stmt = Cil.mkForIncr ~iter:i
      ~first:(Cil.zero ~loc:unknown_loc) ~stopat:(var_to_exp n)
      ~incr:(Cil.one ~loc:unknown_loc) ~body:body ()
    in
    (*Make the block*)
    let ret_stmt = Cil.mkStmt (Return (None, unknown_loc)) in
    let body_block = Cil.mkBlock
      ([mpfr_set_prec_stmt 256] @
        before_loop_stmts @ loop_stmt @ [ret_stmt])
    in
    let tmp_mpfr_locs =
      let q = Hashtbl.find_opt tmp_var_queue (Kernel_function.get_name kf) in
      if Option.is_some q then (Option.get q)#to_list else []
    in
    let loc_vars = ([sfp;dfp;diff;n;i] @ fl_args @ mpfr_args @
        (Option.to_list mpfr_res_vi) @ (Option.to_list res_vi) @ tmp_mpfr_locs)
    in
    body_block.blocals <- loc_vars;
    f.sbody <- body_block;
    f.slocals <- loc_vars;
    self#add_init_clear_stmt f
      ((List.of_seq (ViHashtbl.to_seq_values glob_mpfr_vars)) @ mpfr_args @
        (Option.to_list mpfr_res_vi) @ tmp_mpfr_locs);
    f


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
                 [var_term; {term_node=TConst (LStr "Uniform"); _}; lo_t; hi_t]
                  ->
                  self#add_dist
                    {dvar=var_term;dname="Uniform";dparams=[lo_t;hi_t]}
              | ext -> Kernel.fatal "Not a correct distribution %a"
                          Printer.pp_extended dist
            )
            dists;
          Cil.DoChildren
        | _ -> Kernel.fatal "multiple behaviors not supported"
        )
end
