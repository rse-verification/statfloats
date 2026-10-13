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

let type_equation type_ctxt loc [target; expression] =
  let env = Lenv.empty () in
  Ext_terms [
    type_ctxt.type_term type_ctxt env target;
    type_ctxt.type_term type_ctxt env expression
  ]



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
  let ext_prob = new_acsl_extension ~plugin:"flostat" "prob" unknown_loc false (Ext_terms [prob']) in
  let ext_conf = new_acsl_extension ~plugin:"flostat" "confLevel" unknown_loc false (Ext_terms [conf']) in
  let ext_pred = new_acsl_extension ~plugin:"flostat" "probPred" unknown_loc false (Ext_preds [pred']) in
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

let range_bound_to_int t =
  let rec constant_value t =
    match t.term_node with
    | TConst (Integer (value, _)) -> value
    | TCast (_, _, inner) -> constant_value inner
    | _ ->
      Kernel.fatal "array distribution bounds must be integer constants: %a"
        Printer.pp_term t
  in
  try Z.to_int (constant_value t)
  with Z.Overflow ->
    Kernel.fatal "array distribution bound is outside the supported integer range"

let expand_distribution_var term =
  let rec expand_offset = function
    | TNoOffset -> [TNoOffset]
    | TField (field, rest) ->
      List.map (fun rest' -> TField (field, rest')) (expand_offset rest)
    | TModel _ ->
      Kernel.fatal "array distributions do not support model fields"
    | TIndex (index, rest) ->
      let indices =
        match index.term_node with
        | Trange (Some low, Some high) ->
          let low = range_bound_to_int low in
          let high = range_bound_to_int high in
          if high < low then
            Kernel.fatal "array distribution range has descending bounds";
          let count =
            try Z.to_int (Z.succ (Z.sub (Z.of_int high) (Z.of_int low)))
            with Z.Overflow ->
              Kernel.fatal "array distribution range is too large"
          in
          List.init count (fun offset ->
            Logic_const.tinteger (low + offset))
        | Trange _ ->
          Kernel.fatal "array distribution ranges require constant lower and upper bounds"
        | _ -> [index]
      in
      List.concat_map
        (fun index ->
          List.map (fun rest' -> TIndex (index, rest')) (expand_offset rest))
        indices
  in
  match term.term_node with
  | TLval (host, offset) ->
    List.map
      (fun offset -> {term with term_node = TLval (host, offset)})
      (expand_offset offset)
  | _ ->
    Kernel.fatal "distribution target must be an lvalue: %a" Printer.pp_term term


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
    inherit (Flostat_visitor.flostat_transformer mpfr_funcs_names mpfr_structs_map)

  (* val mutable diff = 0.1 *)
  val mutable prob = 0.1
  val mutable conf_level = 0.95
  val mutable pred = None
  val mutable entry_vi = None

  val mutable dists = []
  val mutable equations = []
  val mutable entry_float_args = []

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

  (* method get_diff () = diff *)

  (* method set_diff_from_term t =
    diff <- term_to_fl_const t *)

    (* prob_contract#set_diff () t *)

  method add_dist d = dists <- d::dists
  method get_dists () = dists
  method add_equation target expression =
    let target_name = Format.asprintf "%a" Printer.pp_term target in
    let is_same_target existing =
      Format.asprintf "%a" Printer.pp_term existing = target_name
    in
    if List.exists (fun dist -> is_same_target dist.dvar) dists then
      Kernel.fatal "equation target also has a distribution: %s" target_name;
    if List.exists (fun (existing, _) -> is_same_target existing) equations then
      Kernel.fatal "equation target is defined more than once: %s" target_name;
    equations <- equations @ [target, expression]

  method init_from_transformer (vis:Flostat_visitor.flostat_transformer): unit =
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

  method entry_arg_for vi =
    match List.find_opt
      (fun arg -> arg.vorig_name = vi.vorig_name)
      entry_float_args
    with
    | Some arg -> arg
    | None ->
      Kernel.fatal "equations can only reference entry-point arguments: %s"
        vi.vorig_name

  method entry_lval_of_term term =
    let lval = Logic_to_c.term_to_lval term in
    match fst lval with
    | Var vi -> Var (self#entry_arg_for vi), snd lval
    | _ -> Kernel.fatal "equation targets and inputs must be entry-point arguments"

  method equation_rhs_to_mpfr term =
    let kf = Option.get self#current_kf in
    match term.term_node with
    | TConst (LReal {r_nearest; r_literal; _}) ->
      let tmp = self#fetch_tmp_var kf in
      let instr = mpfr_set_const_str_instr r_literal tmp rnd_exp in
      [instr], var_to_exp tmp
    | TConst (Integer (value, _)) ->
      let tmp = self#fetch_tmp_var kf in
      [mpfr_set_const_str_instr (Z.to_string value) tmp rnd_exp],
      var_to_exp tmp
    | TCast (_, _, inner) -> self#equation_rhs_to_mpfr inner
    | TUnOp (Neg, inner) ->
      let instrs, operand = self#equation_rhs_to_mpfr inner in
      let tmp = self#fetch_tmp_var kf in
      instrs @ [make_unop_mpfr operand (var_to_exp tmp) Neg rnd_exp],
      var_to_exp tmp
    | TBinOp (operator, left, right) ->
      let left_instrs, left_exp = self#equation_rhs_to_mpfr left in
      let right_instrs, right_exp = self#equation_rhs_to_mpfr right in
      let tmp = self#fetch_tmp_var kf in
      left_instrs @ right_instrs @
        [make_binop_mpfr left_exp right_exp (var_to_exp tmp) operator rnd_exp],
      var_to_exp tmp
    | Tapp (logic_info, _, [argument]) ->
      let fname = logic_info.l_var_info.lv_name in
      let mpfr_name = match fname with
        | "\\sin" | "sin" -> "mpfr_sin"
        | "\\cos" | "cos" -> "mpfr_cos"
        | _ -> Kernel.fatal "equation function not supported: %s" fname
      in
      let argument_instrs, argument_exp =
        self#equation_rhs_to_mpfr argument
      in
      let tmp = self#fetch_tmp_var kf in
      let function_vi = make_fn_vi
        {tnode = TFun(Cil_const.intType,
          Some [("rop", mpfr_type, []); ("op", mpfr_type, []);
                ("rnd", mpfr_rnd_type, [])], false); tattr = []}
        mpfr_name
      in
      argument_instrs @
        [make_fun_call_instr function_vi
          [var_to_exp tmp; argument_exp; rnd_exp]],
      var_to_exp tmp
    | TLval _ ->
      let c_lval = Logic_to_c.term_to_lval term in
      let mapped_lval =
        match fst c_lval with
        | Var vi -> Var (self#entry_arg_for vi), snd c_lval
        | _ -> Kernel.fatal "equation expressions must use entry-point arguments"
      in
      [], self#lval_to_mpfr_exp mapped_lval
    | _ ->
      Kernel.fatal "unsupported equation expression: %a"
        Printer.pp_term term

  method equation_to_instrs (target, expression) =
    let target_lval = self#entry_lval_of_term target in
    if not (Ast_types.is_float (Cil.typeOfLval target_lval)) then
      Kernel.fatal "equation target must have floating-point type: %a"
        Printer.pp_term target;
    let target_mpfr_exp = self#lval_to_mpfr_exp target_lval in
    let rhs_instrs, rhs_exp = self#equation_rhs_to_mpfr expression in
    let set_mpfr = mpfr_set_instr target_mpfr_exp rhs_exp rnd_exp in
    let get_flt_vi = make_fn_vi
      {tnode = TFun(Cil_const.floatType,
        Some [("op", mpfr_type, []); ("rnd", mpfr_rnd_type, [])], false);
       tattr = []}
      "mpfr_get_flt"
    in
    let round_to_float = make_fun_call_instr
      ~res:(Some target_lval) get_flt_vi
      [target_mpfr_exp; rnd_exp]
    in
    let reset_mpfr_from_float =
      mpfr_set_flt_instr (lval_to_exp target_lval)
        target_mpfr_exp rnd_exp
    in
    rhs_instrs @ [set_mpfr; round_to_float; reset_mpfr_from_float]

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



  method lval_to_mpfr_exp lv =
    let kf = Option.get self#current_kf in
    let rec map_lval (host, offset) =
      let host = match host with
        | Var vi ->
            (match self#get_mpfr_type vi.vtype with
            | Some _ -> Var (self#get_local_or_glob_mpfr vi kf)
            | None -> Var vi)
        | Mem exp -> Mem (map_exp exp)
      in
      host, map_offset offset
    and map_exp exp =
      let enode = match exp.enode with
        | Lval lv -> Lval (map_lval lv)
        | AddrOf lv -> AddrOf (map_lval lv)
        | StartOf lv -> StartOf (map_lval lv)
        | CastE (typ, exp) ->
            let typ = Option.value (self#get_mpfr_type typ) ~default:typ in
            CastE (typ, map_exp exp)
        | _ -> exp.enode
      in
      Cil.new_exp ~loc:exp.eloc enode
    and map_offset = function
      | NoOffset -> NoOffset
      | Field (field, rest) ->
          let field =
            match Hashtbl.find_opt mpfr_structs_map field.fcomp with
            | None -> field
            | Some ci ->
                (match ci.cfields with
                | Some fields ->
                    (match List.find_opt
                      (fun candidate -> candidate.fname = field.fname) fields with
                    | Some candidate -> candidate
                    | None ->
                        Kernel.fatal "MPFR struct %s has no field %s"
                          ci.cname field.fname)
                | None ->
                    Kernel.fatal "MPFR struct %s has no field definitions"
                      ci.cname)
          in
          Field (field, map_offset rest)
      | Index (exp, rest) -> Index (map_exp exp, map_offset rest)
    in
    lval_to_exp (map_lval lv)

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
        (* self#set_diff_from_term d; *)
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
    let str_exp = string_to_exp str in
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
    let diff = Cil.makeLocalVar f "diff" Cil_const.doubleType in
    let n = Cil.makeLocalVar f "N" Cil_const.intType in
    let i = Cil.makeLocalVar f "i" Cil_const.intType in
    let fl_args = List.map (fun vi -> Cil.makeLocalVar f vi.vorig_name vi.vtype)
        (Cil.getFormalsDecl (Option.get entry_vi))
    in
    entry_float_args <- fl_args;
    let mpfr_args = List.map (self#get_local_mpfr kf) fl_args in
    let entry_type = (Option.get entry_vi).vtype in
    let res_vi = if Ast_types.is_void (Cil.getReturnType entry_type) then None
        else Some (Cil.makeLocalVar f "res" (Cil.getReturnType entry_type))
    in
    let mpfr_res_vi = Option.map (self#get_local_mpfr kf) res_vi in
    let open_file_instr fp fname mode =
      make_fun_call_instr
        ~res:(Some (vi_to_varlval fp))
        (fopen_fn_vi ())
        [string_to_exp fname; string_to_exp mode]
    in
    (*Open samples files*)
    let open_sample_file_instr = open_file_instr sfp
      (fmgr#get_samples_path ()) "r" in
    let skip_headers_instr =
      make_fun_call_instr
        (fscanf_fn_vi [])
        [var_to_exp sfp;string_to_exp "%*[^\n]\n"]
    in
    (*Open diff file*)
    let open_diff_file_instr = open_file_instr dfp
      (fmgr#get_diff_path ()) "w" in
    let fprintf_instr =
      make_fun_call_instr
        ~res:None
        (fprintf_fn_vi ())
        [var_to_exp dfp;string_to_exp "float_res, real_res, diff\n"]
    in
    (*Read loop guard, N= atoi(argv[1])*)
    let read_N_instr =
      make_fun_call_instr ~res:(Some (vi_to_varlval n)) (atoi_fn_vi ())
        [Cil.new_exp ~loc:unknown_loc
          (Lval (Var argv_vi, Index (Cil.one ~loc:unknown_loc, NoOffset)))]
    in
    let before_loop_stmts = List.map Cil.mkStmtOneInstr
      [open_sample_file_instr; skip_headers_instr; open_diff_file_instr;
        fprintf_instr; read_N_instr]
    in
    (*Make loop body*)
    let mpfr_call_instr = self#get_mpfr_entry_call_instr mpfr_res_vi mpfr_args in
    let call_instr = self#get_entry_call_instr res_vi fl_args in
    let pre_instrs, post_instrs =
      self#pred_to_spec res_vi mpfr_res_vi dfp sfp in
    let equation_instrs =
      List.concat_map self#equation_to_instrs equations
    in
    let body = List.map Cil.mkStmtOneInstr
        (pre_instrs @ equation_instrs @
          [mpfr_call_instr;call_instr] @ post_instrs)
    in
    (*Make loop*)
    let loop_stmt = Cil.mkForIncr ~iter:i
      ~first:(Cil.zero ~loc:unknown_loc) ~stopat:(var_to_exp n)
      ~incr:(Cil.one ~loc:unknown_loc) ~body:body ()
    in
    (*Make the block*)
    let ret_stmt = Cil.mkStmt (Return (None, unknown_loc)) in
    let body_block = Cil.mkBlock
      (before_loop_stmts @ loop_stmt @ [ret_stmt])
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
    self#add_init_clear_stmt
      ~before_init:(Some (mpfr_set_prec_stmt (MPFRPrec.get ()))) f
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
          let spec_dists, prpred = split_into_dist_and_pred l in
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
                  List.iter
                    (fun var_term ->
                      self#add_dist
                        {dvar=var_term;dname="Uniform";dparams=[lo_t;hi_t]})
                    (List.rev (expand_distribution_var var_term))
              | ext -> Kernel.fatal "Not a correct distribution %a"
                          Printer.pp_extended dist
            )
            (List.rev spec_dists);
          List.iter
            (fun equation ->
              match equation.ext_kind with
              | Ext_terms [target; expression] ->
                self#add_equation target expression
              | _ -> Kernel.fatal "equation expects a target and expression")
            (List.filter
              (fun extension -> extension.ext_name = "equation")
              l);
          Cil.DoChildren
        | _ -> Kernel.fatal "multiple behaviors not supported"
        )
end
