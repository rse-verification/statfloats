open Cil_types



module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module IntMap = Map.Make(Int)

module ViHashtbl = Hashtbl.Make(struct
        type t = varinfo
        let equal = (fun x y -> x.vorig_name = y.vorig_name)
        let hash = Hashtbl.hash
      end)

let unknown_loc = Cil_datatype.Location.unknown
let zero_exp = Cil.integer ~loc:unknown_loc 0
let null_exp = Cil.mkCast
let rnd_exp = Cil.integer ~loc:unknown_loc 0






let mpfr_include_global = GText "#include \"mpfr.h\""
let math_include_global = GText "#include \"math.h\""
let include_flsmc = GText "#include \"../flsmc.h\""


let trans_func_names =
  Hashtbl.of_seq (List.to_seq [("sinf", "mpfr_sin");
                               ("cosf", "mpfr_cos");
                               ("sqrtf", "mpfr_sqrt")])

let is_transendental_fun vi = Hashtbl.mem trans_func_names vi.vorig_name
let mpfr_trans_func_name = Hashtbl.find trans_func_names

let vi_to_varlval vi = (Var(vi), NoOffset)

let make_fun_call_exp fn_vi =
  Cil.new_exp ~loc:unknown_loc (Lval (vi_to_varlval fn_vi))

let make_fun_call_instr ?res:(res_vi_lval = None) fn_vi args =
  let call_exp = make_fun_call_exp fn_vi in
  Call (res_vi_lval, call_exp, args, unknown_loc)


let make_fn_vi typ name =
    let new_decl = Cil.makeGlobalVar ~temp:false name typ in
    Cil.setFormalsDecl new_decl typ;
    new_decl


let make_fun_call fn_vi args = Cil.mkStmt (Instr (make_fun_call_instr fn_vi args))

let rec file_ptr_type =
  TPtr(file_type, [])
and file_type =
  TNamed({torig_name = "FILE";
    tname = "FILE";
    ttype = TInt(IInt, []);   (*Hack just for printing, see if it works...*)
    treferenced = false;
  }, [])

let mpfr_rnd_type =
  TNamed({torig_name = "mpfr_rnd_t";
          tname = "mpfr_rnd_t";
          ttype = TInt(IInt, []);   (*Hack just for printing, see if it works...*)
          treferenced = false;
  }, [])

let mpfr_type =
  TNamed({torig_name = "mpfr_t";
    tname = "mpfr_t";
    ttype = TInt(IInt, []);   (*Hack just for printing, see if it works...*)
    treferenced = false;
  }, [])

let mpfr_ptr_type = TPtr (mpfr_type, [])

let mpfr_void_ptr_exp = Cil.mkCast ~newt:mpfr_ptr_type zero_exp

type mpfr_var =
    | Tmp of Cil_types.varinfo
    | Loc of Cil_types.varinfo
    | Glob of Cil_types.varinfo

let mpfr_var_to_vi m_vi = match m_vi with
      | Tmp vi -> vi
      | Loc vi -> vi
      | Glob vi -> vi

let is_tmp_mpfr_vi m_vi = match m_vi with
    | Tmp _ -> true
    | _     -> false

(*Returns true if it is a float, an array of floats, a ptr to a float,
  or a structure containing something that has a float
*)
let rec viHasFloatingType = function
  | TVoid _ -> false
  | TInt _ -> false
  | TFloat _ -> true
  | TPtr (t, _) -> viHasFloatingType t
  | TArray (t, _, _) -> viHasFloatingType t
  | TFun (t, Some tl, _, _) ->
    (viHasFloatingType t) ||
      (Seq.exists (fun (_, t', _) -> viHasFloatingType t') (List.to_seq tl))
  | TFun (t, None, _, _) -> (viHasFloatingType t)
  | TNamed (t, _) -> viHasFloatingType t.ttype
  | TComp ({cfields=fs; _}, _) -> (match fs with
    | Some fs' -> Seq.exists (fun f -> viHasFloatingType f.ftype) (List.to_seq fs')
    | None -> false
    )
  | TEnum _ -> false
  | TBuiltin_va_list _ -> false (*I dont know what this is, returning false*)

let var_to_exp vi =
      Cil.new_exp ~loc:unknown_loc
        (Lval (Var(vi), NoOffset))

let lval_to_exp (lh, lo) =
  Cil.new_exp ~loc:unknown_loc
    (Lval (lh, lo))

let varinfos_to_exps vis = List.map var_to_exp vis




(* float_to_mpfr_vi *)
let vi_to_mpfr_with_newtype fl_vi newtype =
      (* let m_vi = (Cil.copyVarinfo fl_vi (fl_vi.vname ^ "_mpfr")) in *)
      let m_vi = Cil_const.copy_with_new_vid fl_vi in
      Cil_const.change_varinfo_name m_vi (fl_vi.vname ^ "_mpfr");
      Cil.update_var_type m_vi newtype;
      m_vi

(*returns true if the operator is a comparison one*)
let is_compare_op = function
  | Lt | Gt | Le | Ge | Eq | Ne ->  true
  | _ -> false

let float_to_mpfr_vi fl_vi = vi_to_mpfr_with_newtype fl_vi mpfr_type

let uop_to_mpfr_fn_vi uop =
  let args = [
              ("rop", mpfr_type, []);
              ("op", mpfr_type, []);
              ("rnd", mpfr_rnd_type, [])
            ]
  in
  let f = Ast.get () in
  let op_fn_name = match uop with
    | Neg -> "mpfr_neg"
    | _ -> Kernel.fatal "only Neg unary op supported for floats"
  in
  Cil.findOrCreateFunc f op_fn_name
    (TFun(Cil.intType, Some args, false, []))

let bop_to_mpfr_fn_vi oper =
  let args =
    if is_compare_op oper then
      [
        ("op1", mpfr_type, []);
        ("op2", mpfr_type, [])
      ]
    else
      [
        ("rop", mpfr_type, []);
        ("op1", mpfr_type, []);
        ("op2", mpfr_type, []);
        ("rnd", mpfr_rnd_type, [])
      ]
  in
  let op_fn_name = match oper with
    | PlusA -> "mpfr_add"
    | MinusA -> "mpfr_sub"
    | Mult -> "mpfr_mul"
    | Div -> "mpfr_div"
    | Gt -> "mpfr_greater_p"
    | Lt -> "mpfr_less_p"
    | Ge -> "mpfr_greaterequal_p"
    | Le -> "mpfr_lessequal_p"
    | Eq -> "mpfr_equal_p"
    | _ -> Kernel.fatal "unsupported binop"
  in
  let f = Ast.get () in
  Cil.findOrCreateFunc f op_fn_name
  (TFun(Cil.intType, Some args, false, []))

let make_unop_mpfr e r uop rnd_exp =
  let vi = uop_to_mpfr_fn_vi uop in
  make_fun_call_instr vi [r;e;rnd_exp]

(*Makes a binop_mpfr instruction. SHould inly be used for arithmetics*)
let make_binop_mpfr a_exp b_exp r_exp oper rnd_exp =
  let vi = bop_to_mpfr_fn_vi oper in
  make_fun_call_instr vi [r_exp;a_exp;b_exp;rnd_exp]

let make_cmp_binop_mpfr a_exp b_exp r_lval oper =
  let vi = bop_to_mpfr_fn_vi oper in
  make_fun_call_instr ~res:(Some r_lval) vi [a_exp;b_exp]

let exp_to_vi e = match e.enode with
    | Lval (Var (vi), NoOffset) -> vi
    | CastE _ -> Kernel.fatal "test"
    | Lval _ -> Kernel.fatal "exp_to_vi: %a" Printer.pp_exp e
    | _ -> Kernel.fatal "Not a var here"

let mpfr_trans_fn_vi vi =
    let args = [
      ("rop", mpfr_type, []);
      ("op", mpfr_type, []);
      ("rnd", mpfr_rnd_type, [])
    ]
    in
    let t = (TFun(Cil.intType, Some args, false, [])) in
    make_fn_vi t (mpfr_trans_func_name vi.vorig_name)


let mpfr_set_prec_stmt n =
  let args = [("prec",Cil.intType,[])] in
  let t = (TFun(Cil.intType, Some args, true, [])) in
  let fn_vi = make_fn_vi t "mpfr_set_default_prec" in
  Cil.mkStmtOneInstr (make_fun_call_instr fn_vi [Cil.integer ~loc:unknown_loc n])





let var_offs_to_exp vi offs = Cil.new_exp ~loc:unknown_loc (Lval (Var vi, offs))

(*Not yet supported with e.g. mpfr arrays in structs*)
let mpfr_exps_from_struct_vi vi =
  match vi.vtype with
    | TComp (ci, _) ->
        let fs = Option.get ci.cfields in
        List.filter_map (fun f ->
          if not (f.ftype = mpfr_type) then None
          else Some (var_offs_to_exp vi (Field (f, NoOffset))))
          fs
    | _ -> Kernel.fatal "Dont call this function with non-cinfo vi"

let type_of_const : constant -> typ = function
      | CInt64 (_, ik, _) -> Cil_types.TInt (ik, [])
      | CChr _ -> Cil.intType
      | CStr _ -> Cil.theMachine.stringLiteralType
      | CWStr _ -> TPtr (Cil.theMachine.wcharType, [])
      | CReal (_, fk, _) -> TFloat (fk, [])
      | CEnum _ -> Cil.intType

(*From: https://git.frama-c.com/pub/frama-c/-/blob/master/src/plugins/eva/ast/eva_ast_typing.ml*)
let type_of_exp_node : exp_node -> typ = function
  | Const c -> type_of_const c
  | Lval lv -> Cil.type_remove_qualifier_attributes (Cil.typeOfLval lv)
  | UnOp (_, _, t) -> t
  | BinOp (_, _, _, t) -> t
  | CastE (t, _) -> t
  | AddrOf lv -> TPtr (Cil.typeOfLval lv, [])
  | StartOf lv ->
    match Cil.unrollType (Cil.typeOfLval lv) with
    | TArray (t, _, attrs) -> TPtr (t, attrs)
    | _ ->  assert false




(*returns true if exp_node is a binop expression returning a float value,
  or if it is a comparison between two floats. Might have to add more cases
  in the future.
 *)
let exp_is_float_binop = function
  | BinOp (_, _, _, t) when Cil.isFloatingType t -> true
  | BinOp (bop, a, b, _)
    when is_compare_op bop &&
         Cil.isFloatingType (type_of_exp_node a.enode) &&
         Cil.isFloatingType (type_of_exp_node a.enode)
    -> true
  | _ -> false

(*Make*)
let get_mpfr_initOrClear_instr vars fname =
    let lval_exps = List.concat (List.map (fun vi -> match vi.vtype with
      | TComp _ -> mpfr_exps_from_struct_vi vi
      | t when t = mpfr_type  -> [var_to_exp vi]
      | _ -> Kernel.fatal "only mpfr type or mpfrs in structs supported"
    )
    vars )
    in
    (*Dummy arg names, they dont matter*)
    let args =
      (List.mapi (fun i _ -> ("v" ^ (string_of_int i), mpfr_type, [])) lval_exps)
       @ [("end", mpfr_rnd_type, [])]
    in
    let t = (TFun(Cil.intType, Some args, true, [])) in
    let fn_vi = make_fn_vi t fname in
    make_fun_call_instr fn_vi (lval_exps @ [mpfr_void_ptr_exp])

let get_mpfr_clears_instr vars = get_mpfr_initOrClear_instr vars "mpfr_clears"
let get_mpfr_inits_instr vars = get_mpfr_initOrClear_instr vars "mpfr_inits"



(* let get_mpfr_clears_instr vars =
    let args =
      (List.mapi (fun i _ -> ("v" ^ (string_of_int i), mpfr_type, [])) vars)
       @ [("end", mpfr_rnd_type, [])]
    in
    let t = (TFun(Cil.intType, Some args, true, [])) in
    let fn_vi = make_fn_vi t "mpfr_clears" in
    make_fun_call_instr fn_vi ((varinfos_to_exps vars) @ [mpfr_void_ptr_exp]) *)

let mpfr_set_str_instr ?(base = 10) ?(rnd=rnd_exp) rop str  =
  let args = [
    ("rop", mpfr_type, []);
    ("rop", Cil.charPtrType, []);
    ("base", Cil.intType, []);
    ("rnd", mpfr_rnd_type, [])
  ]
  in
  let t = (TFun(Cil.intType, Some args, false, [])) in
  let fn_vi = make_fn_vi t "mpfr_set_str" in
  make_fun_call_instr fn_vi [var_to_exp rop; str; rnd]


let mpfr_set_instr to' from rnd =
  (* let (m_to, m_from) = (mpfr_var_to_vi to', mpfr_var_to_vi from) in *)
  let args = [
    ("rop", mpfr_type, []);
    ("op", mpfr_type, []);
    ("rnd", mpfr_rnd_type, [])
  ]
  in
  let t = (TFun(Cil.intType, Some args, false, [])) in
  let fn_vi = make_fn_vi t "mpfr_set" in
  (* let (to_exp,from_exp) = (var_to_exp to', var_to_exp from) in *)
  make_fun_call_instr fn_vi [to'; from; rnd]



  (* mpfr_add(res1, tmp1, res1, MPFR_RNDN); *)
    (* Call of lval option * exp * exp list * location *)
(* Create a call instr to mpfr_set_flt, from a float constant fl to variable vi *)
let mpfr_set_const_instr fl_exp m_exp rnd =
  let args = [
    ("rop", mpfr_type, []);
    ("op", mpfr_type, []);
    ("rnd", mpfr_rnd_type, [])
  ]
  in
  let t = (TFun(Cil.intType, Some args, false, [])) in
  let fn_vi = make_fn_vi t "mpfr_set_flt" in
  make_fun_call_instr fn_vi [m_exp; fl_exp; rnd]

let mpfr_set_const_str_instr flstr vi rnd =
    let args = [
      ("rop", mpfr_type, []);
      ("s", Cil.charPtrType, []);
      ("base", Cil.intType, []);
      ("rnd", mpfr_rnd_type, [])
    ]
    in
    let t = (TFun(Cil.intType, Some args, false, [])) in
    let fn_vi = make_fn_vi t "mpfr_set_str" in
    let fl_enode = Const (CStr flstr) in
    let fl_exp = Cil.new_exp ~loc:unknown_loc fl_enode in
    let vi_exp = var_to_exp vi in
    let base_exp = Cil.integer ~loc:unknown_loc 10 in
    make_fun_call_instr fn_vi [vi_exp; fl_exp; base_exp; rnd]

(* let float_to_mpfr_vi fl_vi =
  let m_vi = (Cil.copyVarinfo fl_vi (fl_vi.vname ^ "_mpfr")) in
  Cil.update_var_type m_vi mpfr_type;
  m_vi *)

let mpfr_get_d_instr from_vi to_vi rnd =
  let args = [
    ("op", mpfr_type, []);
    ("rnd", mpfr_rnd_type, [])
  ]
  in
  let t = (TFun(Cil.doubleType, Some args, false, [])) in
  let fn_vi = make_fn_vi t "mpfr_get_d" in
  let to_vi_exp = var_to_exp to_vi in
  let res_lval = Some (vi_to_varlval from_vi) in
  make_fun_call_instr ~res:res_lval fn_vi [to_vi_exp; rnd]

let mpfr_fprintf_diff_instr file_vi str_exp a_vi b_vi diff_vi rnd =
    let args = [
      ("file", file_ptr_type, []);
      ("str", Cil.charConstPtrType, []);
      ("a", mpfr_type, []);
      ("b", mpfr_type, []);
      ("diff", mpfr_type, []);
    ]
    in
    let t = (TFun(Cil.intType, Some args, true, [])) in
    let fn_vi = make_fn_vi t "mpfr_fprintf" in
    let file_exp = var_to_exp file_vi in
    let a_exp = var_to_exp a_vi in
    let b_exp = var_to_exp b_vi in
    let diff_exp = var_to_exp diff_vi in
    make_fun_call_instr ~res:None fn_vi [file_exp; str_exp; a_exp; b_exp; diff_exp]

let extract_from_flt_eq p =
    match p with
      | Papp ({l_var_info={lv_name="flteq";_}; _}, _, [e; r; d]) ->
        Some (e,r)
      | _ -> None

let is_int vi = Cil.isIntegralType vi.vtype
let is_char_ptr_ptr vi = match vi.vtype with
  | TPtr (t, _) -> Cil.isAnyCharPtrType t
  | _ -> false
