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


let trans_func_names =
  Hashtbl.of_seq (List.to_seq [("sinf", "mpfr_sin");
                               ("cosf", "mpfr_cos")])

let is_transendental_fun vi = Hashtbl.mem trans_func_names vi.vorig_name
let mpfr_trans_func_name = Hashtbl.find trans_func_names


let make_fun_call_instr fn_vi args =
  let call_exp = Cil.new_exp ~loc:unknown_loc
                (Lval (Var(fn_vi), NoOffset))
  in
  let instr = Call (None, call_exp, args, unknown_loc) in
  instr

let make_fn_vi typ name =
    let new_decl = Cil.makeGlobalVar ~temp:false name typ in
    Cil.setFormalsDecl new_decl typ;
    new_decl


let make_fun_call fn_vi args = Cil.mkStmt (Instr (make_fun_call_instr fn_vi args))

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

let var_to_exp vi =
      Cil.new_exp ~loc:unknown_loc
        (Lval (Var(vi), NoOffset))

let varinfos_to_exps vis = List.map var_to_exp vis


let float_to_mpfr_vi fl_vi =
      let m_vi = (Cil.copyVarinfo fl_vi (fl_vi.vname ^ "_mpfr")) in
      Cil.update_var_type m_vi mpfr_type;
      m_vi

let oper_to_mpfr_fn_vi oper =
let args = [
("rop", mpfr_type, []);
("op1", mpfr_type, []);
("op2", mpfr_type, []);
("rnd", mpfr_rnd_type, [])
]
in
let f = Ast.get () in
let op_fn_name = match oper with
| PlusA -> "mpfr_add"
| MinusA -> "mpfr_sub"
| Mult -> "mpfr_mul"
| Div -> "mpfr_div"
| _ -> Kernel.fatal "unsopported binop"
in
Cil.findOrCreateFunc f op_fn_name
(TFun(Cil.intType, Some args, false, []))

let make_binop_mpfr a_vi b_vi r_vi oper rnd =
  let vi = oper_to_mpfr_fn_vi oper in
  let args = varinfos_to_exps [r_vi;a_vi;b_vi] @ [rnd] in
  make_fun_call_instr vi args
  (* call_exp *)

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
  let fn_vi = make_fn_vi t "mpfr_set_prec" in
  Cil.mkStmtOneInstr (make_fun_call_instr fn_vi [Cil.integer ~loc:unknown_loc n])


let get_mpfr_clears_instr vars =
      let args =
        (List.mapi (fun i _ -> ("v" ^ (string_of_int i), mpfr_type, [])) vars)
         @ [("end", mpfr_rnd_type, [])]
      in
      let t = (TFun(Cil.intType, Some args, true, [])) in
      let fn_vi = make_fn_vi t "mpfr_clears" in
      make_fun_call_instr fn_vi ((varinfos_to_exps vars) @ [mpfr_void_ptr_exp])

let get_mpfr_inits_instr vars =
    let args =
      (List.mapi (fun i _ -> ("v" ^ (string_of_int i), mpfr_type, [])) vars)
       @ [("end", mpfr_rnd_type, [])]
    in
    let t = (TFun(Cil.intType, Some args, true, [])) in
    let fn_vi = make_fn_vi t "mpfr_inits" in
    make_fun_call_instr fn_vi ((varinfos_to_exps vars) @ [mpfr_void_ptr_exp])

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
  let (to_exp,from_exp) = (var_to_exp to', var_to_exp from) in
  make_fun_call_instr fn_vi [to_exp; from_exp; rnd]

  (* mpfr_add(res1, tmp1, res1, MPFR_RNDN); *)
    (* Call of lval option * exp * exp list * location *)
(* Create a call instr to mpfr_set_flt, from a float constant fl to variable vi *)
let mpfr_set_const_instr fl vi rnd =
  let args = [
    ("rop", mpfr_type, []);
    ("op", mpfr_type, []);
    ("rnd", mpfr_rnd_type, [])
  ]
  in
  let t = (TFun(Cil.intType, Some args, false, [])) in
  let fn_vi = make_fn_vi t "mpfr_set_flt" in
  let fl_enode = Const (CReal (fl, FFloat, None)) in
  let fl_exp = Cil.new_exp ~loc:unknown_loc fl_enode in
  let vi_exp = var_to_exp vi in
  make_fun_call_instr fn_vi [vi_exp; fl_exp; rnd]



let float_to_mpfr_vi fl_vi =
  let m_vi = (Cil.copyVarinfo fl_vi (fl_vi.vname ^ "_mpfr")) in
  Cil.update_var_type m_vi mpfr_type;
  m_vi


let extract_from_flt_eq p =
    match p with
      | Papp ({l_var_info={lv_name="flteq";_}; _}, _, [e; r; d]) ->
        Some (e,r)
      | _ -> None

let is_int vi = Cil.isIntegralType vi.vtype
let is_char_ptr_ptr vi = match vi.vtype with
  | TPtr (t, _) -> Cil.isAnyCharPtrType t
  | _ -> false
