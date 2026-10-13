open Cil_types
open Selfplugin
open Ast_types

let unknown_loc = (Filepos.unknown, Filepos.unknown) 
let zero_exp = Cil.integer ~loc:unknown_loc 0
let null_exp = Cil.mkCast
let rnd_exp = Cil.integer ~loc:unknown_loc 0

(* makes string and adds the literal as global var *)
let string_to_exp ?(loc=unknown_loc) s = 
  Cil.evar (Globals.Vars.add_string_literal ~loc:loc (Str s))

let is_result_term t = match t.term_node with
  | TLval (TResult typ, _) -> true
  | _ -> false

let add_fundec_to_cfg ?(loc=unknown_loc) ?(funspec=Cil.empty_funspec ())
      new_fundec new_name =
  let visitor = new Visitor.frama_c_refresh (Project.current()) in
  Cfg.clearCFGinfo ~clear_id:false new_fundec;
  Cfg.cfgFun new_fundec;
  let new_vi = new_fundec.svar in
  new_vi.vname <- new_name;
  let new_funspec =
    Visitor.visitFramacFunspec visitor funspec
  in
  (* Creates the kernel function for the clone function. *)
  let new_kf =
    (* NOTE: it would be better if the replace function would
             return the associated kernel function that is new here *)
    Globals.Functions.replace_by_definition new_funspec new_fundec loc;
    try Globals.Functions.get new_fundec.svar
    with Not_found ->
      Kernel.fatal "No clone kernel function for %s(%d)"
        new_fundec.svar.vname new_fundec.svar.vid
  in
  new_kf


module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module IntMap = Map.Make(Int)

module ViHashtbl = Hashtbl.Make(struct
        type t = varinfo
        let equal = (fun x y -> x.vorig_name = y.vorig_name)
        let hash = Hashtbl.hash
      end)

let type_of_const (c: Cil_types.constant) : Cil_types.typ =
  match c with
    | CInt64 (_, ik, _) -> Cil_const.mk_tint ik
    | CChr _ -> Cil_const.intType
    | CReal (_, fk, _) -> Cil_const.mk_tfloat fk
    | CEnum ei -> Cil.typeOf ei.eival


let include_global fname = GText (Printf.sprintf "#include \"%s\"" fname)
let includes = ["errno.h";"stdlib.h";"stdio.h";"fenv.h";"math.h";"mpfr.h"]
let get_include_list () = List.map include_global includes

let term_binop_to_fl_binop b = match b with
  | PlusA -> (+.)
  | MinusA -> (-.)
  | Mult -> ( *.)
  | Div -> (/.)
  | _ -> Kernel.fatal "not supported binop for float"

let rec term_to_fl_const t = match t.term_node with
  | TConst (LReal lr) -> lr.r_nearest
  | TUnOp (Neg, t) -> -.(term_to_fl_const t)
  | TBinOp (bop, t1, t2) ->
    (term_binop_to_fl_binop bop) (term_to_fl_const t1) (term_to_fl_const t2)
  | _ -> Kernel.fatal "only constants in float expected here"


let trans_func_names =
  Hashtbl.of_seq (List.to_seq [("sinf", "mpfr_sin");
                               ("cosf", "mpfr_cos");
                               ("sqrtf", "mpfr_sqrt");
                               ("pow", "mpfr_pow");
                               ("acosf", "mpfr_acos");
                               ("asinf", "mpfr_asin");
                               ("atanf", "mpfr_atan");
                               ("fabsf", "mpfr_abs")])

let make_id_pred_from_pred_node ?(names=[]) ?(loc=unknown_loc) pn =
  Logic_const.new_predicate {pred_name=names;pred_loc=loc;pred_content=pn}

(*checks last is pred and all prrevious ones are dists*)
let split_into_dist_and_pred l =
  let rev_l = List.rev l in
  let pred = match (List.hd rev_l).ext_kind with
    | Ext_annot ("ProbClause", _) as p -> List.hd rev_l
    |  _ -> Kernel.fatal "last is not prob_ensures"
  in
  let dists = List.rev (List.tl rev_l) in
  List.iter (fun x -> match x with
    | {ext_name="distribution";_} | {ext_name="equation";_} -> ()
    | _ -> Kernel.fatal "Not a distribution where expected one")
    dists;
  (List.filter (fun x -> x.ext_name = "distribution") dists, pred)


let is_transendental_fun vi = Hashtbl.mem trans_func_names vi.vorig_name

let mpfr_trans_func_name = Hashtbl.find trans_func_names

let vi_to_varlval vi = (Var(vi), NoOffset)

(* let make_fun_call_exp fn_vi =
  Cil.new_exp ~loc:unknown_loc (Lval (vi_to_varlval fn_vi)) *)

let make_fun_call_instr ?res:(res_vi_lval = None) fn_vi args =
  (* let call_exp = make_fun_call_exp fn_vi in *)
  Call (res_vi_lval, Var fn_vi, args, unknown_loc)

(*TODO: AVoid making new vi each time function is used*)
let make_fn_vi typ name =
    let new_decl = Cil.makeGlobalVar ~temp:false name typ in
    Cil.setFormalsDecl new_decl typ;
    new_decl


let make_fun_call fn_vi args = Cil.mkStmt (Instr (make_fun_call_instr fn_vi args))

(* let rec file_ptr_type =
  TPtr(file_type, [])
and file_type =
  TNamed({torig_name = "FILE";
    tname = "FILE";
    ttype = TInt(IInt, []);   (*Hack just for printing, see if it works...*)
    treferenced = false;
  }, []) *)

let mpfr_rnd_type =
  {tnode = TNamed{torig_name = "mpfr_rnd_t";
          tname = "mpfr_rnd_t";
          ttype = Cil_const.intType;   (*Hack just for printing, see if it works...*)
          treferenced = false;
  }; tattr = []}

let mpfr_type =
  {tnode = TNamed {torig_name = "mpfr_t";
    tname = "mpfr_t";
    ttype = Cil_const.intType;   (*Hack just for printing, see if it works...*)
    treferenced = false;
    };
   tattr = [];
  }
let mpfr_ptr_type = {tnode = TPtr mpfr_type; tattr = [];}

let mpfr_void_ptr_exp = Cil.mkCast ~newt:mpfr_ptr_type zero_exp

let file_type =
  {tnode = TNamed{torig_name = "FILE";
    tname = "FILE";
    ttype = Cil_const.intType;   (*Hack just for printing, see if it works...*)
    treferenced = false;
  }; 
  tattr = []}

let file_ptr_type = {tnode = TPtr file_type; tattr = []}

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
let hasFloatingType t =
  let rec contains seen t = match t.tnode with
    | TVoid | TInt _ | TEnum _ | TBuiltin_va_list -> false
    | TFloat _ -> true
    | TPtr t' -> contains seen t'
    | TArray (t, _) -> contains seen t
    | TFun (t', Some tl, _) ->
      contains seen t' ||
      Seq.exists (fun (_, t', _) -> contains seen t') (List.to_seq tl)
    | TFun (t', None, _) -> contains seen t'
    | TNamed t -> contains seen t.ttype
    | TComp ci ->
      if Hashtbl.mem seen ci.ckey then false
      else (
        Hashtbl.add seen ci.ckey ();
        match ci.cfields with
        | Some fs -> List.exists (fun f -> contains seen f.ftype) fs
        | None -> false
      )
  in
  contains (Hashtbl.create 10) t

let var_to_exp vi =
      Cil.new_exp ~loc:unknown_loc
        (Lval (Var(vi), NoOffset))

let lval_to_exp (lh, lo) =
  Cil.new_exp ~loc:unknown_loc
    (Lval (lh, lo))

let varinfos_to_exps vis = List.map var_to_exp vis

let flteq_builtin = {
  bl_name="\\flteq";
  bl_labels=[];
  bl_params = ["a"; "b"; "diff"];
  bl_type = None;
  bl_profile=[("a", Lreal); ("b", Lreal); ("diff", Lreal)]
}

let round_error_builtin = {
  bl_name="\\round_error";
  bl_labels=[];
  bl_params = ["x"];
  bl_type = Some Lreal;
  bl_profile=[("x", Lreal)]
}


(*Specific class which adds an empty main function and
  changes the name of the previous function called main (if it exists)
*)
class main_name_fixer = object (self)
  inherit Visitor.frama_c_inplace

  val mutable changed_main = false
  val new_main_name = "main2" (*new name for main function*)

  method set_changed_main ?(newval=true) () = changed_main <- newval
  method get_changed_main () = changed_main

  method get_new_main_name () = new_main_name

  method! vfile f =
    List.iter ( function
        | GFun (fd, loc) when fd.svar.vorig_name = "main" ->
          self#set_changed_main ~newval:true ();
          ignore (add_fundec_to_cfg ~loc:loc ~funspec:fd.sspec fd new_main_name)
        | _ -> ()
      )
      f.globals;
    (*Add new empty main function*)
    let new_main = Cil.emptyFunction "main" in
    let main_args = [("argc", Cil_const.intType, []); 
      ("argv", {tnode = TPtr Cil_const.charPtrType; tattr = []}, [])] 
    in
    Cil.setFunctionTypeMakeFormals new_main
      {tnode = TFun (Cil_const.voidType, Some main_args, false); tattr = [];};
    Cil.setFormals new_main new_main.sformals; (*not sure why this is needed*)
    f.globals <- f.globals @ [GFun (new_main, unknown_loc)];
    ignore (add_fundec_to_cfg new_main "main");
    Ast.mark_as_changed ();
    Cil.ChangeTo f
end

(* float_to_mpfr_vi *)
let vi_to_mpfr_with_newtype fl_vi newtype =
      (* let m_vi = (Cil.copyVarinfo fl_vi (fl_vi.vname ^ "_mpfr")) in *)
      let m_vi = Cil_const.copy_with_new_vid fl_vi in
      Cil_const.change_varinfo_name m_vi (fl_vi.vname ^ "_mpfr");
      Cil.update_var_type m_vi newtype;
      (*If vi is initialised (e.g float x = 2.3;), then vdefined is true.
        Since mpfr vars are init with call to mpfr_set, this should be false*)
      m_vi.vdefined <- false;
      m_vi

(*returns true if the operator is a comparison one*)
let is_compare_op = function
  | Lt | Gt | Le | Ge | Eq | Ne ->  true
  | _ -> false


let float_to_mpfr_vi fl_vi = vi_to_mpfr_with_newtype fl_vi mpfr_type

let atoi_fn_vi () =
  let args = [("li", Cil_const.charPtrType, [])] in
  let t =  {tnode = TFun(Cil_const.intType, Some args, false); tattr = [];} in
  make_fn_vi t "atoi"

let fopen_fn_vi () =
  let args = [("fname", Cil_const.charPtrType, []);
              ("mode", Cil_const.charPtrType, [])] in
  let t = {tnode = TFun(file_ptr_type, Some args, false); tattr = [];} in
  make_fn_vi t "fopen"

let fprintf_fn_vi () =
  let args = [("file", file_ptr_type, []);
              ("str", Cil_const.charPtrType, [])] in
  let t = {tnode = TFun(file_ptr_type, Some args, true); tattr = []} in
  make_fn_vi t "fprintf"


let fscanf_fn_vi mem_types =
  let args = [
      ("file", file_ptr_type, []);
      ("str", Cil_const.charConstPtrType, []);
    ] @ List.mapi (fun i t -> (string_of_int i, t, [])) mem_types
  in
  let t = {tnode = TFun(Cil_const.intType, Some args, true); tattr = []} in
  let fn_vi = make_fn_vi t "fscanf" in
  let t = {tnode = TFun(file_ptr_type, Some args, true); tattr = []} in
  make_fn_vi t "fscanf"

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
    {tnode = TFun(Cil_const.intType, Some args, false); tattr = [];}

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
    | Ne -> "mpfr_lessgreater_p " (* TODO: IS this correct semantics?*)
    | _ -> Kernel.fatal "unsupported binop %a" Printer.pp_binop oper
  in
  let f = Ast.get () in
  Cil.findOrCreateFunc f op_fn_name
  {tnode = TFun(Cil_const.intType, Some args, false); tattr = [];}

(*given args = x,y, generates fscanf(fp, "%f,%f,%f", &x, &y)*)
let make_fscanf_instr ?(sep=",") fp args =
  let mem_args = List.map (Cil.mkAddrOrStartOf ~loc:unknown_loc) args in
  let mem_types = List.map Cil.typeOf mem_args in
  let get_token t = match t.tnode with
    | TPtr t' ->
        (match Ast_types.unroll_node t' with
          | TInt IInt -> "%d"
          | TFloat FFloat -> "%f"
          | TFloat FDouble -> "%lf"
          | _ ->
            (Self.debug ~level:3 "type: %a" Printer.pp_typ t;
            Kernel.fatal "not implemented other yet"))
    | _ -> Kernel.fatal "Expected ptr here: %a" Printer.pp_typ t;
  in
  let tokens = List.map get_token mem_types in
  let fn_vi = fscanf_fn_vi mem_types in
  let format_str = string_to_exp ((String.concat sep tokens) ^ "\n") in
  make_fun_call_instr fn_vi @@ [fp;format_str] @ mem_args

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
    let t = {tnode = TFun(Cil_const.intType, Some args, false); tattr = []} in
    make_fn_vi t (mpfr_trans_func_name vi.vorig_name)


let mpfr_set_prec_stmt n =
  let args = [("prec",Cil_const.intType,[])] in
  let t = {tnode = TFun(Cil_const.intType, Some args, true); tattr = []} in
  let fn_vi = make_fn_vi t "mpfr_set_default_prec" in
  Cil.mkStmtOneInstr (make_fun_call_instr fn_vi [Cil.integer ~loc:unknown_loc n])





let var_offs_to_exp vi offs = Cil.new_exp ~loc:unknown_loc (Lval (Var vi, offs))

let mpfr_exps_from_struct_vi vi =
  let rec append_offset prefix suffix =
    match prefix with
    | NoOffset -> suffix
    | Field (f, rest) -> Field (f, append_offset rest suffix)
    | Index (e, rest) -> Index (e, append_offset rest suffix)
  in
  let rec collect_type prefix typ =
    if typ = mpfr_type then
      [var_offs_to_exp vi prefix]
    else
      match Ast_types.unroll_node typ with
      | TComp ci ->
        (match ci.cfields with
        | Some fields ->
          List.concat_map (fun f ->
            collect_type (append_offset prefix (Field (f, NoOffset))) f.ftype
          ) fields
        | None -> [])
      | TArray (element_type, Some length) ->
        (match length.enode with
        | Const (CInt64 (length, _, _)) when Z.sign length >= 0 ->
          let length =
            try Z.to_int length
            with Z.Overflow -> Kernel.fatal "MPFR array is too large to initialize"
          in
          List.concat_map (fun index ->
            collect_type
              (append_offset prefix
                (Index (Cil.integer ~loc:unknown_loc index, NoOffset)))
              element_type
          ) (List.init length Fun.id)
        | _ -> Kernel.fatal "MPFR arrays require a constant length")
      | TArray (_, None) -> []
      | _ -> []
  in
  match Ast_types.unroll_node vi.vtype with
  | TComp _ -> collect_type NoOffset vi.vtype
  | _ -> Kernel.fatal "Dont call this function with non-cinfo vi"





(*returns true if exp_node is a binop expression returning a float value,
  or if it is a comparison between two floats. Might have to add more cases
  in the future.
 *)
let exp_is_float_binop = function
  | BinOp (_, _, _, t) when Ast_types.is_float t -> true
  | BinOp (bop, a, b, _)
    when is_compare_op bop &&
         Ast_types.is_float (Cil.typeOf a) &&
         Ast_types.is_float (Cil.typeOf a)
    -> true
  | _ -> false


(*Make*)
let get_mpfr_initOrClear_instr vars fname =
    let lval_exps = List.concat (List.map (fun vi -> match vi.vtype with
      | {tnode = TComp _; _} -> mpfr_exps_from_struct_vi vi
      | t when t = mpfr_type  -> [var_to_exp vi]
      | {tnode = TPtr _; _} -> []
      | _ -> Kernel.fatal "only mpfr type or mpfrs in structs supported, got: %a of type %a"
                Printer.pp_varinfo vi
                Printer.pp_typ vi.vtype
    )
    vars )
    in
    (*Dummy arg names, they dont matter*)
    let args =
      (List.mapi (fun i _ -> ("v" ^ (string_of_int i), mpfr_type, [])) lval_exps)
       @ [("end", mpfr_rnd_type, [])]
    in
    let t = {tnode = TFun(Cil_const.intType, Some args, true); tattr = [];} in
    let fn_vi = make_fn_vi t fname in
    make_fun_call_instr fn_vi (lval_exps @ [mpfr_void_ptr_exp])

let get_mpfr_clears_instr vars = get_mpfr_initOrClear_instr vars "mpfr_clears"
let get_mpfr_inits_instr vars = get_mpfr_initOrClear_instr vars "mpfr_inits"



(* let get_mpfr_clears_instr vars =
    let args =
      (List.mapi (fun i _ -> ("v" ^ (string_of_int i), mpfr_type, [])) vars)
       @ [("end", mpfr_rnd_type, [])]
    in
    let t = (TFun(Cil_const.intType, Some args, true, [])) in
    let fn_vi = make_fn_vi t "mpfr_clears" in
    make_fun_call_instr fn_vi ((varinfos_to_exps vars) @ [mpfr_void_ptr_exp]) *)

let mpfr_set_str_instr ?(base = 10) ?(rnd=rnd_exp) rop str  =
  let args = [
    ("rop", mpfr_type, []);
    ("rop", Cil_const.charPtrType, []);
    ("base", Cil_const.intType, []);
    ("rnd", mpfr_rnd_type, [])
  ]
  in
  let t = {tnode = TFun(Cil_const.intType, Some args, false); tattr = []} in
  let fn_vi = make_fn_vi t "mpfr_set_str" in
  make_fun_call_instr fn_vi [var_to_exp rop; str; rnd]



let mpfr_set_instr_fn_vi =
  let args = [
    ("rop", mpfr_type, []);
    ("op", mpfr_type, []);
    ("rnd", mpfr_rnd_type, [])
  ]
  in
  let t = {tnode = TFun(Cil_const.intType, Some args, false); tattr = []} in
  make_fn_vi t "mpfr_set"

let mpfr_set_instr to' from rnd =
  (* let (m_to, m_from) = (mpfr_var_to_vi to', mpfr_var_to_vi from) in *)
  let fn_vi = mpfr_set_instr_fn_vi in
  (* let (to_exp,from_exp) = (var_to_exp to', var_to_exp from) in *)
  make_fun_call_instr fn_vi [to'; from; rnd]



  (* mpfr_add(res1, tmp1, res1, MPFR_RNDN); *)
    (* Call of lval option * exp * exp list * location *)
(* Create a call instr to mpfr_set_flt, from a float constant fl to variable vi *)
let mpfr_set_flt_instr fl_exp m_exp rnd =
  let args = [
    ("rop", mpfr_type, []);
    ("op", mpfr_type, []);
    ("rnd", mpfr_rnd_type, [])
  ]
  in
  let t = {tnode = TFun(Cil_const.intType, Some args, false); tattr = []} in
  let fn_vi = make_fn_vi t "mpfr_set_flt" in
  make_fun_call_instr fn_vi [m_exp; fl_exp; rnd]

let mpfr_set_const_str_instr flstr vi rnd =
    let args = [
      ("rop", mpfr_type, []);
      ("s", Cil_const.charPtrType, []);
      ("base", Cil_const.intType, []);
      ("rnd", mpfr_rnd_type, [])
    ]
    in
    let t = {tnode = TFun(Cil_const.intType, Some args, false); tattr = []} in
    let fn_vi = make_fn_vi t "mpfr_set_str" in
    let fl_exp = string_to_exp flstr in
    let vi_exp = var_to_exp vi in
    let base_exp = Cil.integer ~loc:unknown_loc 0 in
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
  let t = {tnode = TFun(Cil_const.doubleType, Some args, false); tattr = []} in
  let fn_vi = make_fn_vi t "mpfr_get_d" in
  let to_vi_exp = var_to_exp to_vi in
  let res_lval = Some (vi_to_varlval from_vi) in
  make_fun_call_instr ~res:res_lval fn_vi [to_vi_exp; rnd]

let mpfr_fprintf_diff_instr file_vi str_exp a_vi b_vi diff_vi rnd =
    let args = [
      ("file", file_ptr_type, []);
      ("str", Cil_const.charConstPtrType, []);
      ("a", mpfr_type, []);
      ("b", mpfr_type, []);
      ("diff", mpfr_type, []);
    ]
    in
    let t = {tnode = TFun(Cil_const.intType, Some args, true); tattr = []} in
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

let is_int vi = Ast_types.is_integral vi.vtype
let is_char_ptr_ptr vi = match vi.vtype.tnode with
  | TPtr t -> Ast_types.is_any_char_ptr t
  | _ -> false
