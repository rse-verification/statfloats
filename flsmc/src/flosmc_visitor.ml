open Cil_types
open Selfplugin
open CloneMPFR

module Build = Cil_builder.Pure

module StringMap = Map.Make(String)

module StringSet = Set.Make(String)

module IntMap = Map.Make(Int)

let unknown_loc = Cil_datatype.Location.unknown
let zero_exp = Cil.integer ~loc:unknown_loc 0



(*Returns def if key is not in ht, otherwise ht[key]*)
let hashtbl_get_default ht key def =
  match Hashtbl.find_opt ht key with
    | Some elt -> elt
    | None -> def

(*Indicates origin of mpfr_var.
 Tmp = new var, for middle of calc. Loc=orig local var, glob=global var*)
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

let add_kernel_function f new_kf old_kf =
    let new_fundec = Kernel_function.get_definition new_kf in
    let new_loc = Kernel_function.get_location new_kf in
    let gfun = GFun (new_fundec, new_loc) in

    let old_vi = Kernel_function.get_vi old_kf in
    let is_old_fundec fundec = Cil_datatype.Varinfo.equal fundec.svar old_vi in
    let is_old_gfun = function
      | GFun (fundec,_) -> is_old_fundec fundec
      | _ -> false
    in
    (* Scan the globals. Make sure this is tail recursive. *)
    let rec loop (acc: global list) = function
      | [] -> begin
          match f.globinit with
          | Some fundec when is_old_fundec fundec ->
            (* The clone function is the global initializer function.
               Adds it at the end of the list of globals. *)
            List.rev_append acc [gfun]
          | _ -> Kernel.fatal "kernel function not found for %s(%d)" old_vi.vname old_vi.vid
        end
      | g :: restg when is_old_gfun g -> List.rev_append acc (g:: gfun ::restg)
      | g :: restg -> loop (g::acc) restg
    in
    (* Updates the list of globals *)
    f.globals <- loop [] f.globals;
    Ast.mark_as_grown();
    new_kf

(* val mpfr_type =
  let mpfr_prec_ti = {
    torig_name: "mpfr_prec_t";
    tname: "mpfr_prec_t";
    ttyp: TInt(IShort, []);
    treferenced: false
  } in
  let mpfr_prec = TNamed(mpfr_prec_ti, []) in
  let mpfr_sign_ti = {
    torig_name: "mpfr_sign_t";
    tname: "mpfr_sign_t";
    ttyp: TInt(IInt, []);
    treferenced: false
  } in
  let mpfr_sign = TNamed(mpfr_sign_ti, []) in
  let mpfr_exp_ti = {
    torig_name: "mpfr_exp_t";
    tname: "mpfr_exp_t";
    ttyp: TInt(IShort, []);
    treferenced: false
  } in
  let mpfr_exp = TNamed(mpfr_exp_ti, []) in
  let mp_limb_ti = {
    torig_name: "mp_limb_t";
    tname: "mp_limb_t";
    ttyp: TInt(IULong, []);
    treferenced: false
  } in
  let mpfr_limb = TNamed(mpfr_limb_ti, []) in
  let mpfr_struct_anon =
    mkCompInfo(true, "mpfr_struct_anon",
      fun _ -> [
      ("_mpfr_prec", mpfr_prec_t, None, [],
      "_mpfr_sign" mpfr_sign_t,
      "_mpfr_exp"
      "mp_limb_t"
      ]
    )

val mkCompInfo: bool ->      (* whether it is a struct or a union *)
    string -> (* name of the composite type; cannot be empty *)
    ?norig:string -> (* original name of the composite type, empty when anonymous *)
    (compinfo ->
     (string * typ * int option * attributes * location) list option) ->
    (* a function that when given a forward
       representation of the structure type constructs the type of
       the fields. The function can ignore this argument if not
       constructing a recursive type.  *)
    attributes -> compinfo

    TComp(
      cstruct : true;
      corig_name : string
        attributes
    )
let mpfr_struct_ =
    {
      torig_name:"__mpfr_struct";
      tname:"__mpfr_struct";
      ttyp: In;
    } in
let mpfr_ti =
    {
      torig_name:"mpfr_t";
      tname:"mpfr_t";
      ttyp:
      treferenced:false;
    }
    TNamed of typeinfo * attributes *)
(* in *)

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

let float_to_mpfr_vi fl_vi =
  let m_vi = (Cil.copyVarinfo fl_vi (fl_vi.vname ^ "_mpfr")) in
  Cil.update_var_type m_vi mpfr_type;
  m_vi


(*Gatheres info on how many mpfr vars to create*)
class mpfr_functions_adder = object (self)
  inherit Visitor.frama_c_inplace

  val mutable mpfr_funcs_map = Hashtbl.create 10

  method get_funcs_map = mpfr_funcs_map

  method add_fns f =
    Visitor.visitFramacFile
              ((self) :> Visitor.frama_c_inplace)
              f

  method! vfile f =
    let fun' = (fun f' ->
        Hashtbl.iter
          (fun kf new_name ->
            let new_kf = clone_defined_kernel_function kf new_name f' in ()
          )
          mpfr_funcs_map;
        f'
      )
    in Cil.DoChildrenPost fun'

  method! vfunc fnc =
    let kf = Option.get self#current_kf in
    let old_name = Kernel_function.get_name kf in
    let new_name = mk_new_name old_name in
    Hashtbl.add mpfr_funcs_map kf new_name;
    Cil.SkipChildren
end


let make_fn_vi typ name =
  let new_decl = Cil.makeGlobalVar ~temp:false name typ in
  Cil.setFormalsDecl new_decl typ;
  new_decl
  (* Cil.findOrCreateFunc f "mpfr_set_flt"
    (TFun(Cil.intType, Some args, false, [])) *)

(* mpfr_set_flt (mpfr_t rop, float op, mpfr_rnd_t rnd) *)

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
  (* | TFun of typ * (string * typ * attributes) list option * bool * attributes *)

(* makes a call stmt from callee as varinfo and args as exps *)
let make_fun_call fn_vi args =
  let call_exp = Cil.new_exp ~loc:unknown_loc
                (Lval (Var(fn_vi), NoOffset))
  in
  let instr = Call (None, call_exp, args, unknown_loc) in
  Cil.mkStmt (Instr instr)

(*takes a varinfo and wraps it into an expression
  Note, this expects direct reference to the variable, and not e.g. pointer
  with offset.
*)
let var_to_exp vi =
  Cil.new_exp ~loc:unknown_loc
    (Lval (Var(vi), NoOffset))

let varinfos_to_exps vis = List.map var_to_exp vis

let mkBlockWithLocs (slst: stmt list) locs : block =
  { battrs = []; bstmts = slst; blocals =locs; bstatics = []; bscoping = true }


let make_binop_mpfr a b r oper rnd =
  let (a_vi, b_vi, r_vi) =
    ((mpfr_var_to_vi a), (mpfr_var_to_vi b), (mpfr_var_to_vi r)) in
  let vi = oper_to_mpfr_fn_vi oper in
  let args = varinfos_to_exps [r_vi;a_vi;b_vi] @ [rnd] in
  make_fun_call vi args
  (* call_exp *)

let get_mpfr_clears_stmt vars =
      let args =
        (List.mapi (fun i _ -> ("v" ^ (string_of_int i), mpfr_type, [])) vars)
         @ [("end", mpfr_rnd_type, [])]
      in
      let t = (TFun(Cil.intType, Some args, true, [])) in
      let fn_vi = make_fn_vi t "mpfr_clears" in
      make_fun_call fn_vi ((varinfos_to_exps vars) @ [zero_exp])

let get_mpfr_inits_stmt vars =
    let args =
      (List.mapi (fun i _ -> ("v" ^ (string_of_int i), mpfr_type, [])) vars)
       @ [("end", mpfr_rnd_type, [])]
    in
    let t = (TFun(Cil.intType, Some args, true, [])) in
    let fn_vi = make_fn_vi t "mpfr_inits" in
    make_fun_call fn_vi ((varinfos_to_exps vars) @ [zero_exp])

let mpfr_set_stmt to' from rnd =
  let (m_to, m_from) = (mpfr_var_to_vi to', mpfr_var_to_vi from) in
  let args = [
    ("rop", mpfr_type, []);
    ("op", mpfr_type, []);
    ("rnd", mpfr_rnd_type, [])
  ]
  in
  let t = (TFun(Cil.intType, Some args, false, [])) in
  let fn_vi = make_fn_vi t "mpfr_set" in
  let (to_exp,from_exp) = (var_to_exp m_to, var_to_exp m_from) in
  make_fun_call fn_vi [to_exp; from_exp; rnd]

  (* mpfr_add(res1, tmp1, res1, MPFR_RNDN); *)
    (* Call of lval option * exp * exp list * location *)
(* Create a call instr to mpfr_set_flt, from a float constant fl to variable vi *)
let mpfr_set_const_stmt fl vi rnd =
  let m_vi = mpfr_var_to_vi vi in
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
  let vi_exp = var_to_exp m_vi in
  make_fun_call fn_vi [vi_exp; fl_exp; rnd]

let addefunwithstmts name stmts locs formals =
  (* Create global function [name] *)
  (* List.iter
    (fun x -> Self.feedback "Here: %a" Printer.pp_varinfo x)
    locs; *)

  let vi =
    Cil.makeGlobalVar ~source:true
      name
      (TFun(Cil.voidType, Some [], false, []))
  in
  vi.vdefined <- true;
  (* There is no contract associated with the function *)
  let spec = Cil.empty_funspec () in
  (* Create function definition with no stmt yet: they will be added
     afterwards *)
  let blk = match stmts with
    | [{skind = Block b; _} as s] -> b.blocals <- locs; b
    | _ -> assert false; Cil.mkBlock []
    (* mkBlockWithLocs (List.map Cil.mkStmtOneInstr stmts) locs *)
  in
  let fundec =
    { svar = vi;
      sformals = formals;
      slocals = locs;
      smaxid = 0;
      sbody = blk;
      smaxstmtid = None;
      sallstmts = [];
      sspec = spec }
  in
  let fct = Definition(fundec, unknown_loc) in
  (* Create and register the function as kernel function *)
  let kf = { fundec = fct; spec = spec } in
  Globals.Functions.register kf;
  Globals.Functions.replace_by_definition spec fundec unknown_loc;
  Ast.mark_as_grown ();
  vi, fundec, kf



class flosmc_transformer mpfr_funcs_names = object (self)
  inherit Visitor.frama_c_inplace (*(Project.current ())*)

  val mutable var_stack = Hashtbl.create 10
  val mutable tmp_var_id = Hashtbl.create 10
  val mutable tmp_var_queue = Hashtbl.create 10 (*Should contain all created tmp_vars*)
  val mutable res_vars = Hashtbl.create 10

  val mutable tmp_var_map = Hashtbl.create 10 (*Map from id to tmp_var*)
  val mutable new_stmts = Hashtbl.create 5  (*Instructions to add per func*)
  val mutable loc_mpfr_vars = Hashtbl.create 10 (*Mpfr vars for local vars per func*)
  val mutable glob_mpfr_vars = Hashtbl.create 10 (*Mpfr vars for global vars per func*)


  val mutable fn_mpfr_names_to_vis = Hashtbl.create 10

  (* val get_mpfr_kf vi =
    match Hashtbl.find_opt fn_mpfr_vis with
      | Some m_vi -> m_vi
      | None ->
        let m_vi = fn_vi_to_mpfr_vi vi in
        Hashtbl.add fn_mpfr_vis vi m_vi;
        m_vi *)

  (*Hack until it breaks, should be an enum of type mpfr_rnd_t*)
  val rnd_exp = Cil.integer ~loc:unknown_loc 0



  method make_block_stmt () =
    match self#make_block_from_queue (Option.get self#current_kf) with
     | Either.Left (blk, q) -> blk
     | Either.Right () -> Cil.mkBlock []

  (*Convert the expr into an mpfr one, and returns a block of all the
  statements that need to be added before the expression*)
  method convert_expr_and_mkblock e =
    let e' = Visitor.visitFramacExpr (self :> Visitor.frama_c_copy) e in
    (self#make_block_stmt (), e')

  method visit_block_and_mkblock b =
    let _ = Visitor.visitFramacBlock (self :> Visitor.frama_c_refresh) b in
    self#make_block_stmt ()

  method get_res_vi kf =
    match Hashtbl.find_opt res_vars kf with
      | Some vi -> vi
      | None -> let vi = Cil.makeVarinfo false true "res_mpfr" mpfr_type in
                Hashtbl.add res_vars kf vi;
                vi

  method get_local_or_glob_mpfr vi kf =
    let fnc = if vi.vglob then self#get_global_mpfr else self#get_local_mpfr in
    fnc vi kf

  method get_local_mpfr vi kf =
    let locs = match Hashtbl.find_opt loc_mpfr_vars kf with
      | Some locs' -> locs'
      | None -> let locs' = Hashtbl.create 5 in
                Hashtbl.add loc_mpfr_vars kf locs';
                locs'
    in
    let l_m_vi = match Hashtbl.find_opt locs vi with
      | Some l_m_vi' -> l_m_vi'
      | None ->
          let l_m_vi' = Loc (float_to_mpfr_vi vi) in
          Hashtbl.add locs vi l_m_vi';
          l_m_vi'
    in
    l_m_vi

  method get_global_mpfr vi =
    Kernel.fatal "global vars not implemented"
    (* assert false; (*Not yet implemented*)
    Glob vi *)


  method get_mpfr_from_id id =
    match Hashtbl.find_opt tmp_var_map id with
      | Some v -> v
      | None -> let v = Cil.makeVarinfo false false
                          ("tmp" ^ (string_of_int id) ^ "_mpfr") mpfr_type
                in
                Hashtbl.add tmp_var_map id (Tmp v);
                Tmp v



  method push_var v kf =
    let stack = match Hashtbl.find_opt var_stack kf with
      | Some st -> st
      | None -> let st = Stack.create () in Hashtbl.add var_stack kf st; st
    in
    Stack.push v stack

  method get_or_make_stmt_queue kf =
    match Hashtbl.find_opt new_stmts kf with
      | Some q -> q
      | None ->
          let q = Queue.create () in
          Hashtbl.add new_stmts kf q; q


  method fetch_tmp_var kf =
    let var_q = match Hashtbl.find_opt tmp_var_queue kf with
      | Some q -> q
      | None -> let q = Queue.create () in
                Hashtbl.add tmp_var_queue kf q;
                q
    in
    match Queue.take_opt var_q with
        | Some v -> v
        | None -> let id = self#incr_tmp_id kf in
                  let var = self#get_mpfr_from_id id in
                  var

  (*puts the tmp_var back into the queue, does nothing otherwise*)
  method return_var kf var =
    if is_tmp_mpfr_vi var then
      let var_q = Hashtbl.find tmp_var_queue kf in
      Queue.push var var_q;
    else
      ()

  method incr_tmp_id kf =
    let id = match Hashtbl.find_opt tmp_var_id kf with
      | Some id' ->  id'
      | None -> 0
    in
      Hashtbl.replace tmp_var_id kf (id+1);
      id


  (* method decr_tmp_id kf =
    let id = Hashtbl.find tmp_var_id kf in
    Hashtbl.replace tmp_var_id kf (id-1); *)

  (*Returns Left (block,q) if queue exists has some stmts, otherwise Right ()*)
  method make_block_from_queue kf =
    match Hashtbl.find_opt new_stmts kf with
      | None -> Either.Right ()
      | Some q ->
        if Queue.is_empty (Hashtbl.find new_stmts kf) then Either.Right ()
        else
          let blk = Cil.mkBlock (List.of_seq (Queue.to_seq q)) in
          Queue.clear q;
          Either.Left (blk, q)

  method current_kf_name () =
    match self#current_kf with
        | Some kf -> Kernel_function.get_name kf
        | None ->  assert false; "dummy"

  method push_float_constant fl kf =
    let mpfr_var = self#fetch_tmp_var kf in
    self#add_stmt (mpfr_set_const_stmt fl mpfr_var rnd_exp) kf;
    self#push_var mpfr_var kf;
    mpfr_var

  method pop_var kf =
    let st = Hashtbl.find var_stack kf in
    Stack.pop st

  method add_stmt stmt kf  =
    match Hashtbl.find_opt new_stmts kf with
        | Some(fn_q) ->  Queue.add stmt fn_q
        | None -> let fn_q = Queue.create () in
                  Queue.push stmt fn_q;
                  Hashtbl.add new_stmts kf fn_q

(*mpfr_set_flt (mpfr_t rop, float op, mpfr_rnd_t rnd)*)

(*  method add_init_instr var =
    let instr = Cil_builder.Pure.call 'none*)



  method translate f=
    let _ = Visitor.visitFramacFileCopy
              ((self) :> Visitor.frama_c_copy)
              f
    in
    ()

  (* method! vfile fle =
    let f = (fun g ->
      let _ = mpfr_set_flt_fn_vi g in
      g
    )
    in
    Cil.DoChildrenPost f *)
    (* method! vfile f =
      let fun' = (fun g ->
                    Hashtbl.iter
                      (fun kf stmts ->
                        let tmp_locs = List.map mpfr_var_to_vi
                          (List.of_seq (Queue.to_seq (Hashtbl.find tmp_var_queue kf)))
                        in
                        let loc_locs = List.map mpfr_var_to_vi
                          (List.of_seq (Hashtbl.to_seq_values (Hashtbl.find loc_mpfr_vars kf)))
                        in
                        let stmts_to_add = List.of_seq (Queue.to_seq stmts) in
                        let formals = List.map
                                        (fun vi'->
                                          mpfr_var_to_vi
                                          (self#get_local_mpfr vi' kf))
                                        (Kernel_function.get_formals kf)
                        in
                        let res_vi = Cil.makeVarinfo false true
                                            "res_mpfr" mpfr_type
                        in
                        match stmts_to_add with
                          | [] -> ()
                          | _  ->
                            let (_,_,new_kf) = addefunwithstmts
                                  ((Kernel_function.get_name kf) ^ "_mpfr")
                                  stmts_to_add
                                  (tmp_locs @ loc_locs)
                                  (formals @ [res_vi])
                                  (* (List.of_seq (Queue.to_seq (Hashtbl.find tmp_var_queue kf))) *)
                            in
                            let _ = add_kernel_function g new_kf kf in
                            Self.feedback "HELLO2";
                      )
                      new_stmts;
                    g
                 )
      in
      Cil.DoChildrenPost fun' *)

  method! vblock b =
    let fun' = (fun b' ->
      let kf = Option.get self#current_kf in
      match self#make_block_from_queue kf with
        | Either.Left (blk, q) ->
            Queue.push (Cil.mkStmt (Block blk)) q;
            blk
        | Either.Right _  ->
          b'
    )
    in Cil.DoChildrenPost fun'

  method! vstmt_aux s =
    let kf = Option.get self#current_kf in
    match s.skind with
      | Instr(Set((lh, _), _, _)) ->
          (match lh with
            | Var ({vtype=t; _} as vi) when Cil.isFloatingType t ->
              let fun' = (fun g ->
                let m_vi = self#get_local_or_glob_mpfr vi kf
                in
                let m_tmp = self#pop_var kf in
                self#return_var kf m_tmp;
                let stmt = mpfr_set_stmt m_vi m_tmp rnd_exp in
                self#add_stmt stmt kf;
                g
              )
              in
              Cil.DoChildrenPost fun'
            | _ -> Cil.SkipChildren
          )
      | Instr (Call (maybe_lv, fn_exp, args_exps, _)) ->
          let res_mvi =
            match maybe_lv with
              | Some (Var res_vi, _) ->
                self#get_local_or_glob_mpfr res_vi kf;
              | None -> self#fetch_tmp_var kf
              | _ -> Kernel.fatal "value not set to var"
          in
          (* let new_arg_exps = List.map self#convert_expr_and_mkblock args_exps in *)
          let fn_mvi = match fn_exp.enode with
            | Lval (Var vi, _) ->
              let m_name = Hashtbl.find mpfr_funcs_names vi.vorig_name in
              let m_vi = Hashtbl.find fn_mpfr_names_to_vis m_name in
              m_vi
            | _ -> Kernel.fatal "function var is not a var"
          in
          let new_args_e_and_blk =
            List.map self#convert_expr_and_mkblock args_exps
          in
          List.iter (fun (b, _) ->
              self#add_stmt (Cil.mkStmt (Block b)) kf) new_args_e_and_blk;
          self#add_stmt
            (Cil.mkStmt
              (Instr (Call (None, var_to_exp fn_mvi,
                List.map snd new_args_e_and_blk, unknown_loc))))
            kf;

        Cil.SkipChildren
      | If (e, b1, b2, _) ->
        let (e_blk, e') = self#convert_expr_and_mkblock e in
        let b1_blk = self#visit_block_and_mkblock b1 in
        let b2_blk = self#visit_block_and_mkblock b2 in
        let exp_stmt = Cil.mkStmt (Block e_blk) in
        let if_stmt = Cil.mkStmt (If (e', b1_blk, b2_blk,
                            unknown_loc)) in
        let q = self#get_or_make_stmt_queue kf in
        Queue.push exp_stmt q;
        Queue.push if_stmt q;
        Cil.SkipChildren

      | Return (Some e, _) ->
      let fun' = (fun s' ->
        let res_vi = self#get_res_vi kf in
        let m_tmp = self#pop_var kf in
        self#return_var kf m_tmp;
        let stmt = mpfr_set_stmt (Loc res_vi) m_tmp rnd_exp in
        self#add_stmt stmt kf;
        s'
      )
      in
      Cil.DoChildrenPost fun'
      | _ -> Cil.DoChildren


  method! vfunc _ =
    (* let new_f = Cil.emptyFunction ("m_" ^ f.svar.vname) in *)
    match self#current_kf with
      | Some(kf) ->
        (* let _ = Clone.clone_defined_kernel_function kf in *)
        (* Globals.Functions.add (Definition (new_f, Kernel_function.get_location kf)); *)
          (* val makeTempVar : Cil_types.fundec -> ?insert:bool -> ?ghost:bool -> ?name:string ->
          ?descr:string -> ?descrpure:bool -> ?loc:Cil_datatype.Location.t -> Cil_types.typ -> Cil_types.varinfo *)
        let name = (Kernel_function.get_name kf) in
        if Seq.exists (fun n -> n == name) (Hashtbl.to_seq_values mpfr_funcs_names) then
          let fun' = ( fun fnc  ->
            Self.feedback "%s" (Kernel_function.get_name kf);
            (*Fix locals*)
            let tmp_m_locs = List.of_seq (Queue.to_seq
                  (hashtbl_get_default tmp_var_queue kf (Queue.create () )))
            in
            let loc_ht = hashtbl_get_default loc_mpfr_vars kf (Hashtbl.create 1) in
            let og_locs_top_keep =
              List.filter (fun x -> (Hashtbl.mem loc_ht x) |> not) fnc.slocals in
            let loc_m_locs =
              List.filter (fun x -> not (mpfr_var_to_vi x).vformal)
                (List.of_seq (Hashtbl.to_seq_values loc_ht)) in
            (* let stmts_to_add = List.of_seq (Queue.to_seq stmts) in *)
            let all_m_locs = List.map mpfr_var_to_vi (tmp_m_locs @ loc_m_locs) in
            (*Add init stmts for all locals*)
            let all_locs = og_locs_top_keep @ all_m_locs in
            let init_stmt = get_mpfr_inits_stmt all_m_locs in
            let clear_stmt = get_mpfr_clears_stmt all_m_locs in
            fnc.sbody.bstmts <- [init_stmt] @ fnc.sbody.bstmts @ [clear_stmt];
            fnc.slocals <- all_locs;
            fnc.sbody.blocals <- all_locs;
            let formals = List.map
                            (fun vi'->
                              mpfr_var_to_vi
                              (self#get_local_mpfr vi' kf))
                            (Kernel_function.get_formals kf)
            in
            let res_vi = self#get_res_vi kf in
            let all_formals = formals @ [res_vi] in
            Cil.setFormals fnc all_formals;
            fnc.sformals <- all_formals;
            let forms_unrolled =
              (List.map (fun a -> (a.vname, a.vtype, a.vattr)) all_formals)
            in
            let _ = match fnc.svar.vtype with
              | TFun(_, _, fa, aa) ->
                Cil.setFunctionType fnc
                  (TFun(Cil.voidType, Some forms_unrolled, fa, aa));
              | _ -> Kernel.fatal ~current:true "not a function type"
            Ast.mark_as_grown ();
            in
            Hashtbl.add fn_mpfr_names_to_vis name fnc.svar;
            fnc
            )
          in
          Cil.DoChildrenPost fun'
        else
          Cil.SkipChildren
      | _ ->  Cil.SkipChildren

  method! vexpr e =
    match e.enode with
        | Const(CReal(fl, _, _)) ->
          let fun' = (fun e ->
              let m_v = self#push_float_constant fl (Option.get self#current_kf) in
              var_to_exp (mpfr_var_to_vi m_v)
          )
          in
          Cil.DoChildrenPost fun'
        | BinOp(oper, _, _, TFloat(_, _)) ->
          let f = (fun e ->
            let kf = Option.get self#current_kf in
            let b = self#pop_var kf in
            let a = self#pop_var kf in
            self#return_var kf a;
            self#return_var kf b;
            (* Self.feedback "%f" a;
            Self.feedback "%f" b; *)
            (* self#push_var (a +. b); *)
            let r = self#fetch_tmp_var kf in
            self#push_var r kf;
            self#add_stmt (make_binop_mpfr a b r oper rnd_exp) kf;
            var_to_exp (mpfr_var_to_vi r)
          )
          in
          Cil.DoChildrenPost f
        | Lval(lv) ->
          (match lv with
            | (Var(vi), _) ->
              let fun' = (fun e ->
                let kf = Option.get self#current_kf in
                let m_v = self#get_local_or_glob_mpfr vi kf in
                self#push_var m_v kf;
                var_to_exp (mpfr_var_to_vi m_v)
              )
              in
              Cil.DoChildrenPost fun'
            | _ -> Cil.DoChildren)
        | _ -> Cil.DoChildren
end
