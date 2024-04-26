open Cil_types
open Selfplugin
open CloneMPFR
open Mpfr_utils

module Build = Cil_builder.Pure




(*id is the highest id of the variable currently in use*)
class tmpVarQueue = object (self)
  val mutable id = -1
  val mutable vars = Hashtbl.create 10

  method incr_id () = id <- id+1
  method decr_id () = id <- id-1

  method contains_vi vi =
    Seq.exists (fun vi' -> vi'==vi) (Hashtbl.to_seq_values vars)

  method to_list = List.sort compare (List.of_seq (Hashtbl.to_seq_values vars))

  method return_var vi =
    if self#contains_vi vi then
      (if vi == (Hashtbl.find vars id) then self#decr_id ()
      else Kernel.fatal "should always return last var")
    else
      Self.feedback "not var found";
      ()

  method fetch_var () =
    self#incr_id ();
    Self.feedback "id: %d" id;
    if Hashtbl.mem vars id then
      Hashtbl.find vars id
    else
      let v = Cil.makeVarinfo false false
                        ("tmp" ^ (string_of_int id) ^ "_mpfr") mpfr_type
              in
              Hashtbl.add vars id v;
              v
end




let add_snd_last elm li =
  match List.rev li with
    | [] -> [elm]
    | (h::t) -> List.rev (h::elm::t)

(*Returns def if key is not in ht, otherwise ht[key]*)
let hashtbl_get_default ht key def =
  match Hashtbl.find_opt ht key with
    | Some elt -> elt
    | None -> def


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



let exp_to_vi e = match e.enode with
  | Lval (Var (vi), NoOffset) -> vi
  | _ -> Kernel.fatal "Not a var here"



class flosmc_transformer mpfr_funcs_names = object (self)
  inherit Visitor.frama_c_inplace (*(Project.current ())*)

  val mutable var_stack = Hashtbl.create 10
  val mutable tmp_var_id = Hashtbl.create 10
  val mutable tmp_var_queue = Hashtbl.create 10 (*Should contain all created tmp_vars*)
  val mutable res_vars = Hashtbl.create 10

  val mutable tmp_var_map = Hashtbl.create 10 (*Map from id to tmp_var*)
  val mutable new_stmts = Hashtbl.create 5  (*Instructions to add per func*)
  val mutable new_instrs = Hashtbl.create 5  (*Instructions to add per func*)
  val mutable loc_mpfr_vars = Hashtbl.create 10 (*Mpfr vars for local vars per func*)
  val mutable glob_mpfr_vars = Hashtbl.create 10 (*Mpfr vars for global vars per func*)

  (* val mutable tmp_var_queue = Hashtbl.create 10 *)

  val mutable fn_mpfr_names_to_vis = Hashtbl.create 10

  (*Hack until it breaks, should be an enum of type mpfr_rnd_t*)
  val rnd_exp = Cil.integer ~loc:unknown_loc 0

  method queueOneInstr i = self#queueInstr [i]

  (* method make_block_stmt () =
    match self#make_instr_list_from_queue (Option.get self#current_kf) with
     | Either.Left (ilist, q) -> Cil.mkBlock ilist
     | Either.Right () -> Cil.mkBlock [] *)

  (*Convert the expr into an mpfr one, and returns a block of all the
  statements that need to be added before the expression*)
  (* method convert_expr_and_mkblock e =
    let e' = Visitor.visitFramacExpr (self :> Visitor.frama_c_copy) e in
    (self#make_block_stmt (), e') *)

  (* method visit_block_and_mkblock b =
    let _ = Visitor.visitFramacBlock (self :> Visitor.frama_c_refresh) b in
    self#make_block_stmt () *)

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
          let l_m_vi' = float_to_mpfr_vi vi in
          Hashtbl.add locs vi l_m_vi';
          l_m_vi'
    in
    l_m_vi

  method get_global_mpfr vi =
    Kernel.fatal "global vars not implemented"
    (* assert false; (*Not yet implemented*)
    Glob vi *)


  (* method get_mpfr_from_id id =
    match Hashtbl.find_opt tmp_var_map id with
      | Some v -> v
      | None -> let v = Cil.makeVarinfo false false
                          ("tmp" ^ (string_of_int id) ^ "_mpfr") mpfr_type
                in
                Hashtbl.add tmp_var_map id (Tmp v);
                Tmp v *)



  (* method push_var v kf =
    let stack = match Hashtbl.find_opt var_stack kf with
      | Some st -> st
      | None -> let st = Stack.create () in Hashtbl.add var_stack kf st; st
    in
    Stack.push v stack *)

  (* method get_or_make_instr_queue kf =
    match Hashtbl.find_opt new_instrs kf with
      | Some q -> q
      | None ->
          let q = Queue.create () in
          Hashtbl.add new_instrs kf q; q *)


  method fetch_tmp_var kf =
    let var_q = match Hashtbl.find_opt tmp_var_queue kf with
      | Some q -> q
      | None -> let q = new tmpVarQueue in Hashtbl.add tmp_var_queue kf q; q
    in
    var_q#fetch_var ()
    (* match Queue.take_opt var_q with
        | Some v -> v
        | None -> let id = self#incr_tmp_id kf in
                  let var = self#get_mpfr_from_id id in
                  var *)

  (*puts the tmp_var back into the queue, does nothing otherwise*)
  method return_tmp_var kf var =
    match Hashtbl.find_opt tmp_var_queue kf with
      | Some q -> q#return_var var
      | None -> ()

  (* method incr_tmp_id kf =
    let id = match Hashtbl.find_opt tmp_var_id kf with
      | Some id' ->  id'
      | None -> 0
    in
      Hashtbl.replace tmp_var_id kf (id+1);
      id *)

  (*Returns Left (block,q) if queue exists and has some stmts, otherwise Right ()*)
  (* method make_instr_list_from_queue kf =
    match Hashtbl.find_opt new_instrs kf with
      | None -> Either.Right ()
      | Some q ->
        if Queue.is_empty (Hashtbl.find new_instrs kf) then Either.Right ()
        else
          (* let blk = Cil.mkBlock (List.of_seq (Queue.to_seq q)) in *)
          let ilist = (List.of_seq (Queue.to_seq q)) in
          Queue.clear q;
          Either.Left (ilist, q) *)

  method current_kf_name () =
    match self#current_kf with
        | Some kf -> Kernel_function.get_name kf
        | None ->  assert false; "dummy"

  method push_float_constant fl kf =
    let mpfr_var = self#fetch_tmp_var kf in
    self#queueOneInstr (mpfr_set_const_instr fl mpfr_var rnd_exp);
    (* self#push_var mpfr_var kf; *)
    mpfr_var

  (* method pop_var kf =
    let st = Hashtbl.find var_stack kf in
    Stack.pop st *)

  method get_mpfr_fn_vi og_name =
    match Hashtbl.find_opt mpfr_funcs_names og_name with
      | Some m_name -> Some (Hashtbl.find fn_mpfr_names_to_vis m_name)
      | None -> None


  method translate f=
    let _ = Visitor.visitFramacFileCopy
              ((self) :> Visitor.frama_c_copy)
              f
    in
    ()

  method! vfile f =
     let fun' = (fun f' ->
      f'.globals <- math_include_global::mpfr_include_global::f'.globals;
      Ast.mark_as_grown ();
      f'
    )
    in
    Cil.DoChildrenPost fun'

  method! vvrbl vi =
    let kf = Option.get self#current_kf in
    let fun' = (fun vi' ->
      match vi.vtype with
        |  TFloat(_,_) ->
          let m_v = self#get_local_or_glob_mpfr vi' kf in
          (* self#push_var m_v kf; *)
          m_v
        | TFun(t, maybe_args, variable, attrs) ->
          (match self#get_mpfr_fn_vi vi'.vorig_name with
            | Some m_v -> m_v
            | None -> vi')
        | _ -> vi'
    )
    in
    Cil.DoChildrenPost fun'


  method! vinst i =
    let kf = Option.get self#current_kf in
    match i with
      | Set ((Var {vtype=t; _} as vi, _), _, _) when Cil.isFloatingType t ->
        let fun' = (fun i' ->
            match i' with
              | [Set ((Var vi', _), e', loc')] ->
                  Self.feedback "in Set now";
                  let e_var = exp_to_vi e' in
                  self#return_tmp_var kf e_var;
                  [mpfr_set_instr vi' e_var rnd_exp]
              | _ -> Kernel.fatal "some weird happened"
            (* let m_vi = self#get_local_or_glob_mpfr vi kf in *)
            )
            in
            Cil.DoChildrenPost fun'
      | Call (Some (Var vi, _), _, _, _) ->
        let fun' = (fun i' ->
            match i' with
              | [Call (Some (Var vi', _), e', args_exps', loc')] ->
                  (*Check if transendental, then use mpfr version for this*)
                  if (is_transendental_fun (exp_to_vi e')) then
                    match args_exps' with
                      | [arg] ->
                      [Call (None, var_to_exp (mpfr_trans_fn_vi (exp_to_vi e')),
                        ((var_to_exp vi')::args_exps') @ [zero_exp], loc')]
                      | _ -> Kernel.fatal "should be only one arg in trans"
                    (*assumes only one arg in args_exp, eg sinf(x)*)

                  else
                    [Call (None, e', args_exps' @ [var_to_exp vi'], loc')]
                  (* [mpfr_set_instr vi' e_var rnd_exp] *)
              | _ -> Kernel.fatal "some weird happened"
            (* let m_vi = self#get_local_or_glob_mpfr vi kf in *)
            )
            in
            Cil.DoChildrenPost fun'

      | Local_init (vi, li, _) ->
          let fun' = (fun i' ->
            match i' with
              | [Local_init (vi', li', loc')] ->
                (match li' with
                  | AssignInit (SingleInit e) ->
                    let e' =
                      Visitor.visitFramacExpr (self :> Visitor.frama_c_copy) e
                    in
                    [Set (Cil.var vi', e', loc')]
                  | _ -> Kernel.fatal "not supported1"
                )
              | _ -> Kernel.fatal "some weird happened"
          )
          in Cil.DoChildrenPost fun'
      | _ -> Cil.DoChildren

  method! vstmt_aux s =
    let kf = Option.get self#current_kf in
    match s.skind with
      | Return (Some e, _) ->
        let fun' = (fun s' ->
          match s'.skind with
            | Return (Some e', _) ->
              let res_vi = self#get_res_vi kf in
              (* let m_tmp = self#pop_var kf in *)
              let vi_exp = exp_to_vi e' in
              self#return_tmp_var kf vi_exp;
              let instr = mpfr_set_instr res_vi vi_exp rnd_exp in
              self#queueOneInstr instr;
              Cil.mkStmt (Return (None, unknown_loc))
            | _ -> Kernel.fatal "some weird happened"
        )
      in
      Cil.DoChildrenPost fun'
      | _ -> Cil.DoChildren


  method! vfunc _ =
    (* let new_f = Cil.emptyFunction ("m_" ^ f.svar.vname) in *)
    match self#current_kf with
      | Some(kf) ->
        let name = (Kernel_function.get_name kf) in
        if Seq.exists (fun n -> n == name) (Hashtbl.to_seq_values mpfr_funcs_names) then
          let fun' = ( fun fnc  ->
            Self.feedback "%s" (Kernel_function.get_name kf);
            (*Fix locals*)
            let tmp_m_locs =
              (hashtbl_get_default tmp_var_queue kf (new tmpVarQueue))#to_list
            in
            let loc_ht = hashtbl_get_default loc_mpfr_vars kf (Hashtbl.create 1) in
            let og_locs_top_keep =
              List.filter (fun x -> (Hashtbl.mem loc_ht x) |> not) fnc.slocals in
            let loc_m_locs =
              List.filter (fun x -> not x.vformal)
                (List.of_seq (Hashtbl.to_seq_values loc_ht)) in
            (* let stmts_to_add = List.of_seq (Queue.to_seq stmts) in *)
            let all_m_locs = (tmp_m_locs @ loc_m_locs) in
            (*Add init stmts for all locals*)
            let all_locs = og_locs_top_keep @ all_m_locs in
            let init_stmt = Cil.mkStmtOneInstr (get_mpfr_inits_instr all_m_locs) in
            let clear_stmt = Cil.mkStmtOneInstr (get_mpfr_clears_instr all_m_locs) in
            fnc.sbody.bstmts <-
              add_snd_last clear_stmt ([init_stmt] @ fnc.sbody.bstmts);
            fnc.slocals <- all_locs;
            fnc.sbody.blocals <- all_locs;
            let formals = List.map
                            (fun vi'->
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

  (* method! vinit vi offs it ->
    match offs with
      | Some _ -> Kernel.fatal "not supported yet"
      | None ->
        match it with
          SingleInit e ->

          CompundInit _ -> Kernel.fatal "not supported yet" *)

  (* method! vlocal_init vi li =
    match li with
      | AssignInit it ->
        match it with
      | ConsInit (vi, exp_list, ckind) -> Cil.DoChildren *)



  method! vexpr e =
    match e.enode with
        | Const(CReal(fl, _, _)) ->
          let fun' = (fun e ->
              let m_v = self#push_float_constant fl (Option.get self#current_kf) in
              var_to_exp m_v
          )
          in
          Cil.DoChildrenPost fun'
        | BinOp(oper, _, _, TFloat(_, _)) ->
          let f = (fun e' ->
            match e'.enode with
              | BinOp (oper', e1', e2', t') ->
                let kf = Option.get self#current_kf in
                let (a,b) = (exp_to_vi e1', exp_to_vi e2') in
                (* self#pop_var kf in
                let a = self#pop_var kf in *)
                self#return_tmp_var kf b;
                self#return_tmp_var kf a;
                let r = self#fetch_tmp_var kf in
                (* self#push_var r kf; *)
                self#queueOneInstr (make_binop_mpfr a b r oper rnd_exp);
                var_to_exp r
              | _ -> Kernel.fatal "some weird happened"
          )
          in
          Cil.DoChildrenPost f
        | _ -> Cil.DoChildren
end
