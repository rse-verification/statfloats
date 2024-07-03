open Cil_types
open Selfplugin
open CloneMPFR
open Mpfr_utils

module Build = Cil_builder.Pure

let print_chr_chr_arr e =
  match e.enode with
    | AddrOf _-> Self.debug "addrOf"
    | StartOf _-> Self.debug "StartOf"
    | Lval _-> Self.debug "Lval"
    | CastE _-> Self.debug "cast"
    | UnOp _-> Self.debug "Unop"
    | _ -> Self.debug "otherwise"

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
      Self.debug "not var found";
      ()

  method fetch_var () =
    self#incr_id ();
    Self.debug "id: %d" id;
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




      (* | Prel (Rle, t1, t2) ->
          (Self.feedback "found rel";
            match t1.term_node with
            | Tapp ({l_var_info={lv_name="\\abs";_}; _}, _, [e]) ->
                Self.feedback "FOund \\abs";

            | _ -> Self.feedback "no \\abs"
          )
      | Papp _ ->
        Self.feedback "dound app"
        | Prel _ ->
          Self.feedback "dound rel 2" *)
      (* | _ -> Self.feedback "dound nothing";
          None *)




(* let setInstr =
  Set () *)

let copy_compinfo_to_mpfr ci =
  let new_flds =
    Option.map
      (List.map
        (fun fld ->
          fld.fname,
          (if not(Cil.isFloatingType fld.ftype) then fld.ftype else mpfr_type),
          None,
          [],
          unknown_loc
        )
      )
      ci.cfields
  in
  let ci' =
    Cil_const.mkCompInfo
      true
      (ci.cname ^ "_mpfr")
      ~norig:(if ci.corig_name = "" then "" else ci.corig_name ^ "_mpfr")
      (fun _ -> new_flds)
      []
  in ci'


(* let rec interleave_zip_list = function
  | [] -> []
  | (a,b)::t -> a::b::(interleave_zip_list t) *)

(*Copies all struct and union definitions into MPFR ones (if they have
any float members) A map from original to mpfr_struct is also recorded*)
class struct_and_union_copier = object (self)
  inherit Visitor.frama_c_inplace
  val mutable struct_union_map = Hashtbl.create 10;
  method get_mpfr_strct_union_map () = struct_union_map

  method copy_structs f =
    Visitor.visitFramacFile
                ((self) :> Visitor.frama_c_inplace)
                f

  method! vfile f =
    let rec copy_mpfrs l = match l with
      | [] -> []
      | g::t ->
        (match g with
          | GCompTag (ci, _) when viHasFloatingType (TComp (ci, [])) ->
            let ci' = copy_compinfo_to_mpfr ci in
            Hashtbl.add struct_union_map ci ci';
            g::(GCompTag (ci', unknown_loc))::(copy_mpfrs t)
          | _ -> g::(copy_mpfrs t)
        )
    in
    f.globals <- copy_mpfrs f.globals;
    Cil.SkipChildren
end
(*Gatheres info on how many mpfr vars to create*)
class mpfr_functions_adder = object (self)
  inherit Visitor.frama_c_inplace

  val mutable mpfr_funcs_map = Hashtbl.create 10

  method get_funcs_map = mpfr_funcs_map

  method add_fns f =
    Visitor.visitFramacFile
              ((self) :> Visitor.frama_c_inplace)
              f

  method! vinst i =
    if not (Kernel_function.is_main (Option.get self#current_kf)) then
      Cil.SkipChildren
    else
      let () = match i with
        | Set (_, e, _) -> print_chr_chr_arr e
        | _ -> ()
      in Cil.SkipChildren

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
    let () = if Kernel_function.is_main kf |> not then
      let old_name = Kernel_function.get_name kf in
      let new_name = mk_new_name old_name in
      Hashtbl.add mpfr_funcs_map kf new_name
    else
      ()
    in
    Cil.DoChildren
end







(*
  mpfr_funcs_names is a map from functions to mpfr names. eg foo -> foo_mpfr
  structs map is a map from compinfo to mpfr counterparts eg
    struct A {float x;} -> struct A_mpfr {mpfr_t x;}
*)
class flosmc_transformer mpfr_funcs_names mpfr_structs_map = object (self)
  inherit Visitor.frama_c_inplace (*(Project.current ())*)

  (* val mutable glob_mpfr_vars = ViHashtbl.create 10 *)

  (* val mutable var_stack = Hashtbl.create 10 *)
  (* val mutable tmp_var_id = Hashtbl.create 10 *)
  val mutable tmp_var_queue = Hashtbl.create 10 (*Should contain all created tmp_vars*)
  val mutable res_vars = Hashtbl.create 10
  val mutable loc_mpfr_vars = Hashtbl.create 10 (*Mpfr vars for local vars per func*)
  val mutable glob_mpfr_vars = ViHashtbl.create 10 (*Mpfr vars for global vars per func*)

  (* val mutable tmp_var_map = Hashtbl.create 10 (*Map from id to tmp_var*) *)
  (* val mutable new_instrs = Hashtbl.create 5  (*Instructions to add per func*) *)

  (* val mutable tmp_var_queue = Hashtbl.create 10 *)
  val mutable fn_mpfr_names_to_vis = Hashtbl.create 10

  method get_tmp_var_queue () = tmp_var_queue
  method get_res_vars () = res_vars
  method get_loc_mpfr_vars () = loc_mpfr_vars
  method get_glob_mpfr_vars () = glob_mpfr_vars
  method get_fn_mpfr_names_to_vis () = fn_mpfr_names_to_vis

  method set_tmp_var_queue q = tmp_var_queue <- q
  method set_res_vars rvs = res_vars <- rvs
  method set_loc_mpfr_vars lvs = loc_mpfr_vars <- lvs
  method set_glob_mpfr_vars gvs = glob_mpfr_vars <- gvs
  method set_fn_mpfr_names_to_vis mnvis = fn_mpfr_names_to_vis <- mnvis

  (* method get_glob_mpfr_vars () : varinfo ViHashtbl.t = glob_mpfr_vars *)

  (*Hack until it breaks, should be an enum of type mpfr_rnd_t*)

  method queueOneInstr i = self#queueInstr [i]

  (*Gets the corresponding mpfr type of a varinfo,
  returns None if no exists
  *)
  method get_mpfr_type = function
    | TNamed (ti, _)  -> self#get_mpfr_type ti.ttype
    | TFloat _  -> Some mpfr_type
    | TComp (ci, a) -> (match Hashtbl.find_opt mpfr_structs_map ci with
                  | Some ci' -> Some (TComp (ci', a)) | None -> None)
    | t -> Kernel.debug ~level:3 "no type for: %a" Printer.pp_typ t; None

  method get_res_vi kf =
    match Hashtbl.find_opt res_vars kf with
      | Some vi -> vi
      | None -> let vi = Cil.makeVarinfo false true "res_mpfr" mpfr_type in
                Hashtbl.add res_vars kf vi;
                vi

  method get_local_or_glob_mpfr vi kf =
    let m_vi = if vi.vglob then self#get_global_mpfr vi else
      self#get_local_mpfr kf vi
    in
    Kernel.debug ~level:3 "Getting m_vi: %a %a" Printer.pp_varinfo vi Printer.pp_varinfo m_vi;
    m_vi

(*returns mpfr version of local var, should only be called if mpfr can be created*)
  method get_local_mpfr kf vi =
    let locs = match Hashtbl.find_opt loc_mpfr_vars (Kernel_function.get_name kf) with
      | Some locs' -> locs'
      | None -> (Kernel.debug ~level:3 "Found no locs";
                let locs' = Hashtbl.create 20 in
                Hashtbl.add loc_mpfr_vars (Kernel_function.get_name kf) locs';
                locs')
    in
    let l_m_vi = match Hashtbl.find_opt locs vi with
      | Some l_m_vi' -> l_m_vi'
      | None ->
          let l_m_vi' = vi_to_mpfr_with_newtype vi
                        (Option.get (self#get_mpfr_type vi.vtype))
          in
          Hashtbl.add locs vi l_m_vi';
          l_m_vi'
    in
    Kernel.debug ~level:3 "SND";
    Hashtbl.iter (fun a b -> Kernel.debug ~level:3 "v: %a - %a" Printer.pp_varinfo a Printer.pp_varinfo b) locs;
    l_m_vi

  method get_global_mpfr vi =
    (* Self.feedback "len: %d" (ViHashtbl.length glob_mpfr_vars);
    Self.feedback "glob vi: %a" Printer.pp_varinfo vi; *)
    match ViHashtbl.find_opt glob_mpfr_vars vi with
      | Some m_vi -> m_vi
      | None -> Kernel.fatal "global var not found here: %a" Printer.pp_varinfo vi
    (* assert false; (*Not yet implemented*)
    Glob vi *)


  method fetch_tmp_var kf =
    let var_q = match Hashtbl.find_opt tmp_var_queue (Kernel_function.get_name kf) with
      | Some q -> q
      | None -> let q = new tmpVarQueue in
                Hashtbl.add tmp_var_queue (Kernel_function.get_name kf) q;
                q
    in
    var_q#fetch_var ()
    (* match Queue.take_opt var_q with
        | Some v -> v
        | None -> let id = self#incr_tmp_id kf in
                  let var = self#get_mpfr_from_id id in
                  var *)

  (*puts the tmp_var back into the queue, does nothing otherwise*)
  method return_tmp_var kf var =
    match Hashtbl.find_opt tmp_var_queue (Kernel_function.get_name kf) with
      | Some q -> q#return_var var
      | None -> ()
  (*Returns an exp if it is a tmp_var*)
  method return_tmp_var_exp kf viexp =
    match viexp.enode with
      | Lval (Var vi, _) -> self#return_tmp_var kf vi
      | _ -> ()

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



  method push_str_float_constant fl_str kf =
    let mpfr_var = self#fetch_tmp_var kf in
    self#queueOneInstr (mpfr_set_const_str_instr fl_str mpfr_var rnd_exp);
    mpfr_var

  method push_float_constant fl kf =
    let mpfr_var = self#fetch_tmp_var kf in
    let fl_enode = Const (CReal (fl, FFloat, None)) in
    let fl_exp = Cil.new_exp ~loc:unknown_loc fl_enode in
    self#queueOneInstr (mpfr_set_const_instr fl_exp
        (var_to_exp mpfr_var) rnd_exp);
    (* self#push_var mpfr_var kf; *)
    mpfr_var

  (* method pop_var kf =
    let st = Hashtbl.find var_stack kf in
    Stack.pop st *)

  method get_mpfr_fn_vi og_name =
    Kernel.debug ~level:3 "fn_vi: %s" og_name;
    match Hashtbl.find_opt mpfr_funcs_names og_name with
      | Some m_name -> Some (Hashtbl.find fn_mpfr_names_to_vis m_name)
      | None -> None

  method add_init_clear_stmt locs =
    if locs = [] then (Cil.mkEmptyStmt (), Cil.mkEmptyStmt ())
    else
      let init_stmt = Cil.mkStmtOneInstr (get_mpfr_inits_instr locs) in
      let clear_stmt = Cil.mkStmtOneInstr (get_mpfr_clears_instr locs) in
      (init_stmt, clear_stmt)

  method translate f =
    let f' = Visitor.visitFramacFileCopy
              ((self) :> Visitor.frama_c_inplace)
              f
    in
    f'
  method! vglob_aux = function
    | GFun _ -> Cil.DoChildren
    | _ -> Cil.SkipChildren

  method! vfile f =
     let fun' = (fun f' ->
      let new_globs =
        List.map (fun vi -> GVarDecl (vi, unknown_loc))
        (List.of_seq (ViHashtbl.to_seq_values (self#get_glob_mpfr_vars ())))
      in
        (* Updates the list of globals *)
      f'.globals <- (math_include_global::mpfr_include_global::include_flsmc::new_globs) @ f'.globals;
      (* f'.globals <- new_globs @ f'.globals; *)

      (* Self.feedback "%a" Printer.pp_file f'; *)
      f'
    )
    in
    let filter_fl_vars g =
      match g with
        | GVar (vi, _, _) when viHasFloatingType vi.vtype -> Some vi
        | GVarDecl (vi, _) when vi.vstorage = Extern && viHasFloatingType vi.vtype -> Some vi
        | _ -> None
    in
    let fl_vars = List.filter_map filter_fl_vars f.globals in
    glob_mpfr_vars <-
      ViHashtbl.of_seq
      (List.to_seq
      (List.map (fun vi -> (vi, vi_to_mpfr_with_newtype vi
                    (Option.get (self#get_mpfr_type vi.vtype)))) fl_vars));
    ViHashtbl.iter
      (fun k v -> Self.debug "k: %a, v: %a" Printer.pp_varinfo k Printer.pp_varinfo v) glob_mpfr_vars;
    Cil.DoChildrenPost fun'

  method! vvrbl vi =
    match self#current_kf with
      | None -> Cil.DoChildren
      | Some(kf) ->
        let kf = Option.get self#current_kf in
        let fun' = (fun vi' ->
          match Cil.unrollType vi.vtype with
            | TFloat(_,_) ->
              let m_v = self#get_local_or_glob_mpfr vi' kf in
              (* self#push_var m_v kf; *)
              m_v
            | TComp (ci, _) as tci when viHasFloatingType tci ->
                self#get_local_or_glob_mpfr vi' kf
            | TFun(t, maybe_args, variable, attrs) ->
              (match self#get_mpfr_fn_vi vi'.vorig_name with
                | Some m_v -> m_v
                | None -> vi')
            | _ -> vi'
          )
      in
      Cil.DoChildrenPost fun'

  method struct_lval_to_mpfr lv =
    match lv with
      | (Var vi', NoOffset) -> var_to_exp vi'
      | (lh, (Field (_,_) as fld)) ->
          Cil.new_exp ~loc:unknown_loc (Lval (lh, fld))

  method! vinst i =
    let kf = Option.get self#current_kf in
    let add_set_help vi_exp e =
      (* let e_var = exp_to_vi e' in *)
      self#return_tmp_var_exp kf e;
      [mpfr_set_instr vi_exp e rnd_exp]
    in
    match i with
      (* | Set ((Var {vtype=t; _} as vi, NoOffset), _, _) when Cil.isFloatingType t ->
        let fun' = (fun i' ->
            match i' with
              | [Set ((Var vi', _), e', loc')] -> add_set_help (var_to_exp vi') e'
              | _ -> Kernel.fatal "some weird happened"
            )
        in
        Cil.DoChildrenPost fun' *)
      (* | Set ((Mem (Lval (Var vi, Field fi)))) -> *)
     | Set (lv, _, _) when Cil.isFloatingType (Cil.typeOfLval lv) ->
          let fun' = (fun i' ->
            match i' with
              (* | Set ((Mem (Lval (Var vi', Field fi')))) -> *)
              | [Set (lv', e', _)] ->
                let mpfr_lv = self#struct_lval_to_mpfr lv' in
                add_set_help mpfr_lv e'
              | _ -> Kernel.fatal "some weird happened2"
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
              (* let vi_exp = exp_to_vi e' in *)
              self#return_tmp_var kf (exp_to_vi e');
              let instr = mpfr_set_instr (var_to_exp res_vi) e' rnd_exp in
              self#queueOneInstr instr;
              Cil.mkStmt (Return (None, unknown_loc))
            | _ -> Kernel.fatal "some weird happened"
        )
      in
      Cil.DoChildrenPost fun'
      | _ -> Cil.DoChildren

  method! vspec _ = Cil.SkipChildren

  method add_mpfr_stuff_to_func name f' =
    let kf = Option.get self#current_kf in
    Self.debug "%s" (Kernel_function.get_name kf);
    (*Fix locals*)
    let tmp_m_locs =
      (hashtbl_get_default tmp_var_queue (Kernel_function.get_name kf) (new tmpVarQueue))#to_list
    in
    let loc_ht = hashtbl_get_default loc_mpfr_vars (Kernel_function.get_name kf) (Hashtbl.create 1) in
    let og_locs_to_keep =
      List.filter (fun x -> (Hashtbl.mem loc_ht x) |> not) f'.slocals in
    let loc_m_locs =
      List.filter (fun x -> not x.vformal)
        (List.of_seq (Hashtbl.to_seq_values loc_ht)) in
    (* let stmts_to_add = List.of_seq (Queue.to_seq stmts) in *)
    let all_m_locs = (tmp_m_locs @ loc_m_locs) in
    let all_locs = og_locs_to_keep @ all_m_locs in
    let (init_stmt, clear_stmt) = self#add_init_clear_stmt all_m_locs in
    f'.slocals <- all_locs;
    f'.sbody.blocals <- all_locs;
    f'.sbody.bstmts <-
      add_snd_last clear_stmt ([init_stmt] @ f'.sbody.bstmts);
    let fhelp ({vtype=t;_} as vi) =
      if viHasFloatingType t then self#get_local_or_glob_mpfr vi kf else vi
    in
    let formals = List.map fhelp (Kernel_function.get_formals kf) in
    let res_vi_as_list = match Hashtbl.find_opt res_vars kf with
      | Some res_vi -> [res_vi]
      | None -> []
    in
     (* if Cil.isFloatingType f.svar.vtype then [self#get_res_vi kf] else [] in *)
    let all_formals = formals @ res_vi_as_list in
    let () = Cil.setFormals f' all_formals in
    f'.sformals <- all_formals;
    let forms_unrolled =
      (List.map (fun a -> (a.vname, a.vtype, a.vattr)) all_formals)
    in            (* Cil.update_var_type *)
    let () = match f'.svar.vtype with
        | TFun(_, args, fa, aa) ->
          Cil.setFunctionType f'
            (TFun(Cil.voidType, Some forms_unrolled, fa, aa));
        | _ -> Kernel.fatal ~current:true "not a function type"
    in
    Self.debug "typ: %a" Printer.pp_typ f'.svar.vtype;
    Hashtbl.add fn_mpfr_names_to_vis name f'.svar;
    Self.debug "fdec: %a" Cil_printer.pp_fundec f';
    f'

  method! vfunc f =
    (* let new_f = Cil.emptyFunction ("m_" ^ f.svar.vname) in *)
    Kernel.debug ~level:3 "Entering vfunc for %a" Printer.pp_fundec f;
    match self#current_kf with
      | Some(kf) ->
        let name = (Kernel_function.get_name kf) in
        if Seq.exists (fun n -> n = name) (Hashtbl.to_seq_values mpfr_funcs_names) then
          (Kernel.debug ~level:3 "Found mpfr func: %s" name;
          let fun' = self#add_mpfr_stuff_to_func name in
          Cil.DoChildrenPost fun')
        else
          if Kernel_function.is_main kf then
              (let (init_stmt, clear_stmt) =
                self#add_init_clear_stmt (List.of_seq
                    (ViHashtbl.to_seq_values glob_mpfr_vars))
              in
              f.sbody.bstmts <-
                add_snd_last clear_stmt
                  (*Adding dummy stmt, which shall be used by next spec visitor
                    to insert the specification in mpfr mode
                  *)
                  (* ([mpfr_set_prec_stmt 256;init_stmt;Cil.dummyStmt] @ f.sbody.bstmts); *)
                  ([mpfr_set_prec_stmt 256;init_stmt] @ f.sbody.bstmts);
              Cil.ChangeTo f)
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


  method vconst_any fl fl_str =
    Kernel.debug ~level:3 "Pushing const fl: %f" fl;
    let m_v = match fl_str with
     | Some s -> self#push_str_float_constant s (Option.get self#current_kf)
     | None -> self#push_float_constant fl (Option.get self#current_kf)
    in
    m_v


  method vbinop_any a b oper =
    let kf = Option.get self#current_kf in
    self#return_tmp_var_exp kf b;
    self#return_tmp_var_exp kf a;
    let r = var_to_exp (self#fetch_tmp_var kf) in
    let instr = make_binop_mpfr a b r oper rnd_exp in
    self#queueOneInstr instr;
    r

  method! vexpr e =
    let kf = Option.get self#current_kf in
    match e.enode with
        | Const(CReal(fl, _, fl_str)) ->
        let fun' = (fun e ->
          var_to_exp (self#vconst_any fl fl_str)
        )
        in
        Cil.DoChildrenPost fun'
        | BinOp (_,_,_,t) when Cil.isFloatingType t ->
          let f = (fun e' ->
            match e'.enode with
              | BinOp (oper', e1', e2', t') ->
                (* let (a,b) = (exp_to_vi e1', exp_to_vi e2') in *)
                self#vbinop_any e1' e2' oper'
              | _ -> Kernel.fatal "some weird happened"
          )
          in
          Cil.DoChildrenPost f
        | BinOp (bop,a,b,_) when
              is_compare_op bop &&
              Cil.isFloatingType (type_of_exp_node a.enode) &&
              Cil.isFloatingType (type_of_exp_node b.enode) ->
          let f = (fun e' ->
            match e'.enode with
              | BinOp (oper', e1', e2', t') ->
                (* let (a,b) = (exp_to_vi e1', exp_to_vi e2') in *)
                self#return_tmp_var_exp kf e2';
                self#return_tmp_var_exp kf e1';
                let r = Cil.var (Cil.makeTempVar
                  (Kernel_function.get_definition kf) Cil.intType)
                in
                self#queueOneInstr @@ make_cmp_binop_mpfr e1' e2' r oper';
                lval_to_exp r
              | _ -> Kernel.fatal "some weird happened"
          )
          in
          Cil.DoChildrenPost f
        | UnOp (uop, e, t) when Cil.isFloatingType t ->
          let fun' = (fun e' -> match e'.enode with
                        | UnOp (uop', e'', t) ->
                        (*'hack', just set to itself*)
                        let instr = make_unop_mpfr e'' e'' uop rnd_exp in
                        self#queueOneInstr instr;
                        e''
                        | _ -> Kernel.fatal "Some weird happened in unop"
                      )
          in Cil.DoChildrenPost fun'
        | CastE _ -> (*Ignore casts for exps that have been converted into mpfr type*)
          let fun' = (fun e' -> match e'.enode with
            | CastE (t', e'') when type_of_exp_node e''.enode = mpfr_type -> e''
            | _ -> e'
          ) in
          Cil.DoChildrenPost fun'
        | _ -> Cil.DoChildren
end
