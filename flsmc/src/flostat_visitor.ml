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
      else Kernel.fatal "should always return last var %a" Printer.pp_varinfo vi)
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

(* let rec interleave_zip_list = function
  | [] -> []
  | (a,b)::t -> a::b::(interleave_zip_list t) *)

(*Copies all struct and union definitions into MPFR ones (if they have
any float members) A map from original to mpfr_struct is also recorded*)
class struct_and_union_copier = object (self)
  inherit Visitor.frama_c_inplace
  val mutable struct_union_map = Hashtbl.create 10;
  method get_mpfr_strct_union_map () = struct_union_map

  method ci_to_type ci = {tnode = TComp ci; tattr = []}

  method copy_structs f =
    Visitor.visitFramacFile
                ((self) :> Visitor.frama_c_inplace)
                f

  method! vfile f =
    let rec copy_mpfrs l = match l with
      | [] -> []
      | g::t ->
        (match g with
          | GCompTag (ci, _) when hasFloatingType (Cil_const.mk_tcomp ci) ->
            let ci' = self#copy_compinfo_to_mpfr ci in
            g::(GCompTag (ci', unknown_loc))::(copy_mpfrs t)
          | _ -> g::(copy_mpfrs t)
        )
    in
    Self.debug ~level:4 "done with adding structs";
    f.globals <- copy_mpfrs f.globals;
    Self.debug ~level:4 "snd done with adding structs";

    Cil.SkipChildren
  method copy_compinfo_to_mpfr ci =
    match Hashtbl.find_opt struct_union_map ci with
    | Some ci' -> ci'
    | None ->
      let rec get_mpfr_fld_type t =
        match Ast_types.unroll_node t with
        | TComp nested when hasFloatingType t ->
            Cil_const.mk_tcomp (self#copy_compinfo_to_mpfr nested)
        | TPtr pointee when hasFloatingType pointee ->
            {tnode = TPtr (get_mpfr_fld_type pointee); tattr = t.tattr}
        | TArray (element, length) when hasFloatingType t ->
            {tnode = TArray (get_mpfr_fld_type element, length); tattr = t.tattr}
        | _ when Ast_types.is_float t -> mpfr_type
        | _ -> t
      in
      let new_flds =
        Option.map
          (List.map
            (fun fld ->
              fld.fname,
              get_mpfr_fld_type fld.ftype,
              None,
              None,
              [],
              unknown_loc
            )
          )
          ci.cfields
      in
      let ci' =
        Cil_const.mkCompInfo
          ci.cstruct
          (ci.cname ^ "_mpfr")
          ~norig:(if ci.corig_name = "" then "" else ci.corig_name ^ "_mpfr")
          (fun _ -> new_flds)
          []
      in
      Hashtbl.add struct_union_map ci ci';
      ci'
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
class flostat_transformer mpfr_funcs_names mpfr_structs_map = object (self)
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
  method get_mpfr_type t = match t.tnode with
    | TNamed ti  -> self#get_mpfr_type ti.ttype
    | TFloat _  -> Some mpfr_type
    | TPtr t' -> (match self#get_mpfr_type t' with
      | Some t'' -> Some {tnode = TPtr t''; tattr = t.tattr}
      | None -> None )
    | TComp ci -> (match Hashtbl.find_opt mpfr_structs_map ci with
                  | Some ci' -> Some (Cil_const.mk_tcomp ci') | None -> None)
    | _ -> Self.debug ~level:3 "no type for: %a" Printer.pp_typ t; None

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
    Self.debug ~level:3 "Getting m_vi: %a %a" Printer.pp_varinfo vi Printer.pp_varinfo m_vi;
    m_vi

(*returns mpfr version of local var, should only be called if mpfr can be created*)
  method get_local_mpfr kf vi =
    let locs = match Hashtbl.find_opt loc_mpfr_vars (Kernel_function.get_name kf) with
      | Some locs' -> locs'
      | None -> (Self.debug ~level:3 "Found no locs in %s" (Kernel_function.get_name kf);
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
    Hashtbl.iter (fun a b -> Self.debug ~level:5 "in %s: %a - %a" (Kernel_function.get_name kf) Printer.pp_varinfo a Printer.pp_varinfo b) locs;
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
    self#queueOneInstr (mpfr_set_flt_instr fl_exp
        (var_to_exp mpfr_var) rnd_exp);
    (* self#push_var mpfr_var kf; *)
    mpfr_var

  (* method pop_var kf =
    let st = Hashtbl.find var_stack kf in
    Stack.pop st *)

  method get_mpfr_fn_vi og_name =
    Self.debug ~level:3 "fn_vi: %s" og_name;
    match Hashtbl.find_opt mpfr_funcs_names og_name with
      | Some m_name -> Some (Hashtbl.find fn_mpfr_names_to_vis m_name)
      | None -> None

  (*adds init and clear stmt for all vars in locs to f*)
  method add_init_clear_stmt ?(before_init=None) f locs =
    if locs = [] then () (*(Cil.mkEmptyStmt (), Cil.mkEmptyStmt ())*)
    else
      let init_stmt = Cil.mkStmtOneInstr (get_mpfr_inits_instr locs) in
      let clear_stmt = Cil.mkStmtOneInstr (get_mpfr_clears_instr locs) in
      f.sbody.bstmts <-
        if Option.is_none before_init then
          add_snd_last clear_stmt ([init_stmt] @ f.sbody.bstmts)
        else
          add_snd_last clear_stmt
            ([(Option.get before_init);init_stmt] @ f.sbody.bstmts)

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
      f'.globals <- (get_include_list ()) @ new_globs @ f'.globals;
      f'
    )
    in
    let filter_fl_vars g =
      match g with
        | GVar (vi, _, _) when hasFloatingType vi.vtype -> Some vi
        | GVarDecl (vi, _) when vi.vstorage = Extern &&
            hasFloatingType vi.vtype -> Some vi
        | _ -> None
    in
    let fl_vars = List.filter_map filter_fl_vars f.globals in
    glob_mpfr_vars <-
      ViHashtbl.of_seq
      (List.to_seq
      (List.map (fun vi -> (vi, vi_to_mpfr_with_newtype vi
                    (Option.get (self#get_mpfr_type vi.vtype)))) fl_vars));
    ViHashtbl.iter
      (fun k v -> Self.debug "k: %a, v: %a"
        Printer.pp_varinfo k Printer.pp_varinfo v) glob_mpfr_vars;
    Cil.DoChildrenPost fun'

  method! vvrbl vi =
    match self#current_kf with
      | None -> Cil.DoChildren
      | Some(kf) ->
        let kf = Option.get self#current_kf in
        let fun' = (fun vi' ->
          match Ast_types.unroll_node vi.vtype with
            | TFloat _ ->
              let m_v = self#get_local_or_glob_mpfr vi' kf in
              (* self#push_var m_v kf; *)
              m_v
            | TComp ci when hasFloatingType vi.vtype ->
                self#get_local_or_glob_mpfr vi' kf
            | TPtr t when hasFloatingType t ->
                self#get_local_or_glob_mpfr vi' kf
            | TFun(_, _, _) ->
              (match self#get_mpfr_fn_vi vi'.vorig_name with
                | Some m_v -> m_v
                | None -> vi')
            (* | TPtr({tnode = TFloat _; tattr = _}) ->  *)
            (* | _ -> Self. *)
            | _ -> Self.feedback "varinfo not changed: %a" Printer.pp_varinfo vi'; vi'
          )
      in
      Cil.DoChildrenPost fun'

  method struct_lval_to_mpfr lv =
    Cil.new_exp ~loc:unknown_loc (Lval lv)

  method mpfr_field field =
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
            Kernel.fatal "MPFR struct %s has no field definitions" ci.cname)

  method mpfr_offset = function
    | NoOffset -> NoOffset
    | Field (field, rest) -> Field (self#mpfr_field field, self#mpfr_offset rest)
    | Index (exp, rest) -> Index (exp, self#mpfr_offset rest)

  method append_offset prefix suffix =
    match prefix with
    | NoOffset -> suffix
    | Field (f, rest) -> Field (f, self#append_offset rest suffix)
    | Index (e, rest) -> Index (e, self#append_offset rest suffix)

  method lval_with_offset (host, offset) more =
    (host, self#append_offset offset more)

  method exp_of_lval lv =
    Cil.new_exp ~loc:unknown_loc (Lval lv)

  method copy_mpfr_struct_lval dst src loc =
    let rec copy dst src dst_type src_type =
      if dst_type = mpfr_type then
        [mpfr_set_instr (self#exp_of_lval dst) (self#exp_of_lval src) rnd_exp]
      else
        match Ast_types.unroll_node dst_type, Ast_types.unroll_node src_type with
        | TComp dst_ci, TComp src_ci when dst_ci.cstruct && src_ci.cstruct ->
          let dst_fields = Option.value dst_ci.cfields ~default:[] in
          let src_fields = Option.value src_ci.cfields ~default:[] in
          if List.length dst_fields <> List.length src_fields then
            Kernel.fatal "mismatched struct fields in MPFR struct assignment";
          List.concat (List.map2 (fun dst_field src_field ->
            copy
              (self#lval_with_offset dst (Field (dst_field, NoOffset)))
              (self#lval_with_offset src (Field (src_field, NoOffset)))
              dst_field.ftype src_field.ftype
          ) dst_fields src_fields)
        | TArray (dst_elt, Some dst_len), TArray (src_elt, Some src_len) ->
          (match dst_len.enode, src_len.enode with
          | Const (CInt64 (dst_len, _, _)), Const (CInt64 (src_len, _, _))
            when Z.equal dst_len src_len && Z.sign dst_len >= 0 ->
            List.concat_map (fun i ->
              let index = Cil.integer ~loc:unknown_loc i in
              copy
                (self#lval_with_offset dst (Index (index, NoOffset)))
                (self#lval_with_offset src (Index (index, NoOffset)))
                dst_elt src_elt
            ) (List.init (Z.to_int dst_len) Fun.id)
          | _ -> Kernel.fatal "non-constant array in MPFR struct assignment")
        | TArray (_, None), TArray (_, None) -> []
        | _ ->
          [Set (dst, self#exp_of_lval src, loc)]
    in
    copy dst src (Cil.typeOfLval dst) (Cil.typeOfLval src)

  method! vinst i =
    let kf = Option.get self#current_kf in
    let add_set_help vi_exp e =
      (* let e_var = exp_to_vi e' in *)
      self#return_tmp_var_exp kf e;
      [mpfr_set_instr vi_exp e rnd_exp]
    in
    match i with
      (* | Set ((Var {vtype=t; _} as vi, NoOffset), _, _) when Ast_types.is_float t ->
        let fun' = (fun i' ->
            match i' with
              | [Set ((Var vi', _), e', loc')] -> add_set_help (var_to_exp vi') e'
              | _ -> Kernel.fatal "some weird happened"
            )
        in
        Cil.DoChildrenPost fun' *)
      (* | Set ((Mem (Lval (Var vi, Field fi)))) -> *)
     | Set (lv, _, _) when Ast_types.is_float (Cil.typeOfLval lv) ->
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
      | Set (lv, _, _)
        when (match Ast_types.unroll_node (Cil.typeOfLval lv) with
          | TComp _ | TArray _ -> hasFloatingType (Cil.typeOfLval lv)
          | _ -> false) ->
          let fun' = (function
            | [Set (lv', {enode = Lval src; _}, loc)] ->
              self#copy_mpfr_struct_lval lv' src loc
            | [Set _] ->
              Kernel.fatal "MPFR struct assignment requires an lvalue source"
            | _ -> Kernel.fatal "unexpected MPFR struct assignment")
          in
          Cil.DoChildrenPost fun'
      | Local_init (_, ConsInit (callee, _, _), _)
        when is_transendental_fun callee ||
             Hashtbl.mem mpfr_funcs_names callee.vorig_name ->
          let fun' = (function
            | [Local_init (vi, ConsInit (_, args, _), loc)] ->
                let result = var_to_exp vi in
                let mpfr_call =
                  if is_transendental_fun callee then
                    Call
                      (None, Var (mpfr_trans_fn_vi callee),
                       result :: args @ [zero_exp], loc)
                  else
                    let fn_vi = Option.get (self#get_mpfr_fn_vi callee.vorig_name) in
                    Call (None, Var fn_vi, args @ [result], loc)
                in
                [mpfr_call]
            | _ -> Kernel.fatal "unexpected function local initialization")
          in
          Cil.DoChildrenPost fun'
      | Call (Some _, _, _, _) ->
        let fun' = (fun i' ->
            match i' with
              | [Call (Some result_lv, Var vi, args_exps', loc')] ->
                  let result_exp = self#exp_of_lval result_lv in
                  (*Check if transendental, then use mpfr version for this*)
                  if (is_transendental_fun vi) then
                        [Call (None, Var (mpfr_trans_fn_vi vi),
                          (result_exp::args_exps') @ [zero_exp], loc')]
                  else
                    [Call (None, Var vi, args_exps' @ [result_exp], loc')]
                  (* [mpfr_set_instr vi' e_var rnd_exp] *)
              | _ -> Kernel.fatal "some weird happened"
            (* let m_vi = self#get_local_or_glob_mpfr vi kf in *)
            )
            in
            Cil.DoChildrenPost fun'

      | Local_init (vi, AssignInit (SingleInit e), _) when Ast_types.is_float vi.vtype ->
          let fun' = (fun i' ->
            match i' with
              | [Local_init (vi', AssignInit (SingleInit e'), loc)] ->
                  [mpfr_set_instr (var_to_exp vi') e' rnd_exp]
              | _ -> Kernel.fatal "some weird happened"
          )
          in Cil.DoChildrenPost fun'
      | Local_init (vi, AssignInit (SingleInit _), _) ->
          (match Ast_types.unroll_node vi.vtype with
          | TPtr t when hasFloatingType t ->
              let fun' = (function
                | [Local_init (vi', AssignInit (SingleInit e'), loc)] ->
                    [Set ((Var vi', NoOffset), e', loc)]
                | _ -> Kernel.fatal "unexpected pointer local initialization")
              in
              Cil.DoChildrenPost fun'
          | _ -> Cil.DoChildren)
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



  method make_mpfr_func name f' =
    List.iter (fun vi -> Self.debug ~level:3 "ivhere: %a" Printer.pp_varinfo vi) f'.slocals;
    let kf = Option.get self#current_kf in
    (*Fix locals*)
    let tmp_m_locs =
      (hashtbl_get_default tmp_var_queue (Kernel_function.get_name kf) (new tmpVarQueue))#to_list
    in
    let loc_ht = hashtbl_get_default loc_mpfr_vars (Kernel_function.get_name kf)
      (Hashtbl.create 1) in
    Self.debug ~level:3 "Adding mpfr stuff for: %s" (Kernel_function.get_name kf);
    let og_locs_to_keep =
      List.filter (fun x -> (Hashtbl.mem loc_ht x) |> not) f'.slocals in
    let loc_m_locs =
      List.filter (fun x -> not x.vformal)
        (List.of_seq (Hashtbl.to_seq_values loc_ht)) in

    (* let stmts_to_add = List.of_seq (Queue.to_seq stmts) in *)
    let all_m_locs = (tmp_m_locs @ loc_m_locs) in
    let all_locs = og_locs_to_keep @ all_m_locs in
    f'.slocals <- all_locs;
    f'.sbody.blocals <- all_locs;
    self#add_init_clear_stmt f' all_m_locs;
    let fhelp ({vtype=t;_} as vi) =
      if hasFloatingType t then self#get_local_or_glob_mpfr vi kf else vi
    in
    let formals = List.map fhelp (Kernel_function.get_formals kf) in
    let res_vi_as_list =
      if Ast_types.is_float (Cil.getReturnType f'.svar.vtype) then
        [self#get_res_vi kf]
      else
        []
    in
     (* if Ast_types.is_float f.svar.vtype then [self#get_res_vi kf] else [] in *)
    let all_formals = formals @ res_vi_as_list in
    let () = Cil.setFormals f' all_formals in
    f'.sformals <- all_formals;
    let formals_unrolled =
      (List.map (fun a -> (a.vname, a.vtype, a.vattr)) all_formals)
    in            (* Cil.update_var_type *)
    let () = match f'.svar.vtype with
        | {tnode = TFun(_, args, fa); tattr = aa}  ->
          Cil.setFunctionType f'
            {tnode = TFun(Cil_const.voidType, Some formals_unrolled, fa); tattr = aa}
        | _ -> Kernel.fatal ~current:true "not a function type"
    in
    Hashtbl.add fn_mpfr_names_to_vis name f'.svar;
    f'

  method! vfunc f =
    (* let new_f = Cil.emptyFunction ("m_" ^ f.svar.vname) in *)
    Self.debug ~level:3 "Entering vfunc for %a" Printer.pp_fundec f;
    match self#current_kf with
      | Some(kf) ->
        let name = (Kernel_function.get_name kf) in
        if Seq.exists (fun n -> n = name) (Hashtbl.to_seq_values mpfr_funcs_names) then
          (Self.debug ~level:3 "Found mpfr func: %s" name;
          let fun' = self#make_mpfr_func name in
          Cil.DoChildrenPost fun')
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
    Self.debug ~level:3 "Pushing const fl: %f" fl;
    let m_v = match fl_str with
     | Some s -> self#push_str_float_constant s (Option.get self#current_kf)
     | None -> self#push_float_constant fl (Option.get self#current_kf)
    in
    m_v


  method vbinop_any a b oper =
    Self.debug ~level:3 "binop with a: %a, b: %a, op: %a"
      Printer.pp_exp a Printer.pp_exp b Printer.pp_binop oper;
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
        | Lval (_, offset) ->
          let fun' = (fun e' -> match e'.enode with
            | Lval (host, offset') ->
                Cil.new_exp ~loc:e'.eloc (Lval (host, self#mpfr_offset offset'))
            | _ -> e'
          ) in
          Cil.DoChildrenPost fun'
        | AddrOf (_, offset) ->
          let fun' = (fun e' -> match e'.enode with
            | AddrOf (host, offset') ->
                (match host, offset' with
                | Var vi, NoOffset when vi.vformal && vi.vtype = mpfr_type ->
                    Cil.mkCast ~newt:mpfr_ptr_type (var_to_exp vi)
                | _ ->
                    Cil.new_exp ~loc:e'.eloc
                      (AddrOf (host, self#mpfr_offset offset')))
            | _ -> e'
          ) in
          Cil.DoChildrenPost fun'
        | StartOf (_, offset) ->
          let fun' = (fun e' -> match e'.enode with
            | StartOf (host, offset') ->
                Cil.new_exp ~loc:e'.eloc (StartOf (host, self#mpfr_offset offset'))
            | _ -> e'
          ) in
          Cil.DoChildrenPost fun'
        | Const(CReal(fl, _, fl_str)) ->
        let fun' = (fun e ->
          var_to_exp (self#vconst_any fl fl_str)
        )
        in
        Cil.DoChildrenPost fun'
        | BinOp (_,_,_,t) when Ast_types.is_float t ->
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
              Ast_types.is_float (Cil.typeOf a) &&
              Ast_types.is_float (Cil.typeOf b) ->
          let f = (fun e' ->
            match e'.enode with
              | BinOp (oper', e1', e2', t') ->
                (* let (a,b) = (exp_to_vi e1', exp_to_vi e2') in *)
                self#return_tmp_var_exp kf e2';
                self#return_tmp_var_exp kf e1';
                let r = Cil.var (Cil.makeTempVar
                  (Kernel_function.get_definition kf) Cil_const.intType)
                in
                self#queueOneInstr @@ make_cmp_binop_mpfr e1' e2' r oper';
                lval_to_exp r
              | _ -> Kernel.fatal "some weird happened"
          )
          in
          Cil.DoChildrenPost f
        | UnOp (uop, e, t) when Ast_types.is_float t ->
          let fun' = (fun e' -> match e'.enode with
              | UnOp (uop', e'', t) ->
                  self#return_tmp_var_exp kf e'';
                  let new_var_exp = var_to_exp (self#fetch_tmp_var kf) in
                  let instr = make_unop_mpfr e'' new_var_exp uop rnd_exp in
                  self#queueOneInstr instr;
                  new_var_exp
              | _ -> Kernel.fatal "Some weird happened in unop"
          )
          in Cil.DoChildrenPost fun'
        | CastE _ -> (*Ignore casts for exps that have been converted into mpfr type*)
          let fun' = (fun e' -> match e'.enode with
            | CastE (t', e'') when Cil.typeOf e'' = mpfr_type -> e''
            | _ -> e'
          ) in
          Cil.DoChildrenPost fun'
        | _ -> Cil.DoChildren
end
