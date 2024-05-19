open Cil_types
open Logic_typing
open Mpfr_utils
open Logic_const
open Cil
open Selfplugin


(* let foo () = () *)
let type_probContract type_ctxt loc [prob; conf; pred] =
  Self.feedback "before creating old";
  (* let env_with_old = enter_post_state (Lenv.empty ()) Normal in *)
  (* let env_with_old = enter_post_state
    (Lenv.add_logic_label "Old" Logic_const.old_label (Lenv.empty ())) Normal in *)
  let env_with_old = post_state_env Normal Lreal in
  Self.feedback "after old'";
  let prob' = type_ctxt.type_term type_ctxt env_with_old prob in
  let conf' = type_ctxt.type_term type_ctxt env_with_old conf in
  Self.feedback "after årp'";
  let pred' = type_ctxt.type_predicate type_ctxt env_with_old pred in
  Self.feedback "after åred'";
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


class mpfr_contracts_parser entry_name = object (self)
  inherit Visitor.frama_c_inplace

  val mutable prob = 0.1
  val mutable conf_level = 0.95
  val mutable pred = None

  method get_prob () = prob
  method set_prob p_ext =
    let p = match p_ext.ext_kind with
      (* | Ext_annot ("prob", [{ext_kind=Ext_terms [t];_}]) ->
        0.99 *)
        (* get_nearest_float_from_lreal_constant t *)
      | Ext_terms [t] -> get_nearest_float_from_lreal_constant t
      | _ -> Kernel.fatal "not a single term"
    in
    Self.feedback "conf: %f" p;
    prob <- p

  method get_conf_level () = conf_level
  method set_conf_level c_ext =
  let c = match c_ext.ext_kind with
    | Ext_terms [t] ->
      get_nearest_float_from_lreal_constant t
    | _ -> Kernel.fatal "not a single term"
  in
  Self.feedback "conf: %f" c;
  conf_level <- c

  method get_pred () = Option.get pred
  method get_option_pred () = pred
  method set_pred p = pred <- Some p


  method parse_spec f =
    Visitor.visitFramacFileCopy
              ((self) :> Visitor.frama_c_copy)
              f
  method is_in_entry_func () =
    match self#current_kf with
      | None -> false
      | Some kf ->
        Self.feedback "%s :: %s" (Kernel_function.get_name kf) entry_name;
        Kernel_function.get_name kf = entry_name

  method! vfunc f =
    if self#is_in_entry_func ()
    then Cil.DoChildren
    else Cil.SkipChildren (*Avoid traversing other funcs*)


  method! vspec s =
    let kf = Option.get self#current_kf in
    if self#is_in_entry_func () |> not then
      Cil.SkipChildren
    else
      (Self.feedback "what here: %a" Cil_printer.pp_funspec s;
      match s.spec_behavior with
        | [] ->
          Kernel.fatal "no spec for main func"
        | [{b_extended=[ext]; _}] -> (match ext.ext_kind with
            | Ext_annot ("ProbClause", [prob_ext;conf_ext;pred_ext]) ->
              self#set_prob prob_ext;
              self#set_conf_level conf_ext;
              self#set_pred pred_ext;
              Cil.DoChildren
            | _ -> Kernel.fatal "not a prob clause extension"
          )
        | [_] -> Kernel.fatal "no extension found"
        | _ -> Kernel.fatal "multiple behaviors not supported"
        )
end


class mpfr_spec_adder entry_name = object (self)
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
          Self.feedback "spec has no post condition";
          Cil.DoChildren
        | post_li ->
          let new_post = List.map self#ensures_help post_li in
          Cil.DoChildren)
    else
      Cil.DoChildren
end
