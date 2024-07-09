open Mpfr_utils
open Selfplugin

(*Converts a probabilistic contract over floats into a deterministic one
  to be verified wrt reals*)
class real_verifier entry = object (self)
  inherit Visitor.frama_c_inplace
  method! vglob_aux = function
    | GFun (f, _) when f.svar.vorig_name = "entry"-> Cil.DoChildren
    | _ -> Cil.SkipChildren

  method! vbehavior b =
    (* Kernel.assert (Kernel_function.get_name (Option.get self#current_kf) = "entry"); *)
    Self.debug ~level:3 "spec: %a" Printer.pp_behavior b;
    match b with
      | {b_extended=be;_} ->
        let (_, pred) = split_into_dist_and_pred be in
        (match pred.ext_kind with
          | Ext_annot ("ProbClause", [_;_;{ext_kind=Ext_preds [p];_}]) ->
            (match p.pred_content with
              | Papp (li, _, [t1; t2; _]) when li.l_var_info.lv_name = "flteq" ->
                let new_pred = make_id_pred_from_pred_node (Prel (Req, t1, t2)) in
                b.b_extended <- [];
                b.b_post_cond <- [(Normal, new_pred)];
                Cil.ChangeTo b
              | _ -> Kernel.fatal "Only flteq currently supported"
            )
          | _ -> Cil.SkipChildren
        )
end
