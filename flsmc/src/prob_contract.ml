open Cil_types
open Logic_typing

let type_probContract type_ctxt loc l =
  let l' = List.map (type_ctxt.type_predicate type_ctxt (Lenv.empty ())) l in
  Ext_preds l'


(* class mpfr_functions_adder = object (self)
  inherit Visitor.frama_c_inplace


end *)
