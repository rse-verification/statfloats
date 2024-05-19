open Flosmc_visitor
open Selfplugin
open Prob_contract


module Enabled = Self.False
  (struct
  let option_name = "-flosmc"
  let help = "when on (off by default), " ^ help_msg
end)

let run () =
  if not (Enabled.get ()) then ()
  else
    Self.feedback "Starting FloSMC, the statistical model checker for floats";
    Self.feedback "Please note that implicit type casting may not be correctly supported";
    let new_prj = Project.create_by_copy ~last:true "new_prj" in
    Project.set_current new_prj;
    let myvis2 = new mpfr_functions_adder in
    let _ = myvis2#add_fns (Ast.get ()) in
    let mpfr_fns =
      Hashtbl.of_seq
        (Seq.map (fun (kf, new_name) -> (Kernel_function.get_name kf, new_name))
          (Hashtbl.to_seq myvis2#get_funcs_map))
    in
    let myvis = new flosmc_transformer mpfr_fns in
    let specparser = new mpfr_contracts_parser "entry" in
    let specvis = new mpfr_spec_adder "entry" in

    (* let _ = myvis#translate (Ast.get ()) in *)

    (* File.create_project_from_visitor "new_prj"
      (fun prj -> ((myvis prj) :> Visitor.frama_c_inplace)) in *)
    (* File.pretty_ast
      ~fmt:(Format.formatter_of_out_channel (open_out "tmp_out.c")) (); *)
    let new_file = myvis#translate (Ast.get ()) in
    let new_file2 = specparser#parse_spec new_file in
    let new_file3 = specvis#add_spec new_file2 in
    Printer.pp_file (Format.formatter_of_out_channel (open_out "tmp_out.c")) new_file3;



    (* Project.set_current_as_last_created (); *)

    (* let specvis = new mpfr_spec_adder in
    let _ = specvis#add_spec (Ast.get ()) in *)

(*    let () = Hashtbl.iter (fun x y -> Self.feedback "%s: %d" x y) vars_per_func in*)
    ()

(* let () = Acsl_extension.register_behavior "prob_dist" type_probDist false ~plugin:"flsmc" *)
let () = Acsl_extension.register_behavior "probPred" type_probPred false ~plugin:"flsmc"
let () = Acsl_extension.register_behavior "prob" type_prob false ~plugin:"flsmc"
let () = Acsl_extension.register_behavior "confLevel" type_conf false ~plugin:"flsmc"
let () = Acsl_extension.register_behavior "prob_ensures" type_probContract false ~plugin:"flsmc"
let () = Boot.Main.extend run
