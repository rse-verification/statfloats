open Flosmc_visitor
open Selfplugin
open Prob_contract


module Enabled = Self.False
  (struct
  let option_name = "-flosmc"
  let help = "when on (off by default), " ^ help_msg
end)

module MPFRFile = Self.String(struct
  let option_name = "-mpfr-file"
  let default = "/home/jesper/Documents/floats/statfloats/flsmc/output_files/out.c"
  let arg_name = "mpfr-file"
  let help = "file where the mpfr code is stored."
end)

module AnalyzeEnabled = Self.False
  (struct
  let option_name = "-flosmc-analyse"
  let help = "when on (off by default), " ^ help_msg
end)

module MpfrForExtern = Self.True
  (struct
  let option_name = "-flosmc-extern-mpfr"
  let help = "when on (on by default), creates mpfr-vars for all floats declared with 'extern'"
end)

let generate () =
  Self.feedback "Starting FloSMC, the statistical model checker for floats";
  Self.feedback "Please note that implicit type casting may not be correctly supported";
  (* Self.feedback "1. %a" Printer.pp_file (Ast.get ()); *)
  let new_prj = Project.create_by_copy ~last:true "new_prj" in
  Project.set_current new_prj;
  let struct_vis = new struct_and_union_copier in
  struct_vis#copy_structs (Ast.get ());
  let myvis2 = new mpfr_functions_adder in
  (* Self.feedback "%a" Printer.pp_file (Ast.get ()); *)
  let _ = myvis2#add_fns (Ast.get ()) in
  Self.feedback "Done with adding funcs (first step)";
  (* Self.feedback "%a" Printer.pp_file (Ast.get ()); *)
  let mpfr_fns =
    Hashtbl.of_seq
      (Seq.map (fun (kf, new_name) -> (Kernel_function.get_name kf, new_name))
        (Hashtbl.to_seq myvis2#get_funcs_map))
  in
  let structs_map = struct_vis#get_mpfr_strct_union_map () in
  let myvis = new flosmc_transformer mpfr_fns structs_map in
  let specparser = new mpfr_contracts_parser mpfr_fns structs_map "entry" in
  let new_file = myvis#translate (Ast.get ()) in
  Self.feedback "done with transforming functions";
  specparser#init_from_transformer myvis;
  let new_file2 = specparser#parse_spec new_file in
  Self.feedback "done with parsing spec";
  Printer.without_annot
    Printer.pp_file
      (Format.formatter_of_out_channel (open_out (MPFRFile.get ()))) new_file2;
  let prob, conf = (specparser#get_prob (), specparser#get_conf_level ()) in
  let diff = specparser#get_diff () in
  (prob, conf, diff)



(*returns out file name*)
let make_c_file () =
  let fname = MPFRFile.get () in
  Self.feedback "%s" fname;
  let out_name = "../output_files/out" in
  let compile_cmd =
    Printf.sprintf "gcc %s -lmpfr -lgmp -lm -o %s" fname out_name;
  in
  ignore @@ Sys.command compile_cmd;
  out_name


(* let run () =
  if not (Enabled.get ()) then
    if (AnalyzeEnabled.get ()) then
      (let out_name = make_c_file () in
      let csv_fname = "../output_files/diff.csv" in
      let sa = new Statistical_analyser.statistical_analyser out_name csv_fname in
      sa#analyse)
    else ()
  else
    generate () *)

let run () =
  if (Enabled.get ()) then
    (let prob, conf, diff = generate () in
    (* if (AnalyzeEnabled.get ()) then *)
    let out_name = make_c_file () in
    let csv_fname = "../output_files/diff.csv" in
    let sa = new Statistical_analyser.statistical_analyser
      out_name csv_fname prob conf diff
    in
    sa#analyse ()
    )
    (* else () *)
  else ()


    (* Project.set_current_as_last_created (); *)

    (* let specvis = new mpfr_spec_adder in
    let _ = specvis#add_spec (Ast.get ()) in *)

(*    let () = Hashtbl.iter (fun x y -> Self.feedback "%s: %d" x y) vars_per_func in*)

(* let () = Acsl_extension.register_behavior "prob_dist" type_probDist false ~plugin:"flsmc" *)
let () = Acsl_extension.register_behavior "probPred" type_probPred false ~plugin:"flsmc"
let () = Acsl_extension.register_behavior "prob" type_prob false ~plugin:"flsmc"
let () = Acsl_extension.register_behavior "confLevel" type_conf false ~plugin:"flsmc"
let () = Acsl_extension.register_behavior "distribution" type_distribution false ~plugin:"flsmc"
let () = Acsl_extension.register_behavior "prob_ensures" type_probContract false ~plugin:"flsmc"
let () = Boot.Main.extend run
