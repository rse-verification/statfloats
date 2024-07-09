open Flosmc_visitor
open Selfplugin
open Parse_prob_contract
open Mpfr_utils
open Real_verifier


let generate () =
  Self.feedback "Starting FloSMC, the statistical model checker for floats";
  Self.feedback "Please note that implicit type casting may not be correctly supported";
  let stat_prj = Project.create_by_copy ~last:true "stat_prj" in
  let real_prj = Project.create_by_copy ~last:true "real_prj" in
  Project.set_current stat_prj;
  (*Add new empty main function*)
  let main_adder = new main_name_fixer in
  let _ = Visitor.visitFramacFileCopy (main_adder :> Visitor.frama_c_copy) (Ast.get ()) in
  Self.feedback "Done with adding main (0th step)";

  (* Add structs/union defs for mpfr *)
  let struct_vis = new struct_and_union_copier in
  struct_vis#copy_structs (Ast.get ());
  let structs_map = struct_vis#get_mpfr_strct_union_map () in
  Self.feedback "Done with adding structs (0.5th step)";

  (*Add function defs for mpfr (not yet rewriting statements)*)
  let myvis2 = new mpfr_functions_adder in
  let _ = myvis2#add_fns (Ast.get ()) in
  Self.feedback "Done with adding funcs (first step)";
  let mpfr_fns =
    Hashtbl.of_seq
      (Seq.map (fun (kf, new_name) -> (Kernel_function.get_name kf, new_name))
        (Hashtbl.to_seq myvis2#get_funcs_map))
  in

  (*Rewrite all statements in mpfr_funcs into mpfr_mode. Also changes
   all variables into mpfr at appropriate places*)
  let myvis = new flosmc_transformer mpfr_fns structs_map in
  let new_file = myvis#translate (Ast.get ()) in
  Self.feedback "done with transforming functions";

  (*Parse the spec into what can be used for statistical analysis*)
  let specparser = new mpfr_contracts_parser mpfr_fns structs_map "entry" in
  specparser#init_from_transformer myvis;
  let new_file2 = specparser#parse_spec new_file in
  Self.feedback "done with parsing spec";

  (*Print resulting transformed file*)
  Printer.pp_file
      (Format.formatter_of_out_channel (open_out (MPFRFile.get ()))) new_file2;

  (*Parse spec into deterministic pred over reals*)
  Project.set_current real_prj;
  let realvis = new real_verifier "entry" in
  let new_file3 = Visitor.visitFramacFileCopy
    (realvis :> Visitor.frama_c_copy) (Ast.get ()) in

  Printer.pp_file
    (Format.formatter_of_out_channel (open_out "real_out.c")) new_file3;

  (*Extract user-specified confidence level, probability and diff*)
  (* let prob, conf = (specparser#get_prob (), specparser#get_conf_level ()) in
  let diff = specparser#get_diff () in *)
  specparser

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
    (let specparser = generate () in
    (* if (AnalyzeEnabled.get ()) then *)
    let out_name = make_c_file () in
    let csv_fname = "../output_files/diff.csv" in
    let flt_eq = specparser#make_flteq_contract () in
    let sa = new Statistical_analyser.statistical_analyser
      out_name csv_fname flt_eq
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
