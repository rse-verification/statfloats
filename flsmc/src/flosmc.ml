open Flosmc_visitor
open Selfplugin
open Parse_prob_contract
open Mpfr_utils
open Real_verifier
open Cil_types



let pretty_print_time () =
  let time = Unix.localtime (Unix.time ()) in
  Printf.sprintf "%04d-%02d-%02d_%02d-%02d-%02d"
    (1900 + time.tm_year)  (* Year *)
    (time.tm_mon + 1)      (* Month *)
    time.tm_mday           (* Day *)
    time.tm_hour           (* Hour *)
    time.tm_min            (* Minute *)
    time.tm_sec            (* Second *)

class file_manager = object (self)
  val mutable exec_fname = "out"
  val mutable mpfr_fname = "mpfr_out.c"
  val mutable real_fname = "real_out.c"
  val mutable dir_name = "tmp"
  val mutable diff_fname = "diff.csv"

  val mutable samples_fname = "samples.csv"
  val mutable user_has_samples = false

  method remove_samples_file () = Sys.remove @@ self#get_samples_path ()

  method remove_diff_file () = Sys.remove @@ self#get_diff_path ()

  method handle_user_samples () =
    (*If user provides samples, then we copy the file to the new destination*)
    let usersamples = SampleFile.get () in
    Self.feedback "user smaple file: %s" usersamples;
    if usersamples <> "" then
      (
         user_has_samples <- true;
         samples_fname <- "user_samples.csv";
         let cmd = "cp " ^ usersamples ^ " " ^ (self#get_samples_path ()) in
         Self.debug ~level:2 "hello: %s" cmd;
         ignore @@ Sys.command cmd
      )
    else ()

  method user_has_samples () = user_has_samples

  (*makes the dir, if user_has_samples is true then also copies the user
    samples to the directory.*)
  method make_dir_name () =
    let files = (List.map File.get_name (File.get_all ())) in
    if List.is_empty files then
      (Self.debug ~level:3 "no files found";
      ())
    else (
        let outdir = OutDir.get () in
        let out_dir_name = if outdir <> "" then outdir else
          let fname = Filename.remove_extension (List.hd files) in
          let dt = pretty_print_time () in
          fname ^ "_" ^ dt
        in
        let curr_dir = Sys.getcwd () in
        dir_name <- curr_dir ^ "/" ^ out_dir_name;
        let () = if not (Sys.file_exists dir_name) then
        Sys.mkdir dir_name 0o777 in ()
      )


  method get_exec_path () = dir_name ^ "/" ^ exec_fname
  method get_mpfr_path () = dir_name ^ "/" ^ mpfr_fname
  method get_real_path () = dir_name ^ "/" ^ real_fname
  method get_diff_path () = dir_name ^ "/" ^ diff_fname
  method get_samples_path () = dir_name ^ "/" ^ samples_fname


  method print_astfile_to_file fname f =
    Printer.pp_file
        (Format.formatter_of_out_channel (open_out fname)) f

  method print_to_mpfr_file f =
    Self.debug ~level:3 "start with mpfr printing";
    self#print_astfile_to_file (self#get_mpfr_path ()) f;
    Self.debug ~level:3 "done with mpfr printing"

  method print_to_real_file f =
    self#print_astfile_to_file (self#get_real_path ()) f


  method compile_mpfr_file () =
    let compile_cmd =
      Printf.sprintf "gcc -O3 %s -lmpfr -lgmp -lm -o %s"
        (self#get_mpfr_path ()) (self#get_exec_path ());
    in
    ignore @@ Sys.command compile_cmd
end

let fmgr = ref (new file_manager)

(* let get_out_file_name ?fend=".c" fname =
  let curr_dir = Sys.getcwd () in
  let out_dir = OutDir.get () in
  let time_str = get_current_datetime () in
  curr_dir ^ "/" ^ out_dir ^ "/" fname ^ "_" ^ time_str ^ "." ^ fend *)




let generate () =
  Self.feedback "Starting FloSMC, the statistical model checker for floats";
  Self.feedback "Please note that implicit type casting may not be correctly supported";
  !fmgr#make_dir_name ();
  !fmgr#handle_user_samples ();

  let stat_prj = Project.create_by_copy ~last:true "stat_prj" in
  let real_prj = Project.create_by_copy ~last:true "real_prj" in
  Project.set_current stat_prj;
  (*Add new empty main function*)
  let main_adder = new main_name_fixer in
  let _ = Visitor.visitFramacFileCopy
    (main_adder :> Visitor.frama_c_copy) (Ast.get ()) in
  Self.debug ~level:1 "Done with adding main (0th step)";
  let entry_name =
    if main_adder#get_changed_main () then main_adder#get_new_main_name ()
    else Kernel.MainFunction.get_plain_string ()
  in
  Self.debug ~level:3 "entry_name_set_to: %s" entry_name;

  (* Add structs/union defs for mpfr *)
  let struct_vis = new struct_and_union_copier in
  struct_vis#copy_structs (Ast.get ());
  let structs_map = struct_vis#get_mpfr_strct_union_map () in
  Self.debug ~level:1 "Done with adding structs (0.5th step)";

  (*Add function defs for mpfr (not yet rewriting statements)*)
  let myvis2 = new mpfr_functions_adder in
  let _ = myvis2#add_fns (Ast.get ()) in
  Self.debug ~level:1 "Done with adding funcs (first step)";
  let mpfr_fns =
    Hashtbl.of_seq
      (Seq.map (fun (kf, new_name) -> (Kernel_function.get_name kf, new_name))
        (Hashtbl.to_seq myvis2#get_funcs_map))
  in

  (*Rewrite all statements in mpfr_funcs into mpfr_mode. Also changes
   all variables into mpfr at appropriate places*)
  let myvis = new flosmc_transformer mpfr_fns structs_map in
  let new_file = myvis#translate (Ast.get ()) in
  Self.debug ~level:1 "done with transforming functions";

  (*Parse the spec into what can be used for statistical analysis*)
  let specparser = new mpfr_contracts_parser mpfr_fns structs_map
    entry_name !fmgr in
  specparser#init_from_transformer myvis;
  let new_file2 = specparser#parse_spec new_file in
  Self.debug ~level:1 "done with parsing spec";

  (*Print resulting transformed file*)
  Self.debug ~level:3 "printing to mpfr file";
  !fmgr#print_to_mpfr_file new_file2;

  (*Parse spec into deterministic pred over reals*)
  Project.set_current real_prj;
  let realvis = new real_verifier entry_name in
  let new_file3 = Visitor.visitFramacFileCopy
    (realvis :> Visitor.frama_c_copy) (Ast.get ()) in

  Self.debug ~level:3 "printing to real file";
  !fmgr#print_to_real_file new_file3;


  (*Extract user-specified confidence level, probability and diff*)
  (* let prob, conf = (specparser#get_prob (), specparser#get_conf_level ()) in
  let diff = specparser#get_diff () in *)
  specparser

(*returns out file name*)



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
      !fmgr#compile_mpfr_file ();
      (* if (AnalyzeEnabled.get ()) then *)
      let flt_eq = specparser#make_flteq_contract () in
      let sa = new Statistical_analyser.statistical_analyser !fmgr flt_eq in
      sa#analyse ();
      let () =
        if (PlotDiffsEnabled.get ()) then
          Plotting.plot_diffs (!fmgr#get_diff_path ())
        else ()
      in
      if (not (SaveSamples.get ())) then begin !fmgr#remove_samples_file () end;
      if (not (SaveDiffs.get ())) then begin !fmgr#remove_diff_file () end;
      ()
      (* if (RealVerificationEnabled.get ()) then
         *)
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
