open Flosmc_visitor
open Selfplugin


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
    let myvis2 = new mpfr_functions_adder in
    let _ = myvis2#add_fns (Ast.get ()) in
    let mpfr_fns =
      Hashtbl.of_seq
        (Seq.map (fun (kf, new_name) -> (Kernel_function.get_name kf, new_name))
          (Hashtbl.to_seq myvis2#get_funcs_map))
    in
    let myvis = new flosmc_transformer mpfr_fns in
    let _ = myvis#translate (Ast.get ()) in
(*    let () = Hashtbl.iter (fun x y -> Self.feedback "%s: %d" x y) vars_per_func in*)
    ()


let () = Db.Main.extend run
