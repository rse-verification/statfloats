open Csv
open Selfplugin
open Prob_contract
open Cil_types
open Owl
open Mpfr_utils


let get_csv_col header csv =
  let headers, data = match csv with h :: d -> h, d | [] -> assert false in
  let data2 = Csv.associate headers data in
  List.concat (List.map (fun l ->
      List.map snd (List.filter (fun s ->
          fst s = header) l)) data2)



let conf_level eps n =
  Self.feedback "EPS: %g, n: %d" eps n;
  exp(-.(2.0 *. (float_of_int n) *. (eps *. eps)))


(*Left conf if meas is geq than requested
  RIght conf otherwise
*)
let one_sided_conf_test req_v meas_v n =
  (* P(P − ˆP ≥ ε) ≤ δ *)
  if meas_v < req_v then
    (let eps = req_v -. meas_v in
     Either.Right (conf_level eps n))
  else
    (let eps = meas_v -. req_v in
     Either.Left (conf_level eps n))


class statistical_analyser bin csv_fname (prob_contract:flteq_contract) = object (self)
  method get_sample_funs = function
    | d::t ->
      (match d with
        | {dname="Uniform"; dvar=x; dparams=[a;b]} ->
          Self.debug ~level:3 "found dist";
          let [fl_a; fl_b] = List.map term_to_fl_const [a;b] in
          let f' = (fun () -> Stats.uniform_rvs ~a:fl_a ~b:fl_b) in
          (x, f')::(self#get_sample_funs t)
        | {dname=dname;_} -> Kernel.fatal "only uniform dist currenly supported: %s" dname)
    | [] ->
      Self.debug ~level:3 "found  no more dist";
      []

  method do_samples n =
    Self.feedback "Starting sampleing";
    let sample_fns = self#get_sample_funs (prob_contract#get_dists ()) in
    let samples = List.init n
      (fun _ -> List.map (fun (_,f') -> string_of_float (f' ())) sample_fns) in
    let headers = List.map (fun (x, _) ->
      Format.asprintf "%a" Printer.pp_term x) sample_fns
    in
    (* List.iter (List.iter (fun x -> Self.feedback "%s" x)) (headers::samples); *)
    Csv.save ~separator:',' "../output_files/samples.csv" (samples)

  method run_file n =
    let exec_cmd = Printf.sprintf "%s %d" bin n in
    ignore @@ Sys.command exec_cmd;

  method calc_avg () =
    let x = Csv.load csv_fname in
    (* Self.feedback "q:%s" (snd (List.hd @@ List.hd data)); *)
    let data2 = get_csv_col "diff" x in
    let qdata = List.map Q.of_string data2 in
    let qdata2 = List.fold_left Q.add Q.zero qdata in
    Q.div qdata2 (Q.of_int (List.length qdata))

  method get_meas_prob () =
    let diff_q = Q.of_float (prob_contract#get_fl_diff ()) in
    let x = Csv.load csv_fname in
    (* Self.feedback "q:%s" (snd (List.hd @@ List.hd data)); *)
    let data2 = get_csv_col "diff" x in
    let qdata = List.map (fun x -> Q.abs (Q.of_string x)) data2 in
    let bools = List.filter (fun x -> Q.leq x diff_q) qdata in
    (float_of_int (List.length bools)) /. (float_of_int (List.length qdata))

  method analyse () =
    let n = NrExecs.get () in
    self#do_samples n;
    (* self.do_samples (); *)
    self#run_file n;
    (* let avg = self#calc_avg () in *)
    (* Self.feedback "AVG: %.17g" (Q.to_float avg); *)
    (* let meas_conf = self#get_meas_conf_level () in *)
    let meas_prob = self#get_meas_prob () in
    Self.debug ~level:3 "Measured prob: %g" meas_prob;
    let meas_conf = one_sided_conf_test
      (prob_contract#get_prob ()) meas_prob n
    in
    match meas_conf with
      | Left c ->
          let () = if c < (prob_contract#get_confLevel ()) then
            Self.feedback "Success!"
          else
            Self.feedback "Failure!\n\
            The measured conf level is worse than the specified"
          in
          Self.feedback
            "Stats\n\
            Measured probability: %g  Requested probability: %g \n \
            Measured conf level: %g   Requested conf level: %g"
            meas_prob (prob_contract#get_prob ())
                      c (prob_contract#get_confLevel ())
      | Right c ->
          Self.feedback "Failure!\n\
            The measured probability is smaller than the specified \n\
            Measured probability: %g  Requested probability: %g \n "
            meas_prob (prob_contract#get_prob ())
end
