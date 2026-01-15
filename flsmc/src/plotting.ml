open Plplot
open Csv


(*assumes file has data in the form [a, b, diff], with one row header*)
let plot_diffs fname =
  let csv_data = Csv.load fname in
  let csv_diffs = List.tl @@ List.map (fun [_;_;diff] -> diff) csv_data in
  let csv_fl_diffs = List.map Float.of_string csv_diffs in
  let arr_diffs = Array.of_list csv_fl_diffs in
  let minval = Array.fold_left Float.min Float.max_float arr_diffs in
  let maxval = Array.fold_left Float.max Float.min_float arr_diffs in
  let (xmin, xmax) = 1.2*.minval, 1.2*.maxval in
  let (ymin, ymax) = 0.0, 1000.0 in
  plinit ();
  plenv xmin xmax ymin ymax 0 0 ;
  plhist arr_diffs minval maxval 100 [PL_HIST_DEFAULT];
  plend ();
  ()




let split_whitespace (s : string) : string list =
  s
  |> String.trim
  |> Str.split (Str.regexp "[ \t]+")

let load_whitespace_file (filename : string) : string list list =
  let ic = open_in filename in
  let rec loop acc =
    match input_line ic with
    | line ->
        loop (split_whitespace line :: acc)
    | exception End_of_file ->
        Stdlib.close_in ic;
        List.rev acc
  in
  loop []


let read_column ~(filename : string) ~(column : string) : float list =
  let csv = load_whitespace_file filename in
  match csv with
  | [] | [_] -> failwith "CSV file is empty or has no data rows"
  | header_row :: rows ->
      List.iter (fun x ->
      Selfplugin.Self.feedback "%s" x) header_row;
      let col_index =
        match List.find_index (( = ) column) header_row with
        | Some i -> i
        | None -> failwith ("Header not found: " ^ column)
      in
      rows
      |> List.filter_map (fun row ->
           if col_index < List.length row then
             float_of_string_opt (List.nth row col_index)
           else
             None)


let histogram ~(bins : int) (data : float list)
  : (float * int) list =
  if data = [] then failwith "No data";

  let min_v = List.fold_left Float.min infinity data in
  let max_v = List.fold_left Float.max neg_infinity data in

  let range = max_v -. min_v in
  if range = 0.0 then failwith "All values are identical";

  let bin_width = range /. float_of_int bins in
  let counts = Array.make bins 0 in

  List.iter (fun x ->
    let idx =
      if x = max_v then
        bins - 1
      else
        int_of_float ((x -. min_v) /. bin_width)
    in
    if idx >= 0 && idx < bins then
      counts.(idx) <- counts.(idx) + 1
  ) data;

  Array.to_list @@
  Array.mapi (fun i c ->
    let center =
      min_v +. (float_of_int i +. 0.5) *. bin_width
    in
    (center, c)
  ) counts


let plot_histogram (hist : (float * int) list) =
    let xs = Array.of_list (List.map fst hist) in
    let ys = Array.of_list (List.map (fun (_, y) -> float_of_int y) hist) in
    let n = Array.length xs in

    plinit ();

    let xmin = Array.fold_left min xs.(0) xs in
    let xmax = Array.fold_left max xs.(0) xs in
    let ymin = 0.0 in
    let ymax = Array.fold_left max ys.(0) ys *. 1.1 in

    plenv xmin xmax ymin ymax 0 0;
    pllab "Value" "Count" "Histogram";

    let bar_width =
      if n > 1 then xs.(1) -. xs.(0) else 1.0
    in

    plcol0 2;  (* blue *)

    for i = 0 to n - 1 do
      let x0 = xs.(i) -. bar_width /. 2.0 in
      let x1 = xs.(i) +. bar_width /. 2.0 in
      let y1 = ys.(i) in

      let px = [| x0; x1; x1; x0 |] in
      let py = [| 0.0; 0.0; y1; y1 |] in
      plfill px py
    done;

    plend ()


let plot_csv_histogram
    (filename : string)
    (column : string)
    (bins : int) =
  let data = read_column ~filename ~column in
  let hist = histogram ~bins data in
  plot_histogram hist
