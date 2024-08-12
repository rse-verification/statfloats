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
