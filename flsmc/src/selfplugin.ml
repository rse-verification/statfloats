let help_msg = "Statistical Model Checking of Floats"
module Self = Plugin.Register
  (struct

  let name = "FloStat"
  let shortname = "fs"
  let help = help_msg
end)


module Enabled = Self.False
  (struct
  let option_name = "-flostat"
  let help = "when on (off by default), " ^ help_msg
end)

(* module MPFRFile = Self.String(struct
  let option_name = "-mpfr-file"
  let default = "/home/jesper/Documents/floats/statfloats/flostat/output_files/out.c"
  let arg_name = "mpfr_file"
  let help = "file where the mpfr code is stored."
end) *)

module OutDir = Self.String(struct
  let option_name = "-fs-out-dir"
  let default = ""
  let arg_name = "out_dir"
  let help = "Folder where the output is stored. If omitted, a new dir will be created automatically."
end)

module SampleFile = Self.String(struct
  let option_name = "-fs-sample-file"
  let default = ""
  let arg_name = "sample_file"
  let help = "File with input sample values. If not provided,
    FloStat will sample randomly. If samples are provided, they must align exactly
    with the input variables of the specified function."
end)



module NrExecs = Self.Int(struct
  let option_name = "-fs-execs"
  let short_name = "-execs"
  let default = 10
  let arg_name = "nr_execs"
  let help = "number of executions"
end)

module MPFRPrec = Self.Int(struct
  let option_name = "-fs-prec"
  let short_name = "-prec"
  let default = 256
  let arg_name = "precision"
  let help = "Precision in bits used for the MPFR simulation"
end)

module OnlySample = Self.False
  (struct
  let option_name = "-fs-only-sample"
  let short_name = "-FloStat-sample"
  let help = "when on (off by default), only samples the input values, does not perform the statistical analysis"
end)

module StatisticalAnalysisEnabled = Self.True
  (struct
  let option_name = "-FloStat-statistical-analysis"
  let short_name = "-FloStat-stat"
  let help = "when on (on by default), performs statistical analysis of the rounding error"
end)

module PlotDiffsEnabled = Self.False
  (struct
  let option_name = "-FloStat-plot-diffs"
  let help = "when on (off by default), plots diffs"
end)

module RealVerificationEnabled = Self.True
  (struct
  let option_name = "-FloStat-real-verification"
  let short_name = "-FloStat-real"
  let help = "when on (on by default), verifies the contract wrp real semantics"
end)

module MpfrForExtern = Self.True
  (struct
  let option_name = "-FloStat-extern-mpfr"
  let help = "when on (on by default), creates mpfr-vars for all floats declared with 'extern'"
end)
