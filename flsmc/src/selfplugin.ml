let help_msg = "Statistical Model Checking of Floats"
module Self = Plugin.Register
  (struct

  let name = "flosmc"
  let shortname = "fs"
  let help = help_msg
end)


module Enabled = Self.False
  (struct
  let option_name = "-flosmc"
  let help = "when on (off by default), " ^ help_msg
end)

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
    flosmc will sample randomly. If samples are provided, they must align exactly
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

module Seed = Self.Int(struct
  let option_name = "-fs-seed"
  let short_name = "-fs-seed"
  let default = 0
  let arg_name = "seed"
  let help = "Seed for the mpfr random samples. If set to 0 (default), then will use Ocaml default seed. I.e., set to some non-zero value if you want to set the seed."
end)

module OnlySample = Self.False
  (struct
  let option_name = "-fs-only-sample"
  let short_name = "-flosmc-sample"
  let help = "when on (off by default), only samples the input values, does not perform the statistical analysis"
end)

module StatisticalAnalysisEnabled = Self.True
  (struct
  let option_name = "-flosmc-statistical-analysis"
  let short_name = "-flosmc-stat"
  let help = "when on (on by default), performs statistical analysis of the rounding error"
end)

module PlotDiffsEnabled = Self.False
  (struct
  let option_name = "-flosmc-plot-diffs"
  let help = "when on (off by default), plots diffs"
end)

module RealVerificationEnabled = Self.True
  (struct
  let option_name = "-flosmc-real-verification"
  let short_name = "-flosmc-real"
  let help = "when on (on by default), verifies the contract wrp real semantics"
end)

module MpfrForExtern = Self.True
  (struct
  let option_name = "-flosmc-extern-mpfr"
  let help = "when on (on by default), creates mpfr-vars for all floats declared with 'extern'"
end)


module SaveSamples = Self.True
  (struct
  let option_name = "-fs-save-samples"
  let help = "when on (on by default), saves the samples in file 'samples.csv'"
end)

module SaveDiffs = Self.True
  (struct
  let option_name = "-fs-save-diffs"
  let help = "when on (on by default), saves the diffs in file 'diff.csv'"
end)
