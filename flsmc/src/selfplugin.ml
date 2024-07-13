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

module MPFRFile = Self.String(struct
  let option_name = "-mpfr-file"
  let default = "/home/jesper/Documents/floats/statfloats/flsmc/output_files/out.c"
  let arg_name = "mpfr_file"
  let help = "file where the mpfr code is stored."
end)

module NrExecs = Self.Int(struct
  let option_name = "-nr-of-executions"
  let short_name = "-execs"
  let default = 10
  let arg_name = "nr_execs"
  let help = "number of executions"
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
