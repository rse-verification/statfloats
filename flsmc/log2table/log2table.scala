import scala.util.parsing.combinator._
import scala.io.Source
import scala.math.log10
import java.io._

import scala.collection.SortedSet

case class VerTime(real: Double, user: Double, sys: Double) {
  override def toString = f"real: $real, user:$user, sys:$sys"

  def get_cpu_time = user + sys
}

object VerTime {
  def dummy = new VerTime(-1, -1, -1)
  def timeout(t: Double) = new VerTime(t, -1, -1)
}



class BoxPlotData(values: List[Double], val info: String) {
  def log2 = (x: Double) => log10(x)/log10(2.0)
  // Ensure the input list is sorted
  private val sortedValues = values.sorted
  private val length = values.length
  // Immutable variables
  val min: Double = (sortedValues.head)
  val max: Double = (sortedValues.last)
  val median: Double = (calculateMedian(sortedValues))
  val q1: Double = (calculateMedian(sortedValues.take(sortedValues.size / 2)))
  val q3: Double = (calculateMedian(sortedValues.drop((sortedValues.size + 1) / 2)))

  // Helper function to calculate median
  private def calculateMedian(data: List[Double]): Double = {
    val size = data.size
    if (size % 2 == 0) {
      (data(size / 2 - 1) + data(size / 2)) / 2.0
    } else {
      data(size / 2)
    }
  }
  override def toString: String = {
   f"BoxPlotData(min = $min%.2f, Q1 = $q1%.2f, median = $median%.2f, Q3 = $q3%.2f, max = $max%.2f)"
  }
  def toPgfPlotsFormatBoxPlot(style: String): String = {
    f"""
    %%$info%s
    %%$length%d
    \\addplot[
    $style%s,
      boxplot prepared={
        median=$median%.2f,
        upper quartile=$q3%.2f,
        lower quartile=$q1%.2f,
        upper whisker=$max%.2f,
        lower whisker=$min%.2f
      },
    ] coordinates {};
    """
  }
}

object Science_pp {
  def science_pp(x: Double) : String = {
    if (x == 0.0) "0"
    else {
      val formatted = f"$x%.2e"
      formatted.replaceAll("e([+-])([0-9]*)", "e{$1$2}").replaceAll(
        "e\\+00", "{e\\+0}")
    }
  }
}

trait Outcome {
    def fname : String;
    def tool : String;
    def error : Option[String];
    def diff : Option[Double];
    def verTime : VerTime;
    def to_oopsla_string: String;
    def to_oopsla_string_notime: String;
    def time_pp_oopsla(vt: VerTime) : String = {
      val t = vt.user + vt.sys
      if (t <= 10) f"${t}%.1f" + "s"
      else if (t <= 60)
        f"${t.round}s"
      else if (t < 3600) {
        val m = (t / 60).round
        // val s = t % 60z
        f"${(t/60).round}m"
      }
      // else if (t < 360000) {
      //   val h = (t / 3600).toInt
      //   val m = ((t % 3600) / 60).round
      //   f"${h}h${m}m"
      // }
      else {
        f"${(t / 3600).round}h"
      }
    }
    def science_pp(x: Double) : String = Science_pp.science_pp(x)
    def fnameNoEnding: String = {
      val dotIndex = fname.lastIndexOf('.')
      if (dotIndex > 0) fname.substring(0, dotIndex)
      else fname
    }
}

case class FsOutcome(fname: String, prec: Int, meas_prob: Double,
  diff: Option[Double], conf:Double, verTime:VerTime,
  viols: Int, execs: Int, tool: String, error: Option[String]) extends Outcome {

    override def toString = {
      "%s, %d, %g, %e, %g, %s, %d, %s".format(fname, prec, meas_prob, diff.get, conf,
        verTime.toString, execs, tool)
    }
    def to_oopsla_string = {
      val conf_str = if (isSuccess) science_pp(conf) else "n/a"
      val time_str = if (diff.isDefined) time_pp_oopsla(verTime) else "t/o"
      "$%s$ & $%s$ & %s".format(science_pp(diff.get), conf_str, time_str)
    }
    def to_oopsla_string_notime = {
      val conf_str = if (isSuccess) "$" + science_pp(conf) + "$" else "n/a"
      val prob_str = science_pp(1.0 - meas_prob)
      "$%s$ & $%s$ & %s".format(science_pp(diff.get), prob_str, conf_str)
    }
    def isSuccess = conf != -1.0
}

object FsOutcome {
  def apply(fname: String, prec: Int, meas_prob: Double,
    diff: Option[Double], conf:Double, verTime:VerTime,
    viols: Int, execs: Int, tool: String) =
      new FsOutcome(fname, prec, meas_prob, diff, conf, verTime,
                    viols, execs, tool, None)
}


case class StaticOutcome(fname: String, diff: Option[Double], verTime:VerTime,
    tool: String, error: Option[String])
  extends Outcome {

  override def toString = {
    diff match {
      case Some(d) => "%s, %e, %s, %s".format(fname, d, verTime.toString, tool)
      case None => "%s, t/o, -, %s".format(fname, tool)
    }
  }
  def to_oopsla_string = {
    (diff, error) match {
      case (Some(d), _) => {
        "$%s$ & %s".format(science_pp(d), (time_pp_oopsla(verTime)))
      }
      case (None, None) => tool match {
        case "dummy" => "n/a & n/a".format()
        case _ => "n/a & t/o".format()
      }
      case (None, Some(_)) => "error & n/a".format()

//      case (None, Some(_)) => "err & n/a".format()
    }
  }
  def to_oopsla_string_notime = {
    (diff, error) match {
      case (Some(d), _) => {
        "$%s$".format(science_pp(d))
      }
      case (None, None) => tool match {
        case "dummy" => "n/a".format()
        case _ => "n/a".format()
      }
      case (None, Some(_)) => "err & n/a".format()
//      case (None, Some(_)) => "err & n/a".format()
    }
  }
}

object StaticOutcome {
  // def apply(fname: String, diff: Option[Double], verTime:Double) =
  //   new StaticOutcome(fname, diff, verTime)
  def dummy(fname: String) =
    new StaticOutcome(fname, None, VerTime.dummy, "dummy", None)

  def fromDiff(fname: String, diff: Double, tool: String) =
    new StaticOutcome(fname, Some(diff), VerTime.dummy, tool, None)

    //If error bound is given as [a, b], where a <= 0 and b>=0
  def fromSpec(fname: String, diff: Option[Double], verTime:Option[VerTime],
        tool: String, error: Option[String]) = {
      val vt = verTime.getOrElse(VerTime.dummy)
      new StaticOutcome(fname, diff, vt, tool, error)
      // diff match {
      //   case Some(d) => new StaticOutcome(fname, Some(d), vt, tool)
      //   case Some((lo: Double, hi: Double)) => {
      //     assert(lo <= 0 && hi >= 0)
      //     val d = if (-lo >= hi) -lo else hi
      //     new StaticOutcome(fname, Some(d), vt, tool)
      //   }
      //   case None => new StaticOutcome(fname, None, vt, tool)
      // }
    }

}

abstract class SimpleParser(tool: Option[String] = None) extends RegexParsers {
  def filename: Parser[String]
  def file : Parser[Outcome]
  def skipLine = "(.*\n)".r
  def word: Parser[String]    = """[a-z]+""".r
  def integer: Parser[Int] = "[0-9]+".r ^^ { _.toInt }
  def filestart: Parser[String] = """.*Running file:\s*""".r ~> filename ^^ (_.trim)
  def fileend(fname: String): Parser[String] =
    (".*done with .*" + fname).r ^^ (_ => fname)

  def number: Parser[Double] =
      {"\\.[0-9]+".r |
      ("(-)?[0-9]+((\\.[0-9]+)?(e[+-][0-9]+)?)?".r)} ^^ { _.toDouble }
  def parseResFile(fname : String) : List[Outcome] = {
    val fcontents = scala.io.Source.fromFile(fname).mkString
    val parseResult = parse(rep(file), fcontents)
    parseResult match {
      case Success(result, _) => println("success"); result
      case Failure(msg, _) => println("Parse failure: " + msg); List()
      case Error(msg, _) => println("Parse error: " + msg); List()
    }
  }
  def parseResFiles(files: List[String]) : List[Outcome] = {
    println(f"parsing files: $files")
    files.map(parseResFile).flatten
  }
  def line: Parser[String] = """.*\n""".r
  // def verTime: Parser[String ~ Double] =
  //     "Done analysing file".r ~> filename ~ ("in".r ~> number <~ """\s*s\s*""".r)

  def timeToDouble(t: String): Double = {
      val timeRegex = "([0-9]+)m([0-9]+\\.[0-9]+)s".r
      val totalSeconds: Double = t match {
        case timeRegex(minStr, secStr) =>
          val minutes = minStr.toDouble
          val seconds = secStr.toDouble
          minutes * 60 + seconds
        case _ =>
          throw new IllegalArgumentException(s"Unexpected format: $t")
      }
      totalSeconds
  }
  private val hhmmss: Parser[Double] = (number <~ ":") ~ (number <~ ":") ~ number ^^
    {case hh ~ mm ~ ss => hh * 3600.0 + mm * 60.0 + ss}
  private val mmss: Parser[Double] = (number <~ ":") ~ number ^^
    {case mm ~ ss => mm * 60.0 + ss}

  def binUserTime: Parser[Double] = """\s*User time \(seconds\):\s+""".r ~> number
  def binSysTime: Parser[Double] = """\s*System time \(seconds\):\s+""".r ~> number
  def binRealTime: Parser[Double] =
    """\s*Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s+""".r ~> (hhmmss | mmss)

  // User time (seconds): 1690.18
  // System time (seconds): 1108.25
  // Percent of CPU this job got: 454%
  // Elapsed (wall clock) time (h:mm:ss or m:ss): 10:15.42


  def realUnixTime: Parser[Double] = """real\s+""".r ~> time ^^ { t => timeToDouble(t) }
  def userUnixTime: Parser[Double] = """user\s+""".r ~> time ^^ { t => timeToDouble(t) }
  def sysUnixTime: Parser[Double] = """sys\s+""".r ~> time ^^ { t => timeToDouble(t) }
  def time: Parser[String] = """[0-9]+m[0-9]+\.[0-9]+s""".r
    // "user" ~> """\s+""".r ~> minutes ~ ("m" ~> seconds <~ "s") ^^ {
    //   case min ~ sec => min * 60 + sec
    // }
  def verBinTime: Parser[VerTime] = {
    binUserTime ~ (binSysTime <~ line) ~ binRealTime ^^
        { case ut ~ st ~ rt => VerTime(rt, ut, st) }
  }
  def verUnixTime: Parser[VerTime] = {
      realUnixTime ~ userUnixTime ~ sysUnixTime ^^
        { case rt ~ ut ~ st => VerTime(rt, ut, st) }
  }
  def verTime: Parser[VerTime] = {
    verUnixTime | verBinTime
  }
  def __skipUntil[A](p : Parser[A]): Parser[A] = {
        rep(not(p) ~> line ^^ { l => l }) ~> p
  }
  def skipUntil[A](p : Parser[A]): Parser[A] = {
            println("skipping with: " + p.getClass)
            rep(not(p) ~> line ^^ { l =>
              println(s"⏭️ Skipped line: $l")
              l
            }) ~> p
          }
  def timeout : Parser[Double] =
    """\[Timeout\] Benchmark exceeded\s+""".r ~> number ^^ {case n => n}
  def diff : Parser[Double]
  def error : Parser[String] = "error".r
                                    // (diff, error, time)
  def diffortimeoutorerror: Parser[(Option[Double], Option[String], Option[VerTime])] = {
    //First get diff t/o or error
    def helper : Parser[(Option[Double], Option[String], Option[VerTime])] = {
      (diff ^^ {case d => (Some(d), None, None)}) |
      (timeout ^^ {case t => (None, None, Some(VerTime.timeout(t)))}) |
      (error ^^ {case e => (None, Some(e), None)} )
    }
    skipUntil(helper).flatMap {
       //if diff, add verification time (needs flatmap since parser in parser)
      case (Some(d), None, None) => {
        (skipUntil(verTime) ^^ {case vt => (Some(d), None, Some(vt))})
      }
      case x => success(x)
    }
  }
}

class FloStatParser(tool: Option[String] = None)  extends SimpleParser {
  def filename: Parser[String] = """[a-z0-9A-Z_/]+\.c""".r
  def diff: Parser[Double] = ".*requested diff:\\s*".r ~> number
  def prob: Parser[Double] = ".*Measured probability:\\s*".r ~> number
  def conf: Parser[Double]   = ".*Measured confidence level: ".r ~> number
  def probbad: Parser[String] = ".*The measured probability is smaller than the specified.*".r
  def execs: Parser[Int] = ".*Execs n:\\s*".r ~> integer

  def viols: Parser[Int] = {
    """.*Number of violations:\s*([0-9]+).*""".r ^^ {
      case line =>
        val Pattern = """.*Number of violations:\s*([0-9]+).*""".r
        line match {
          case Pattern(n) => n.toInt
        }
    }
  }
  def failorsucc: Parser[Boolean] = (".*(Failure|Success!).*".r) ^^
    {s =>
      if (s matches ".*Success.*") true else false
    }
  def failorconf: Parser[Double] = {
    failorsucc >>
      {case true => (rep(not(conf) ~> ".*".r) ~> conf) ^^ {c => c}
       case false => probbad ^^{_=> -(1.0) }
     }
   }
  def prec: Parser[Int] = ".*-fs-prec ".r ~> integer <~ ".*".r
  def file: Parser[FsOutcome] =
      skipUntil(filestart) ~
      skipUntil(prec) ~
      skipUntil(execs) ~
      skipUntil(diff) ~
      failorconf ~
      skipUntil(viols) ~
      skipUntil(prob) ~
      skipUntil(verTime) >>
        {case fname ~ prec ~ execs ~ d ~ fc ~ v ~ p ~ vt =>
          skipUntil(fileend(fname)) ^^ { case fname2 =>
            assert(fname == fname2, s"Mismatched file: expected $fname, got $fname2")
            FsOutcome(fname, prec, p, Some(d), fc, vt, v, execs, tool.getOrElse("flostat"))
          }
        }
}

object FloStatParser extends FloStatParser(Some("flostat")) {
  def apply(tool: Option[String] = None): FloStatParser = new FloStatParser(tool)
}

class SatireParser(tool: Option[String] = None) extends SimpleParser {
  def filename: Parser[String] = """[a-z0-9A-Z_]+\.txt""".r

  def diff : Parser[Double] =
    ("ABSOLUTE_ERROR : ".r ~> number)
  override def error: Parser[String] = """Command exited with non-zero status 255""".r
  // def diffortimeoutorerror : Parser[(Option[Double], Option[VerTime])] =
  //   satdiff | satto

  def file : Parser[StaticOutcome] = {
    skipUntil(filestart) ~ diffortimeoutorerror >>
    { case fname ~ ((diff, e, vt)) => //fname2 ~ vt =>
        skipUntil(fileend(fname)) ^^ { case fname2 =>
          assert(fname == fname2, s"Mismatched file: expected $fname, got $fname2")
          StaticOutcome.fromSpec(fname, diff, vt, tool.getOrElse("Satire"), e)
        }
    }
  }
}

object SatireParser extends SatireParser(Some("satire")) {
  def apply(tool: Option[String] = None): SatireParser = new SatireParser(tool)
}

class DaisyParser(tool: Option[String] = None) extends SimpleParser {
  def filename: Parser[String] = """[a-z0-9A-Z_]+\.scala""".r
  def diff : Parser[Double] = ".*Absolute error: ".r ~> number
  // def diffortimeoutorerror : Parser[Option[Double]] =
  //     (".*Absolute error: ".r ~> number ^^ {n => Some(n)}) | ("\\[Timeout\\].*".r ^^ { _ => None })
  override def error = """.*Something really bad happened.*""".r
  def file : Parser[StaticOutcome] = //(name, diff, time)
      skipUntil(filestart) ~ diffortimeoutorerror >>
      { case fname ~ ((diff, e, vt)) => //fname2 ~ vt =>
          skipUntil(fileend(fname)) ^^ { case fname2 =>
            assert(fname == fname2, s"Mismatched file: expected $fname, got $fname2")
            StaticOutcome.fromSpec(fname, diff, vt, tool.getOrElse("daisy"), e)
          }
      }
}
object DaisyParser extends DaisyParser(Some("Daisy")) {
  def apply(tool: Option[String] = None): DaisyParser = new DaisyParser(tool)
}

class PafParser(tool: Option[String] = None) extends SimpleParser {
  def filename: Parser[String] = """[a-z0-9A-Z_]+\.txt""".r
  def diff: Parser[Double] =
    (("0.99:\\[".r ~> number) ~ (", ".r ~> number <~ "\\]".r) ^^
      {case (lo ~ hi) =>
        assert(lo <= 0 && hi >= 0)
        if (-lo >= hi) -lo else hi
      })
  // def diffortimeoutorerror : Parser[Option[(Double, Double)]] =
  //     (("0.99:\\[".r ~> number) ~ (", ".r ~> number <~ "\\]".r) ^^
  //     {case (lo ~ hi) => Some(lo, hi)}) |
  //     ("\\[Timeout\\].*".r ^^ { _ => None })
  def file : Parser[StaticOutcome] = //(name, diff, time)
    skipUntil(filestart) ~ diffortimeoutorerror >>
    { case fname ~ ((diff, e, vt)) => //fname2 ~ vt =>
        skipUntil(fileend(fname)) ^^ { case fname2 =>
            assert(fname == fname2, s"Mismatched file: expected $fname, got $fname2")
            StaticOutcome.fromSpec(fname, diff, vt, tool.getOrElse("Paf"), e)
        }
    }
}
object PafParser extends PafParser(Some("Paf")) {
  def apply(tool: Option[String] = None): PafParser = new PafParser(tool)
}

object TestSimpleParser {
  val parserMap = Map(
    "flostat" -> FloStatParser(Some("flostat")),
    "flostat2" -> FloStatParser(Some("flostat2")),
    "flostat4" -> FloStatParser(Some("flostat4")),
    "flostat8" -> FloStatParser(Some("flostat8")),
    "nflostat" -> FloStatParser(Some("nflostat")),
    "nflostat2" -> FloStatParser(Some("nflostat2")),
    "nflostat4" -> FloStatParser(Some("nflostat4")),
    "nflostat8" -> FloStatParser(Some("nflostat8")),
    "satire" -> SatireParser(Some("satire")),
    "satire_lo" -> SatireParser(Some("satire_lo")),
    "paf" -> PafParser(Some("paf")),
    "daisy" -> DaisyParser(Some("daisy")),
    "daisy_fold" -> DaisyParser(Some("daisy_fold"))
  )

  // def lorenz_opers(n: Int): Int = if (n == 1) 5 else lorenz_opers(n-1) + 9 + 5
  def lorenz_opers(n: Int): Int = 14 * n - 9

  val paf_paper_errors: Map[String, Double] = Map(
    "bsplines0"   -> 5.71e-08,
    "bsplines1"   -> 1.86e-07,
    "bsplines2"   -> 1.94e-07,
    "bsplines3"   -> 4.22e-08,
    "classIDX0"   -> 6.93e-06,
    "classIDX1"   -> 3.71e-06,
    "classIDX2"   -> 5.23e-06,
    "doppler1"    -> 7.95e-05,
    "doppler2"    -> 1.43e-04,
    "doppler3"    -> 4.55e-05,
    "filter1"     -> 1.25e-07,
    "filter2"     -> 7.93e-07,
    "filter3"     -> 2.34e-06,
    "filter4"     -> 4.15e-06,
    "rigidBody1"  -> 1.74e-04,
    "rigidBody2"  -> 1.96e-02,
    "sine"        -> 2.37e-07,
    "solvecubic"  -> 1.78e-05,
    "sqrt"        -> 1.54e-04,
    "traincar1"   -> 1.76e-03,
    "traincar2"   -> 1.04e-03,
    "traincar3"   -> 1.75e-02,
    "traincar4"   -> 1.81e-01,
    "trid"        -> 6.01e-03,
    "trid2"       -> 1.03e-02,
    "trid3"       -> 1.75e-02,
    "trid4"       -> 2.69e-02
  )
  val opers_per_file = Map("bsplines0" -> 6,
                        "bsplines1" -> 8,
                        "bsplines2" -> 10,
                        "bsplines3" -> 3,
                        "classIDX0" -> 15,
                        "classIDX1" -> 15,
                        "classIDX2" -> 15,
                        "doppler1" -> 7,
                        "doppler2" -> 7,
                        "doppler3" -> 7,
                        "filter1" -> 1,
                        "filter2" -> 6,
                        "filter3" -> 15,
                        "filter4" -> 25,
                        "lorenz2" -> lorenz_opers(2),
                        "lorenz4" -> lorenz_opers(4),
                        "lorenz5" -> lorenz_opers(5),
                        "lorenz8" -> lorenz_opers(8),
                        "lorenz10" -> lorenz_opers(10),
                        "lorenz20" -> lorenz_opers(20),
                        "lorenz40" -> lorenz_opers(40),
                        "lorenz70" -> lorenz_opers(70),
                        "lorenz100" -> lorenz_opers(100),
                        "lorenz200" -> lorenz_opers(200),
                        "lorenz400" -> lorenz_opers(400),
                        "lorenz700" -> lorenz_opers(700),
                        "lorenz1000" -> lorenz_opers(1000),
                        "lorenzloop100" -> lorenz_opers(100),
                        "rigidBody1" -> 6,
                        "rigidBody2" -> 10,
                        "sine" -> 17,
                        "solveCubic" -> 14,
                        "sqrt" -> 13,
                        "traincar1" -> 6,
                        "traincar2" -> 10,
                        "traincar3" -> 17,
                        "traincar4" -> 18,
                        "trid" -> 9,
                        "trid2" -> 15,
                        "trid3" -> 21,
                        "trid4" -> 27,
                      )

  def get_files_in_dir(dirname: String) = {
    val dir = new File(dirname)
    dir.listFiles().filter(_.isFile).map(_.toString).toList
  }

    //This is wrong
  def getLorenOperations(n: Int) = {
    import scala.collection.immutable.SortedMap

    var x = SortedMap(1 -> BigInt(4))
    var y = SortedMap(1 -> BigInt(5))
    var z = SortedMap(1 -> BigInt(5))

    for (i <- 2 to n) {
      val xi = 2 * x(i - 1) + y(i - 1) + z(i - 1) + 4
      val yi = 2 * y(i - 1) + x(i - 1) + z(i - 1) + 5
      val zi = 2 * z(i - 1) + x(i - 1) + y(i - 1) + 5

      x = x + (i -> xi)
      y = y + (i -> yi)
      z = z + (i -> zi)
    }
    (x, y, z)
  }
  def minOpt_fs(a: Option[FsOutcome], b: Option[FsOutcome]): Option[FsOutcome] = {
    val MAXCONF = 0.0001
    (a,b) match {
      case (Some(a2), None) if a2.isSuccess && a2.conf <= MAXCONF => a
      case (None, Some(b2)) if b2.isSuccess => b
      case (Some(a2), Some(b2)) => (a2.isSuccess, b2.isSuccess) match {
        case (false, false) => None
        case (true, false) if a2.conf <= MAXCONF => a
        case (false, true) if b2.conf <= MAXCONF => b
        case (true, true) if a2.conf <= MAXCONF && b2.conf > MAXCONF => a
        case (true, true) if b2.conf <= MAXCONF && a2.conf > MAXCONF => b
        case (true, true) if a2.conf <= MAXCONF && b2.conf <= MAXCONF => {
          if (a2.diff.get <= b2.diff.get) a else b
        }
        case _ => None
      }
      case _ => None
    }
  }
  def minOpt(a: Option[StaticOutcome], b: Option[StaticOutcome]) = (a,b) match {

    case (Some(a2), None) if a2.diff.isDefined => a
    case (None, Some(b2)) if b2.diff.isDefined => b
    case (Some(a2), Some(b2)) => (a2.diff.isDefined, b2.diff.isDefined) match {
      case (true, true) => if (a2.diff.get < b2.diff.get) a else b
      case (true, false) => a
      case (false, true) => b
      case _ => None
    }
    case _ => None
  }

  def getAllResult(log_dir: String, tools: List[String]) = {
    import java.io.File

    val files_map = tools.map(t => (t, get_files_in_dir(f"$log_dir/$t")))
    val results = files_map.map({case (k, v) => parserMap(k).parseResFiles(v)})
    val results_map = results.flatten.map(oc => ((oc.fnameNoEnding, oc.tool), oc)).toMap
    results_map
  }

  def getBestFs(ocs: List[Option[FsOutcome]]): Option[FsOutcome] = {
    val best_fs = ocs.foldLeft(Option.empty[FsOutcome]){case (acc, x) =>
      minOpt_fs(acc, x)}
    best_fs
  }

  def getBestStatic(ocs: List[Option[StaticOutcome]]): Option[Outcome] = {
    val best = ocs.foldLeft(Option.empty[StaticOutcome]){case (acc, x) =>
      minOpt(acc, x)}
    best
  }

  def sortAlphaNumeric : String => (String, Option[Int]) = {
    val pattern = """^([a-zA-Z]+)(\d*)$""".r
    s => s match {
      case pattern(prefix, "")       => (prefix, None)
      case pattern(prefix, numStr)   => (prefix, Some(numStr.toInt))
      case other                     => (other, None)
    }
  }

  def calculate_speedups(log_dir: String) = {
    val tools = List("flostat", "flostat2", "flostat4", "flostat8", "satire", "satire_lo", "daisy", "daisy_fold", "paf")

    val results = tools.map{case t =>
      (t, parserMap(t).parseResFiles(get_files_in_dir(f"$log_dir/$t")))
    }

    def speedup(oc:Outcome) = oc.verTime.get_cpu_time / oc.verTime.real
    results.foreach{ case (t, t_res) =>
      val all_su = t_res.map(oc => (oc, speedup(oc)))
      val avg_su = all_su.map(_._2).sum / all_su.size
      val (max_oc, max_su) = all_su.maxBy{case (oc, su) => su}
      println(f"Average speedup for $t: ${avg_su}")
      println(f"Max speedup for $t: $max_su for file ${max_oc.fname} (vt: ${max_oc.verTime})")
    }

  }


  def alltools(log_dir: String) = {
    val remove_progs = List("lorenzloop100","lorenz30")
    val ADD_PAF_PAPER = false
    val fs_tools = List("flostat", "flostat2", "flostat4", "flostat8")
    val other_tools = List("satire", "satire_lo", "daisy", "daisy_fold")

    val tools = fs_tools ++ other_tools  ++ List("paf")
    val results_map = getAllResult(log_dir, tools)
    val all_fnames = results_map.values.map(_.fnameNoEnding).toSet.filterNot(f => remove_progs.contains(f))
    val pw = new PrintWriter(new File("latextable.txt"))

    all_fnames.toList.sortBy(sortAlphaNumeric).foreach{case fname =>
      val paf_server = results_map.get((fname, "paf"))
      val other_res = other_tools.map{ case t =>
          results_map.getOrElse((fname, t),
        StaticOutcome.dummy(fname))
      }
      if (fname == "lorenz100") {println(other_res)}
      val best_fs = getBestFs(fs_tools.map(t =>
        results_map.get((fname, t)).map(x => x.asInstanceOf[FsOutcome] )))

      pw.write(f"${fname}%s & ")
      pw.write(f"${opers_per_file(fname)}%d & ")
      pw.write(f"${best_fs.get.to_oopsla_string}%s &")

      val other_str = other_res.map{e => e.to_oopsla_string}
      pw.write(other_str.mkString("  &  "))

      if (ADD_PAF_PAPER && paf_server.flatMap(_.diff).isEmpty) {
        paf_paper_errors.get(fname) match {
          case Some(x) => pw.write(f" & (${Science_pp.science_pp(x)}) & n/a")
          case None => pw.write(" & n/a & n/a")
        }
      } else {
          val p = paf_server.getOrElse(StaticOutcome.dummy(fname))
          pw.write(f" & ${p.to_oopsla_string}")
      }
      // if (ADD_PAF_PAPER) pw.write(f" & ${paf_paper_errors.getOrElse(fname, "n/a")}")

      pw.write(f" \\\\ \n")
    }
    pw.close()
  }


  // def printBest(log_dir: String, tools: List[String]){
  //
  //   val results = getAllResult(log_dir, tools)
  //   val all_fnames: SortedSet[String] = results.values.map(_.fnameNoEnding).to[SortedSet]
  //
  //   val fsvsmax_opt = all_fnames.map {case fname =>
  //     val best_fs = getBestFs(fs_tools.map(t =>
  //       results_map.get((fname, t)).map(x => x.asInstanceOf[FsOutcome] )))
  //
  //     val experiments = tools.map(t => results.get((fname, t)))
  //
  //     val paf_paper: Option[Outcome] = paf_paper_errors.get(fname).map(StaticOutcome.fromDiff(fname, _, "paf_paper"))
  //     val all = experiments :+ paf_paper
  //
  //     val best = all.foldLeft(Option.empty[Outcome]){case (acc, x) => minOpt(acc, x)}
  //     println(f"Best for ${fname}: ${best}")
  //   }
  //
  // }
  def printScatterPlot(vals: List[(Option[Double], Option[Double])], plotfile: String) = {
    val pw = new PrintWriter(plotfile)
    vals.foreach{ case (x,y) => (x, y) match {
        case (Some(x_), Some(y_)) => {
          if (y_ < x_ ) println(f"x: $x_  y:$y_")
          pw.write(f"${x_}%.12f ${y_}%.12f a \n")
        }
        case _ => //skip
      }
    }
    pw.close()
  }

  def makeScatterPlots(log_dir: String) {
    val fs_tools = List("flostat", "flostat2", "flostat4", "flostat8")
    val static_tools = List("satire", "satire_lo", "daisy")
    val results = getAllResult(log_dir, fs_tools ++ static_tools)
    val all_fnames: SortedSet[String] = results.values.map(_.fnameNoEnding).to[SortedSet]

    val bests = all_fnames.to[List].map{ case fname =>
      val best_fs = getBestFs(fs_tools.map(t =>
        results.get((fname, t)).map(x => x.asInstanceOf[FsOutcome])))
      val static_best = getBestStatic(static_tools.map(t =>
        results.get((fname, t)).map(x => x.asInstanceOf[StaticOutcome])))
      val paf_paper = paf_paper_errors.get(fname)
      (best_fs.flatMap(_.diff), static_best.flatMap(_.diff), paf_paper)
    }
    def log2 = (x: Double) => log10(x)/log10(2.0)

    printScatterPlot(bests.map({case (fs, st, paf) => (fs, st)}),
      "scatter_static.txt")
    printScatterPlot(bests.map({case (fs, st, paf) => (fs, paf)}),
      "scatter_paf.txt")
  }

  def flostat_all_bounds(log_dir: String) = {
    val remove_progs = List("lorenzloop100","lorenz30")
    val tools = List("flostat", "flostat2", "flostat4", "flostat8")
    val results = getAllResult(log_dir, tools)
    val all_fnames: Set[String] = results.values.map(_.fnameNoEnding).toSet.filterNot(x => remove_progs.contains(x))

    val pw = new PrintWriter(new File("flostatallbounds.txt"))
    all_fnames.toList.sortBy(sortAlphaNumeric).foreach{case fname =>
      pw.write(f"${fname} & ")
      val res_str = tools.map(t => results((fname, t)).to_oopsla_string_notime)
      pw.write(res_str.mkString("  &  "))
      pw.write(f"\\\\ \n")
    }
    pw.close()

  }

  def nflostat_all_bounds(log_dir: String) = {
    val tools = List("nflostat", "nflostat2", "nflostat4", "nflostat8")
    val results = getAllResult(log_dir, tools)
    val all_fnames: Set[String] = results.values.map(_.fnameNoEnding).toSet

    val pw = new PrintWriter(new File("nflostatallbounds.txt"))
    all_fnames.toList.sortBy(sortAlphaNumeric).foreach{case fname =>
      pw.write(f"${fname} & ")
      val res_str = tools.map(t => results((fname, t)).to_oopsla_string_notime)
      pw.write(res_str.mkString("  &  "))
      pw.write(f"\\\\ \n")
    }
    pw.close()
  }

  def makevertimeboxplot(results: List[FsOutcome], outfile : String = "boxplot.txt") = {
    val pw = new PrintWriter(outfile)
     val boxplots = results.sortBy(_.prec).groupBy(_.prec).toList.sortBy(
       _._1).map( {case (p, x) => new BoxPlotData(x.map(_.verTime.get_cpu_time), p.toString)})
     boxplots.foreach{x => pw.write(x.toPgfPlotsFormatBoxPlot(outfile))}
     pw.close()
  }

  def makevertimelineplot(results: List[FsOutcome], outfile : String = "boxplot.txt") = {
    val pw = new PrintWriter(outfile)
     val boxplots = results.sortBy(_.prec).groupBy(_.prec).toList.sortBy(
       _._1).map( {case (p, x) => new BoxPlotData(x.map(_.verTime.get_cpu_time), p.toString)})
    val coords = boxplots.zipWithIndex.map{case (x,i) => f"(${i}, ${x.median})"}.mkString(" ")
   val plot_str = f"""
\\addplot[line_case_study]
  coordinates {
    ${coords}
  };
  %%%%%%%%%%%%%%%%%%%%
"""
  pw.write(plot_str)
     pw.close()
  }

  def compareprecicions(results: List[FsOutcome], fname: String) = {
    println(f"#### Comparing for file $fname \n ############ \n\n")
    results.sortBy(_.fname).groupBy(_.fname).map(_._2).map{
      (o: List[FsOutcome]) =>
        val pairs = o.flatMap(x => o.map(y => (x, y)))
        pairs.foreach(x => if (x._1.isSuccess != x._2.isSuccess) {
          println(f"""differ detected for file ${x._1.fname} between prec
                ${x._1.prec} and ${x._2.prec}.
                ${x._1.prec} measured prob to ${x._1.meas_prob}.
                ${x._2.prec} measured prob to ${x._2.meas_prob}.
          """)}
      )
    }
    println(f"#### Done with file $fname ############ \n")
  }
  def do_all_precs_test(log_dir: String, fname: String) = {
    val results = FloStatParser(Some("flostat")).parseResFile(f"$log_dir/$fname").asInstanceOf[List[FsOutcome]]
    //makevertimeboxplot(results, f"boxplot_$fname")
    makevertimelineplot(results, f"lineplot_$fname")
    compareprecicions(results, fname)
  }

  def computeHistogram(fileName: String, numBins: Int, outfile: String = "histogram.txt") = {

     val lines = Source.fromFile(fileName).getLines().toSeq
     require(lines.nonEmpty, f"File $fileName is empty.")

     val header = lines.head.split("[,;\\s]+").map(_.trim)
     val diffIndex = header.indexOf("diff")
     require(diffIndex >= 0, f"No column named 'diff' found in $fileName")

     // Read the "diff" column values
     val data = lines.tail.flatMap { line =>
       val cols = line.split("[,;\\s]+").map(_.trim)
       if (diffIndex < cols.length && cols(diffIndex).nonEmpty)
         Some(cols(diffIndex).toDouble)
       else None
     }

     require(data.nonEmpty, f"No valid numeric data found in column 'diff' of $fileName")

     val min = data.min
     val max = data.max
     val binWidth = (max - min) / numBins
     val bins = Array.fill(numBins)(0)

     // Bin the data
     data.foreach { x =>
       val idx = ((x - min) / binWidth).toInt match {
         case i if i >= numBins => numBins - 1
         case i if i < 0        => 0
         case i                 => i
       }
       bins(idx) += 1
     }


         // --- Write output (bin_start, count) ---
    val pw = new PrintWriter(outfile)
    for (i <- bins.indices) {
      val binStart = min + i * binWidth
      pw.println(f"$binStart%g ${bins(i)}")
    }
    pw.close()

    println(s"Histogram written to $outfile with $numBins bins.")
    // Return (binStart, count)
  }

  def lorenz_line_plot(log_dir: String, fnames: List[String] = List("lorenz2",
          "lorenz4", "lorenz5", "lorenz8", "lorenz10", "lorenz20", "lorenz40",
          "lorenz70", "lorenz100", "lorenz200", "lorenz400", "lorenz700",
          "lorenz1000")) = {

    val pw = new PrintWriter("lorenz_line_plot.txt")
    val fs_tools = List("flostat", "flostat2", "flostat4", "flostat8")
    val results = getAllResult(log_dir, fs_tools).filter{case (_, x) => fnames.contains(x.fnameNoEnding)}
    val all_fnames: SortedSet[String] = results.values.map(_.fnameNoEnding).to[SortedSet]

    all_fnames.to[List].sortBy(sortAlphaNumeric).foreach{ case fname =>
      val best_fs = getBestFs(fs_tools.map(t =>
        results.get((fname, t)).map(x => x.asInstanceOf[FsOutcome])))
      val (first, second) = fname.span(_.isLetter)
      val iters = second.toInt
      println(s"first = $first, second = $iters")

      pw.write(f"($iters, ${best_fs.get.diff.get})\n")
    }
    pw.close()

  }

  def executions_line_plot(log_dir: String) = {

    val pw = new PrintWriter("execs_line_plot.txt")
    val results = FloStatParser(Some("flostat")).parseResFile(f"$log_dir/execs_flostat/results_execs.txt").asInstanceOf[List[FsOutcome]]
    println(results)
    results.foreach{ case res =>
      pw.write(f"(${res.execs}, ${res.conf})\n"),
    }
    pw.close()

  }



  def lorenz_dists(log_dir: String) = {
    val dist_par = Map(
      "lorenz100aN00625.c" -> ("Normal", 0.0625),
      "lorenz100bN0125.c" -> ("Normal", 0.125),
      "lorenz100cN025.c" -> ("Normal", 0.25),
      "lorenz100dN05.c" -> ("Normal", 0.5),
      "lorenz100eN1.c" -> ("Normal", 1.0),
      "lorenz100fN2.c" -> ("Normal", 2.0),
      "lorenz100gN4.c" -> ("Normal", 4.0),
      "lorenz100Ua125.c" -> ("Uniform", 0.125),
      "lorenz100Ub025.c" -> ("Uniform", 0.25),
      "lorenz100Uc05.c" -> ("Uniform", 0.5),
      "lorenz100Ud1.c" -> ("Uniform", 1.0),
      "lorenz100Ue2.c" -> ("Uniform", 2.0),
      "lorenz100Uf4.c" -> ("Uniform", 4.0),
    )
    val pw = new PrintWriter("lorenz_dists.txt")
    val results = FloStatParser(Some("flostat")).parseResFile(f"$log_dir/lorenz_dists/flostat_results.txt").asInstanceOf[List[FsOutcome]]
    println(results)
    results.to[List].sortBy(_.fname).foreach{ case res =>
      dist_par(res.fname) match {
        case ("Normal", sigma) => (0.0, sigma)
        pw.write(f" $$ N(0.0, ${sigma})$$ & ${res.meas_prob} & ${res.conf} \\\\  \n")
        case ("Uniform", x) =>
        pw.write(f"$$ U(${-x}, ${x}) $$ & ${res.meas_prob} & ${res.conf} & \n")
      }
    }
    pw.close()
  }

  def checkSeeds(log_dir: String) = {
    val fs_tools = List("flostat", "flostat2", "flostat4", "flostat8")

    val seeds = List.range(1,11)
    val tool_seeds = for {t <- fs_tools; s <- seeds} yield (t, s)


    val res_map = scala.collection.mutable.Map[(String, String), List[(Int, FsOutcome)]]()
    tool_seeds.foreach{case (t, s) =>
      val fname = f"${log_dir}/seeds/${t}/${t}_seed${s}_results.txt"
      val results = parserMap(t).parseResFile(fname).filter(_.fname != "lorenzloop100.c")
      results.foreach{ case oc =>
        val rlist = res_map.getOrElse((t, oc.fname), List())
        res_map.put((t, oc.fname), (s, oc.asInstanceOf[FsOutcome]) :: rlist)
      }
    }
    val maxViols_list = res_map.map{case ((t, f), rlist) =>
      val max = rlist.maxBy{case (s, oc) => oc.viols}
      val min = rlist.minBy{case (s, oc) => oc.viols}
      (max,min)
    }
    val maxConfs_list = res_map.map{case ((t, f), rlist) =>
      val max = rlist.maxBy{case (s, oc) => oc.conf}
      val min = rlist.minBy{case (s, oc) => oc.conf}
      (max,min)
    }
    val maxProbs_list = res_map.map{case ((t, f), rlist) =>
      val max = rlist.maxBy{case (s, oc) => oc.meas_prob}
      val min = rlist.minBy{case (s, oc) => oc.meas_prob}
      (max,min)
    }
    val confMax = maxConfs_list.maxBy{case (a,b) => a._2.conf - b._2.conf}
    val probMax = maxProbs_list.maxBy{case (a,b) => a._2.meas_prob - b._2.meas_prob}
    val violsMax = maxViols_list.maxBy{case (a,b) => a._2.viols - b._2.viols}
    println(f"total max conf diff: ${confMax}")
    println(f"total max prob diff: ${probMax}")
    println(f"total max viols diff: ${violsMax}")
    // res_map.map{case ((t, f), (s, oc)) => }
    val verProbMax = maxProbs_list.filter{case (a,b) => a._2.conf <= 0.001 && a._2.conf >= 0.0 && b._2.conf <= 0.001 && b._2.conf >= 0.0}.
      maxBy{case (a,b) => a._2.meas_prob - b._2.meas_prob}
    val verConfMax = maxConfs_list.filter{case (a,b) => a._2.conf <= 0.001 && a._2.conf >= 0.0 && b._2.conf <= 0.001 && b._2.conf >= 0.0}.
      maxBy{case (a,b) => (a._2.conf - b._2.conf)/(b._2.conf + (a._2.conf - b._2.conf)/2)}
    println(verProbMax)
    println(verConfMax)
  }

  def main(args: Array[String]): Unit = {
    val log_dir = "oopsla_results"
    // val f = Source.fromFile("args[1]")
    println("starting main")
    //
    // print(DaisyParser(Some("df")).parseResFile("oopsla_results/daisy_fold/daisy_fold_results.txt"))
    // do_all_precs_test(log_dir + "/compare_precs", "case_study.txt")
    // do_all_precs_test(log_dir + "/compare_precs", "lorenz4_results.txt")
    // do_all_precs_test(log_dir + "/compare_precs", "lorenz10_results.txt")
    // do_all_precs_test(log_dir + "/compare_precs", "lorenz100_results.txt")
    // do_all_precs_test(log_dir + "/compare_precs", "lorenz1000_results.txt")
    // print(DaisyParser.parseResFile("oopsla_results/daisy_fold/daisy_fold_results.txt"))


    // // Full table with all tools
    alltools(log_dir)
    // calculate_speedups(log_dir)
    // // //
    // flostat_all_bounds(log_dir)
    //
    // lorenz_line_plot(log_dir)

    // executions_line_plot(log_dir)
    // nflostat_all_bounds(log_dir)
    // lorenz_dists(log_dir)

    // checkSeeds(log_dir)
    // // // // printBest(log_dir, List("daisy", "paf", "satire", "satire_lo"))
    // //
    // // makeScatterPlots(log_dir)
    // // print(PafParser.parseResFile("oopsla_results/paf/paf_results1.txt"))
    // computeHistogram(
    //   "oopsla_results/histogram/small_torque_2025-10-09_09-02-08/diff.csv",
    //   100,
    //   "small_torque_histogram.txt"
    // )
  }
}
