import scala.util.parsing.combinator._
import scala.io.Source
import scala.math.log10

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
  def toPgfPlotsFormat: String = {
    f"""
    %%$info%s
    %%$length%d
    \\addplot[
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

class Outcome(val fname: String, val prec: Int, val meas_prob: Double,
  val spec_prob: Double, val conf:Double, val vertime:Double) {

    override def toString = {
      "%s, %d, %g, %g, %g, %g".format(fname, prec, meas_prob, spec_prob, conf,
        vertime)
    }
    def isSuccess = conf != -1.0

}

class SimpleParser extends RegexParsers {
  def skipLine = "(.*\n)".r
  def word: Parser[String]    = """[a-z]+""".r
  def filename: Parser[String] = """[a-z0-9A-Z_]+\.c""".r
  def filestart: Parser[String] = """Running file: """ ~> filename
  def fileend(l: String): Parser[String] = (".*Done with file: " + l).r ^^ (_ => l)
  def integer: Parser[Int] = "[0-9]+".r ^^ { _.toInt }
  def number: Parser[Double] = "[0-9]+((\\.[0-9]+)?(e-[0-9]+)?)?".r ^^ { _.toDouble }
  def diff: Parser[Double] = ".*diff: ".r ~> number
  def prob: Parser[Double] = ".*Measured probability: ".r ~> number <~ ".*".r
  def conf: Parser[Double] = ".*Measured conf level: ".r ~> number <~ ".*".r
  def probbad: Parser[String] = ".*The measured probability is smaller than the specified.*".r
  def failorsucc: Parser[Boolean] = (".*(Failure|Success).*".r) ^^
    {s => if (s matches ".*Success.*") true else false}
  def failorconf: Parser[Double] = failorsucc >>
    {case true => (rep(not(conf) ~> ".*".r) ~> conf) ^^ {c => c}
     case false => probbad ^^{_=> -(1.0) }
   }
  def verTime: Parser[Double] = "Done with .* executions of file .* in".r ~> number <~ "s".r
  def prec: Parser[Int] = ".*-fs-prec ".r ~> integer <~ ".*".r
  def file: Parser[Outcome] =
    rep(not(filestart) ~> ".*\n".r) ~> filestart ~
      (rep(not(prec) ~> ".*".r) ~> prec) ~
      (rep(not(diff) ~> ".*".r) ~> diff) ~
      failorconf ~
      (rep(not(prob) ~> ".*".r) ~> prob) ~
      (rep(not(verTime) ~> ".*".r) ~> verTime) >>
        {case fs ~ prec ~ d ~ fc ~ p ~ vt =>
          rep(not(fileend(fs)) ~> ".*".r) ~>
          (fileend(fs) ^^ (es => new Outcome(es, prec, p, d, fc, vt)))}
}

object TestSimpleParser extends SimpleParser {
  def makefulltable(results: TestSimpleParser.ParseResult[List[Outcome]]) = {
    results.get.foreach(x => print(x.fname + "&" +
      ("$%s$".format(x.prec)) + "&" +
      "$%s$".format(x.spec_prob) + "&" +
      "$%s$".format(x.meas_prob)  + "&" +
      "%s".format(x.conf)  + "&" +
      "%s".format(x.vertime) + "\n"))
  }
  def makevertimeboxplot(results: TestSimpleParser.ParseResult[List[Outcome]]) = {
    val boxplots = results.get.sortBy(_.prec).groupBy(_.prec).toList.sortBy(
      _._1).map( {case (p, x) => new BoxPlotData(x.map(_.vertime), p.toString)})
    print(boxplots.map(_.toPgfPlotsFormat))
  }

  def compareprecicions(results: TestSimpleParser.ParseResult[List[Outcome]]) = {
    results.get.sortBy(_.fname).groupBy(_.fname).map(_._2).map{
      (o: List[Outcome]) =>
        val pairs = o.flatMap(x => o.map(y => (x, y)))
        pairs.foreach(x => if (x._1.isSuccess != x._2.isSuccess) {print(
          ("""differ detected for file %s between prec
                %d and %d.
                %d measured prob to %f.
                %d measured prob to %f.
          """).format(x._1.fname, x._1.prec, x._2.prec, x._1.prec, x._1.meas_prob, x._2.prec, x._2.meas_prob)
          )}
      )
    }
    print("Done")
  }

  def main(args: Array[String]) = {
    // val f = Source.fromFile("args[1]")
    val input = scala.io.Source.fromInputStream(System.in).mkString
    print(input)
    val results = parse(rep(file), input)
    // makefulltable(results)
    // makevertimeboxplot(results)
    compareprecicions(results)
  }
}
