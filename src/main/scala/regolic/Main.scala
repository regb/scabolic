package regolic

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

object Main {

  private var dimacs = false
  private var smtlib = false
  private var smtlib2 = false

  private val optionsHelp: String = (
    "  --dimacs             The input file is to be interpreted as a DIMACS CNF SAT problem" + "\n" +
    "  --smtlib             The input file is to be interpreted as an SMT problem in SMTLIB version 1 format" + "\n" +
    "  --smtlib2            The input file is to be interpreted as an SMT problem in SMTLIB version 2 format" + "\n" +
    "  --debug=[1-5]        Debug level" + "\n" +
    "  --tags=t1:...        Filter out debug information that are not of one of the given tags" 
  )

  def processOptions(options: Array[String]) {
    for(option <- options) {
      option match {
        case "dimacs"        =>                     dimacs = true
        case "smtlib"        =>                     smtlib = true
        case "smtlib2"       =>                     smtlib2 = true

        case s if s.startsWith("debug=") =>         Settings.debugLevel = try { 
                                                      s.substring("debug=".length, s.length).toInt 
                                                    } catch { 
                                                      case _ => 0 
                                                    }
        case s if s.startsWith("tags=") =>          Settings.debugTags = Set(splitList(s.substring("tags=".length, s.length)): _*)
        case _ => Reporter.error("Invalid option: " + option + "\nValid options are:\n" + optionsHelp)
      }
    }
  }

  def main(args: Array[String]) {
    val (options0, trueArgs) = args.partition(str => str.startsWith("--"))
    val options = options0.map(str => str.substring(2))
    processOptions(options)
    val inputFile = trueArgs(0)
    val is = new java.io.FileInputStream(inputFile)

    if(dimacs) {
      val satInstance: List[Formula] = regolic.parsers.Dimacs(is)
      val res = regolic.sat.DPLL.isSat(satInstance)
      println(res)
    }

  }

  private def splitList(lst: String) : Seq[String] = lst.split(':').map(_.trim).filter(!_.isEmpty)

}
