package regolic

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import java.io.File

object Main {

  private var dimacs = true
  private var smtlib2 = true

  private val optionsHelp: String = (
    "  --dimacs             The input file is to be interpreted as a DIMACS CNF SAT problem" + "\n" +
    "  --smtlib2            The input file is to be interpreted as an SMT problem in SMTLIB version 2 format" + "\n" +
    "  --debug=[1-5]        Debug level" + "\n" +
    "  --tags=t1:...        Filter out debug information that are not of one of the given tags" + "\n" +
    "  --timeout=N          Timeout in seconds" + "\n" +
    "  --stats              Print statistics information"
  )

  def processOptions(options: Array[String]) {
    for(option <- options) {
      option match {
        case "dimacs"        =>                     dimacs = true
        case "smtlib2"        =>                    smtlib2 = true

        case "stats"         =>                     Settings.stats = true

        case s if s.startsWith("debug=") =>         Settings.debugLevel = try { 
                                                      s.substring("debug=".length, s.length).toInt 
                                                    } catch { 
                                                      case _ => 0 
                                                    }
        case s if s.startsWith("tags=") =>          Settings.debugTags = Set(splitList(s.substring("tags=".length, s.length)): _*)
        case s if s.startsWith("timeout=") =>       Settings.timeout = try { 
                                                      Some(s.substring("timeout=".length, s.length).toInt)
                                                    } catch { 
                                                      case _ => None
                                                    }
        case _ => Reporter.error("Invalid option: " + option + "\nValid options are:\n" + optionsHelp)
      }
    }
  }

  def main(arguments: Array[String]) {
    val cmd = arguments(0)
    val args = arguments.tail
    try {
      val (options0, trueArgs) = args.partition(str => str.startsWith("--"))
      val options = options0.map(str => str.substring(2))
      processOptions(options)
      val inputFile = trueArgs(0)
      val is = new java.io.FileInputStream(inputFile)

      if(cmd == "sat") {
        val (satInstance, nbVars) = regolic.parsers.Dimacs.cnf(is)
        val res = regolic.sat.DPLL.isSat(satInstance, nbVars)
        res match {
          case Some(_) => println("sat")
          case None => println("unsat")
        }
      } else if(cmd == "smt") {
        val smtInstance = regolic.parsers.SmtLib2(is)
        regolic.smt.Solver.execute(smtInstance)
      }
    } catch {
      case e =>
        e.printStackTrace
        sys.exit(1)
    }
  }

  private def splitList(lst: String) : Seq[String] = lst.split(':').map(_.trim).filter(!_.isEmpty)

  private def recursiveListFiles(f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter(_.isDirectory).flatMap(recursiveListFiles)
  }
}
