package regolic

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import java.io.File

object Main {

  private var dimacs = true
  private var smtlib2 = true
  private var time = false

  private val optionsHelp: String = (
    "  --dimacs             The input file is to be interpreted as a DIMACS CNF SAT problem" + "\n" +
    "  --smtlib2            The input file is to be interpreted as an SMT problem in SMTLIB version 2 format" + "\n" +
    "  --debug=[1-5]        Debug level" + "\n" +
    "  --tags=t1:...        Filter out debug information that are not of one of the given tags" + "\n" +
    "  --timeout=N          Timeout in seconds" + "\n" +
    "  --stats              Print statistics information" +
    "  --restartfactor=N    Restart strategy factor" + "\n" +
    "  --restartinterval=N  Restart strategy initial interval" + "\n" +
    "  --time               Time the solving phase"
  )

  def processOptions(options: Array[String]) {
    for(option <- options) {
      option match {
        case "dimacs"        =>                           dimacs = true
        case "smtlib2"        =>                          smtlib2 = true
        case "time"        =>                             time = true

        case "stats"         =>                           Settings.stats = true

        case s if s.startsWith("debug=") =>               Settings.debugLevel = try { 
                                                            s.substring("debug=".length, s.length).toInt 
                                                          } catch { 
                                                            case _ => 0 
                                                          }
        case s if s.startsWith("tags=") =>                Settings.debugTags = Set(splitList(s.substring("tags=".length, s.length)): _*)
        case s if s.startsWith("timeout=") =>             Settings.timeout = try { 
                                                            Some(s.substring("timeout=".length, s.length).toInt)
                                                          } catch { 
                                                            case (_: Throwable) => None
                                                          }
        case s if s.startsWith("restartinterval=") =>     try { 
                                                            Settings.restartInterval = s.substring("restartInterval=".length, s.length).toInt
                                                          } catch { 
                                                            case (_: Throwable) =>
                                                          }
        case s if s.startsWith("restartfactor=") =>       try { 
                                                            Settings.restartFactor = s.substring("restartFactor=".length, s.length).toDouble
                                                          } catch { 
                                                            case (_: Throwable) =>
                                                          }
        case _ => Reporter.error("Invalid option: " + option + "\nValid options are:\n" + optionsHelp)
      }
    }
  }

  import regolic.sat.Solver
  import Solver.Results._

  def satSolver(f: File) = {


    val is = new java.io.FileInputStream(f)
    val (satInstance, nbVars) = regolic.parsers.Dimacs.cnf(is)
    val s = new Solver(nbVars)
    satInstance.foreach(s.addClause(_))
    val res = s.solve()
    res match {
      case Satisfiable(_) => println("sat")
      case Unsatisfiable => println("unsat")
      case Unknown => println("unknown")
    }
    res
  }

  def main(arguments: Array[String]) {
    val cmd = arguments(0)
    val args = arguments.tail
    try {
      val (options0, trueArgs) = args.partition(str => str.startsWith("--"))
      val options = options0.map(str => str.substring(2))
      processOptions(options)

      if(cmd == "sat") {
        val inputFile = trueArgs(0)
        val start = System.currentTimeMillis
        satSolver(new java.io.File(inputFile))
        val end = System.currentTimeMillis
        val elapsed = end - start
        if(time)
          println(elapsed/1000d)
        sys.exit(0)
      } else if(cmd == "smt") {
        val inputFile = trueArgs(0)
        val is = new java.io.FileReader(inputFile)
        val smtInstance = regolic.parsers.SmtLib2(is)
        //println(smtInstance)
        regolic.smt.Solver.execute(smtInstance)
      } else if(cmd == "satlib") {
        val dir = trueArgs(0)
        val dirFile = new java.io.File(dir)
        val benchmarks = recursiveListFiles(dirFile)

        //jvm's warmup
        val benchmark = benchmarks.head
        (1 to 3).foreach{_ => satSolver(benchmark)}

        val start = System.currentTimeMillis
        var nbTimeout = 0
        benchmarks.foreach(file => {
          print("Solving " + file + " ... ")
          val res = satSolver(file)
          if(res == Unknown)
            nbTimeout += 1
        })
        val end = System.currentTimeMillis
        val elapsed = (end - start) - (Settings.timeout.getOrElse(0)*1000d*nbTimeout)
        println("Number of timeout: " + nbTimeout)
        println("Total solving time (w/o Timeouts): " + (elapsed/1000d))
        println("Average solving time (w/o Timeouts): " + (elapsed/1000d)/(benchmarks.size - nbTimeout))
      } else {
        println("Unknown command: " + cmd)
      }
    } catch {
      case (e: Throwable) =>
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
