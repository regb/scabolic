package regolic

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import java.io.File

object Scheduler {
  import java.util.concurrent.Executors
  import scala.compat.Platform
  import java.util.concurrent.TimeUnit

  private lazy val sched = Executors.newSingleThreadScheduledExecutor();
  def schedule(f: => Unit, time: Long) {
    sched.schedule(new Runnable {
      def run = f
    }, time , TimeUnit.MILLISECONDS)
  }
}

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
    "  --time               Time the solving phase"
  )

  def processOptions(options: Array[String]) {
    for(option <- options) {
      option match {
        case "dimacs"        =>                     dimacs = true
        case "smtlib2"        =>                    smtlib2 = true
        case "time"        =>                       time = true

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

  def satSolver(f: File) {
    Settings.timeout match {
      case Some(secs) => Scheduler.schedule(sys.exit(42), 1000*secs)
      case None =>
    }
    val is = new java.io.FileInputStream(f)
    val (satInstance, nbVars) = regolic.parsers.Dimacs.cnf(is)
    val res = regolic.sat.DPLL.isSat(satInstance, nbVars)
    res match {
      case Some(_) => println("sat")
      case None => println("unsat")
    }
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
          println(elapsed/1000.)
        sys.exit(0)
      } else if(cmd == "smt") {
        val inputFile = trueArgs(0)
        val is = new java.io.FileInputStream(inputFile)
        val smtInstance = regolic.parsers.SmtLib2(is)
        regolic.smt.Solver.execute(smtInstance)
      } else if(cmd == "satlib") {
        val dir = trueArgs(0)
        val dirFile = new java.io.File(dir)
        val benchmarks = recursiveListFiles(dirFile)

        //letting some time to hotspot
        val benchmark = benchmarks.head
        (1 to 3).foreach{_ => satSolver(benchmark)}

        val start = System.currentTimeMillis
        benchmarks.foreach(file => {
          print("Solving " + file + " ... ")
          satSolver(file)
        })
        val end = System.currentTimeMillis
        val elapsed = end - start
        println("Total solving time: " + (elapsed/1000.))
      } else {
        println("Unknown command: " + cmd)
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
