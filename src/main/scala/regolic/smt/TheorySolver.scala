package regolic.smt

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._
import regolic.parsers.SmtLib2.Trees._

import regolic.smt.qfeuf.CongruenceClosure

import regolic.dpllt.DPLLTSolverWrapper
import regolic.dpllt.Results._

import regolic.sexpr.SExprs._

import scala.collection.mutable.Stack

// Interface similar to the one described in "DPLL(T): Fast Decision Procedures"
// by Ganzinger, Hagen, Nieuwenhuis, Oliveras, Tinelli
trait TheorySolver {

  def initialize(ls: Set[Formula]): Unit

  def isTrue(l: Formula): Boolean

  def backtrack(n: Int): Unit

  def backtrackTo(l: Formula): Unit

  def explain(): Set[Formula]

  def explain(l: Formula, lPrime: Formula = null): Set[Formula]

  def setTrue(l: Formula): Option[Set[Formula]]
  
  var time: Double
}

object TheorySolver {

  object SolverFactory {
    import regolic.parsers.SmtLib2.Trees._
    def apply(logic: Logic) = {
      logic match {
        case QF_UF => Some(new CongruenceClosure)
        case _ => {
          println("Logic not supported.")
          None
        }
      }
    }
  }

  def execute(cmds: List[Command]) {
    var solver: Option[TheorySolver] = None
    var asserts: List[Formula] = List(True())

    var expectedResult: Option[Boolean] = None

    for(cmd <- cmds) {
      cmd match {
        case SetLogic(logic) => solver = SolverFactory(logic)
        case Pop(n) => {
          asserts = asserts.tail
        }
        case Push(n) => {
          asserts ::= True()
        }
        case Assert(f) => {
          asserts = And(f, asserts.head) :: asserts.tail
        }
        case CheckSat => {
          if(solver != None) {
            val formula = simplify(asserts.foldLeft(True(): Formula)((acc, f) => And(acc, f)))
            val result = DPLLTSolverWrapper(solver.get, formula)

            val resultString = result match {
              case Satisfiable(_) if expectedResult == Some(false) => "sat | should be unsat"
              case Satisfiable(_) => "sat"
              case Unsatisfiable if expectedResult == Some(true) => "unsat | should be sat"
              case Unsatisfiable => "unsat"
            }
            println(resultString)
          } else println("Solver not set.")
        }
        case SetInfo(attr) => {
          attr match {
            case Attribute("STATUS", Some(SSymbol("SAT"))) => expectedResult = Some(true)
            case Attribute("STATUS", Some(SSymbol("UNSAT"))) => expectedResult = Some(false)
            case Attribute("STATUS", _) => {
              println("WARNING: set-info status set to unsupported value")
              expectedResult = None
            }
            // TODO
            case Attribute("SOURCE", Some(SSymbol(src))) => ()
            case Attribute("SMT-LIB-VERSION", Some(SDouble(ver))) => ()
            case Attribute("CATEGORY", Some(SString(cat))) => ()
            case _ => println("WARNING: unsupported set-info attribute")
          }
        }
        case Exit => {
          sys.exit()
        }
      }
    }

  }

}
