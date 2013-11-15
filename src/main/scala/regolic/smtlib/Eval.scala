package regolic
package smtlib

import parsers.SmtLib2._
import parsers.SmtLib2.Trees._
import sexpr.SExprs._

import dpllt.TheorySolver
import dpllt.Solver.Results._
import smt.qfeuf._


import asts.core.Manip._
import asts.core.Trees._
import asts.fol.Trees._
import asts.fol.Manip._

object Eval {

  object SolverFactory {
    def apply(logic: Logic) = {
      logic match {
        case QF_UF => Some(new FastCongruenceClosure)
        case _ => {
          println("Logic not supported.")
          None
        }
      }
    }
  }

  def execute(cmds: List[Command]): Unit = {
    //var solver: Option[TheorySolver] = None
    var solver: Option[FastCongruenceClosure] = None
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
            val formula: Formula = simplify(asserts.foldLeft(True(): Formula)((acc, f) => And(acc, f)))
            val currified: Formula = mapPreorder(formula, f => f, t => Currifier(t))
            val (flattened, eqs) = Flattener.transform(currified)
            println("flatten: " + flattened)
            println("eqs: " + eqs)

            //val result = DPLLTSolverWrapper(solver.get, formula)


            //val resultString = result match {
            //  case Satisfiable(_) if expectedResult == Some(false) => "sat | should be unsat"
            //  case Satisfiable(_) => "sat"
            //  case Unsatisfiable if expectedResult == Some(true) => "unsat | should be sat"
            //  case Unsatisfiable => "unsat"
            //}
            //println(resultString)
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
