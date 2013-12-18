package regolic
package smtlib

import parsers.SmtLib2._
import parsers.SmtLib2.Trees._
import sexpr.SExprs._

import dpllt._
import DPLLSolver.Results._

import util._

import asts.core.Manip._
import asts.core.Trees._
import asts.fol.Trees._
import asts.fol.Manip._

import scala.collection.mutable.HashMap

/*
 * We assume symbols declaration are valid at the top level and are not scope (stack/frame) specific
 * (Even Z3 is not supporting that)
 */
object Eval {

  //object SolverFactory {
  //  def apply(logic: Logic) = {
  //    logic match {
  //      case QF_UF => Some(new FastCongruenceClosure)
  //      case _ => {
  //        println("Logic not supported.")
  //        None
  //      }
  //    }
  //  }
  //}

  //def execute(cmds: List[Command])(implicit context: Context): Unit = ???
  def execute(cmds: List[Command])(implicit context: Context): Unit = {
    val solver = new cafesat.Solver
    var expectedResult: Option[Boolean] = None

    for(cmd <- cmds) {
      cmd match {
        case SetLogic(logic) => () //solver = SolverFactory(logic)
        case Pop(n) => {
          solver.pop(n)
        }
        case Push(n) => {
          (1 to n).foreach(_ => solver.push())
        }
        case Assert(f) => {
          solver.assertCnstr(f)
        }
        case CheckSat => {
          val result = solver.check()
          val resultString = result match {
            case Some(true) => {
              if(expectedResult == Some(false))
                "sat | should be unsat"
              else
                "sat"
            }           
            case Some(false) if expectedResult == Some(true) => "unsat | should be sat"
            case Some(false) => "unsat"
            case None => "unknown"
          }
          println(resultString)
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
