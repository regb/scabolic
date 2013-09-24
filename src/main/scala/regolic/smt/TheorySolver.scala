package regolic.smt

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._
import regolic.parsers.SmtLib2.Trees._

import regolic.smt.qfeuf.CongruenceSolver
import regolic.smt.qfeuf.CongruenceClosure
import regolic.smt.qfeuf.FastCongruenceSolver
import regolic.smt.qflra.SimplexSolver

import regolic.dpllt.LazyBasicSolver
import regolic.dpllt.DPLLTSolverWrapper
import regolic.dpllt.Results._

import regolic.sexpr.SExprs._

trait TheorySolver {

  val logic: Logic
    
  def initialize(ls: Set[Formula]): Unit

  def isTrue(l: Formula): Boolean

  def backtrack(n: Int): Unit

  def backtrackTo(l: Formula): Unit

  def explain(l: Formula, lPrime: Formula = null): Set[Formula]

  def setTrue(l: Formula): Option[Set[Formula]]
  
  val iStack: collection.mutable.Stack[Pair[Int, Formula]]

  var reason: Formula
}

object TheorySolver {

  val allSolvers: List[TheorySolver] = List() // TODO wrapper object for congruence closure

  def execute(cmds: List[Command]) {
    var solver: Option[TheorySolver] = None
    var asserts: List[Formula] = List(True())

    var expectedResult: Option[Boolean] = None

    for(cmd <- cmds) {
      cmd match {
        case SetLogic(logic) => solver = getSolver(logic)
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
          val formula = simplify(asserts.foldLeft(True(): Formula)((acc, f) => And(acc, f)))
          val cc = new CongruenceClosure
          val result = DPLLTSolverWrapper(cc, formula)

          val resultString = result match {
            case Satisfiable(_) if expectedResult == Some(false) => "sat | should be unsat"
            case Satisfiable(_) => "sat"
            case Unsatisfiable if expectedResult == Some(true) => "unsat | should be sat"
            case Unsatisfiable => "unsat"
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
          // TODO
          sys.exit()
        }
      }
    }

  }


  def getSolver(logic: Logic): Option[TheorySolver] = allSolvers.find(_.logic == logic)

}
