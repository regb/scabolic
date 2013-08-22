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

trait TheorySolver {

  val logic: Logic
    
  def initialize(ls: Set[Formula]): Unit

  def isTrue(l: Formula): Boolean

  def backtrack(n: Int): Unit

  def explain(l: Formula): Set[Formula]

  def setTrue(l: Formula): Option[Set[Formula]]
  
}

object TheorySolver {

  val allSolvers: List[TheorySolver] = List() // TODO wrapper object for congruence closure

  def execute(cmds: List[Command]) {
    println("Executing following script: " + cmds)
    var solver: Option[TheorySolver] = None
    var asserts: List[Formula] = List(True())

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
          //println("isSat: "+ FastCongruenceSolver.isSat(formula))
          val cc = new CongruenceClosure
          //println("isSat: " + DPLLTSolverWrapper(solver.get, formula))
          println("isSat: " + DPLLTSolverWrapper(cc, formula))
        }
        case Exit => {
          // TODO
        }
      }
    }

  }


  def getSolver(logic: Logic): Option[TheorySolver] = allSolvers.find(_.logic == logic)

}
