package regolic.smt

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._
import regolic.parsers.SmtLib2.Trees._

import regolic.smt.qfeuf.CongruenceSolver
import regolic.smt.qfeuf.FastCongruenceSolver
import regolic.smt.qflra.SimplexSolver

import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer

import regolic.dpllt.LazyBasicSolver

trait Solver {

  val logic: Logic
  
  /*
   * Return a pair containing the answer (true / false) and if unsat a Map from
   * each inequality causing it, to the explanation
   */
  def isSat(f: Formula): Pair[Boolean, Option[Map[Formula, List[Formula]]]]

  def isValid(f: Formula): Boolean = isSat(Not(f))._1 == false
  
  //def findCounterample(f: Formula): Option[Map[FunctionSymbol, Term]] = isSat(Not(f))

}

object Solver {

  val allSolvers: List[Solver] = List(FastCongruenceSolver, SimplexSolver, regolic.smt.qfa.Solver)

  def execute(cmds: List[Command]) {
    println("Executing following script: " + cmds)
    var solver: Option[Solver] = None
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
          //println("isSat: " + solver.get.isSat(formula))
          println("isSat: " + LazyBasicSolver.solve(solver.get, formula))
        }
        case Exit => {
          // TODO
        }
      }
    }

  }


  def getSolver(logic: Logic): Option[Solver] = allSolvers.find(_.logic == logic)

}
