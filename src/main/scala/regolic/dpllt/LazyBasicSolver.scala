package regolic.dpllt

import regolic.sat.Literal
import regolic.sat.Solver.Results._
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.smt.qfeuf.CongruenceSolver
import regolic.smt.qfeuf.FastCongruenceSolver

import regolic.StopWatch

object LazyBasicSolver {

  private def makeBlockingClauses(explanations: Map[Formula, List[Formula]], theoryLitToId: Map[Formula, Int]): List[Set[Literal]] = {

    /*
     * e.g. a = b because of a = c, c = b
     *      a = c and c = b implies a = b
     *      !e(a = c) or !e(c = b) or e(a = b)
     * where e is the theory literal to id / prop. literal map
     */
    explanations.map{
      case (eq, explanation) => {
        Set(new Literal(theoryLitToId(eq), true)) ++ explanation.map(exp => new Literal(theoryLitToId(exp), false))
      }
    }.toList
  }

  /*
   * Algorithm 11.2.1 from Decision Procedures by Kroening and Strichman
   */
  def solve(solver: regolic.smt.Solver, phi: Formula): Boolean = {
    val (clauses, nbVars, idToTheoryLit, theoryLitToId) = PropositionalSkeleton(phi)
    val satSolver = new regolic.sat.Solver(nbVars)
    clauses.foreach(satSolver.addClause)

    while(true) {
      satSolver.solve() match {
        case Unsatisfiable(_) => {
          return false
        }
        case Satisfiable(alpha) => {
          val thAlpha = idToTheoryLit.map{case (id, theoryLit) =>
            if(alpha(id)) theoryLit else Not(theoryLit)
          }.toList

          val (res, t) = solver.isSat(And(thAlpha))
          if(res) {
            return true
          } else {
            t match {
              case Some(explanation) => {
                val blockingClauses = makeBlockingClauses(explanation, theoryLitToId)
                //println("newClauses: "+ blockingClauses.mkString("\n", "\n", "\n"))
                //println("newClausesTheory: "+ blockingClauses.map(cl =>
                  //cl.map(lit => if(lit.polarity) idToTheoryLit(lit.id) else
                    //Not(idToTheoryLit(lit.id)))).mkString("\n", "\n", "\n"))
                blockingClauses.foreach(satSolver.addClause)
              }
              case None => { //no explanation returned from solver, block alpha
                satSolver.addClause(alpha.zipWithIndex.map{
                  case (b, i) => new Literal(i, !b)
                }.toSet)
              }
            }
          }
        }
        case Unknown => sys.error("SAT solver returned unknown")
      }
    }
    throw new Exception("Unreachable code.")
  }

}

