package regolic.dpllt

import regolic.sat.Literal
import regolic.sat.Solver
import regolic.sat.Solver.Results._
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.smt.qfeuf.CongruenceSolver
import regolic.smt.qfeuf.FastCongruenceSolver

class LazyBasicSolver() {

  private def makeClauses(explanations: Map[Formula, List[Formula]], theoryLitToId: Map[Formula, Int]): List[Set[Literal]] = {

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
  def solve(phi: Formula): Boolean = {
    val (clauses, nbVars, idToTheoryLit, theoryLitToId) = PropositionalSkeleton(phi)
    val satSolver = new Solver(nbVars)
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

          val (res, t) = FastCongruenceSolver.isSat(And(thAlpha))
          if(res) {
            return true
          } else {
            makeClauses(t.get, theoryLitToId).foreach(satSolver.addClause)
          }
        }
        case Unknown => sys.error("SAT solver returned unknown")
      }
    }
    throw new Exception("Unreachable code.")
  }
}

