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
    explanations.map{
      case (Not(eq), explanation) => {
        Set(new Literal(theoryLitToId(eq), true)) ++ explanation.map(exp => new Literal(theoryLitToId(exp), false))
      }
    }.toList
  }

  def solve(phi: Formula): Boolean = {
    val (clauses, nbVars, idToTheoryLit, theoryLitToId) = PropositionalSkeleton(phi)
    val satSolver = new Solver(nbVars)
    clauses.foreach(satSolver.addClause)
    var done = false
    var retVal = false
    while(!done) {
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
            println("explanations: "+ t.mkString("\n", "\n", "\n"))
            makeClauses(t.get, theoryLitToId).foreach(satSolver.addClause)
            //retVal = false
            //done = true
          }
        }
        case Unknown => sys.error("SAT solver returned unknown")
      }
    }
    throw new Exception("Unreachable code.")
  }
}

