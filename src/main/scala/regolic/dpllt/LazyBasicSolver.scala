package regolic.dpllt

import regolic.sat.PropLiteral
import regolic.sat.PropLiteralID
import regolic.sat.TLiteral
import regolic.sat.TLiteralID
import regolic.sat.Literal
import regolic.sat.Solver.Results._
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.printers.SmtLib2

import regolic.StopWatch

object LazyBasicSolver {

  private def makeBlockingClauses(explanations: Map[Formula, List[Formula]],
    encoding: collection.mutable.Map[Formula, Int]): List[Set[Literal]] = {

    /*
     * e.g. a = b because of a = c, c = b
     *      a = c and c = b implies a = b
     *      !e(a = c) or !e(c = b) or e(a = b)
     * where e is the theory literal to id / prop. literal map
     */
    explanations.map{
      case (eq, explanation) => {
        Set(new TLiteral(encoding(eq), true)) ++ explanation.map(exp => new TLiteral(encoding(exp), false))
      }
    }.toList.asInstanceOf[List[Set[Literal]]]
  }

  /*
   * Algorithm 11.2.1 from Decision Procedures by Kroening and Strichman
   */
  def solve(solver: regolic.smt.Solver, phi: Formula): Boolean = {
    val (clauses, encoding) = PropositionalSkeleton(phi)
    val satSolver = new regolic.sat.Solver(PropLiteralID.count + TLiteralID.count)
    clauses.foreach(satSolver.addClause)

    while(true) {
      satSolver.solve() match {
        case Unsatisfiable => {
          return false
        }
        case Satisfiable(alpha) => {
          val thAlpha = encoding.theory.zipWithIndex.map{case (theoryLit, id) =>
            if(alpha(id)) theoryLit else Not(theoryLit)
          }.toList

          val (res, t) = solver.isSat(And(thAlpha))
          if(res) {
            return true
          } else {
            t match {
              case Some(explanation) => {
                val blockingClauses = makeBlockingClauses(explanation, encoding.id)
                blockingClauses.foreach(satSolver.addClause)
              }
              case None => { //no explanation returned from T-solver, block alpha
                satSolver.addClause(alpha.zipWithIndex.map{
                  case (b, i) => new TLiteral(i, !b)
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

