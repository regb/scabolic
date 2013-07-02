package regolic.dpllt

import regolic.asts.core.Trees._

class LazyBasicSolver() {

  def solve(f: Formula) {

    val (clauses, nbVars, mapping) = PropositionalSkeleton(f)
    val satSolver = new regolic.sat.Solver(nbVars)

  }
}

