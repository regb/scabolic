package regolic.qelim.lra

import regolic.qelim.QuantifierElimination
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._
import regolic.asts.theories.real.Trees._

object FourierMotzkin extends QuantifierElimination {

  def constructiveElimExistential(formula: Formula, variable: Variable): (Formula, Term) = {
    require(isQuantifierFree(formula))
    val And(lits) = formula
    null
  }

}
