package regolic.simplifier

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.theories.real.Trees._
import regolic.asts.theories.real.Manip._
import regolic.equation.PolynomialSolver

object PolynomialFactorizer {

  def factorizePolynomial(polynomial: Term): Term = {
    require(isSingleVarPolynomial(polynomial))
    val roots = PolynomialSolver.polynomialRoots(polynomial)
    val variables = vars(polynomial)
    assert(variables.size == 1)
    val variable = variables.toList.head
    val factors = roots.foldLeft(List[Term]())( (a, r) => (1 to r._2).map(_ => Sub(variable, r._1)).toList ::: a)
    Mul(factors)
  }

}
