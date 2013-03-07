package regolic.equation

/*
 * Provides algorithms that works on a single linear equation with some variables
 */

object LinearEquationSolver {

  private def coeffVar(v: Variable, t: Term): Rational = if(!contains(t, v)) Rational.zero else polynomialForm(t, v) match {
    case Add(Mul(coeff :: Pow(v2, Num(r)) :: Nil) :: rest :: Nil) if v2==v && r.isOne => Eval(coeff, Map())
    case Add(Mul(coeff :: Pow(v2, Num(r)) :: Nil) :: Nil) if v2==v && r.isZero => Rational.zero
    case _ => throw new IllegalArgumentException("not a linear expression: " + t)
  }

  //find one particular instance of a solution to the equation
  //def particularSolution(eq: PredicateApplication): Map[Variable, Term] {
  //  val lhSide: Term = polynomialForm(eq.map{ case Equals(t1, t2) => Sub(t1, t2) })
  //  val varsToCoef: Map[Variable, Term] = 
  //}

}
