package regolic.polynomial

import regolic.algebra.Ring

/* Let's say we only need uni-variable polynomials */

/* TODO: I believe Polynomial over ring/field are themself ring or fields */
/* First element is higher degree */
class Polynomial[T <: Ring[T]](coefs: Seq[T])(implicit field: Ring[T], man: ClassManifest[T]) {

  private val repr: Array[T] = coefs.toArray

  def degree: Int = repr.size
  def coef(i: Int): T = repr(i)
}

object Polynomial {

  import regolic.algebra.Rational
  import regolic.algebra.Integer
  import regolic.asts.theories.number.Trees._
  import regolic.asts.theories.real.{Trees => RealT, Eval => RealEval}
  import regolic.asts.theories.real.Manip._
  import regolic.asts.theories.int.{Trees => IntT}
  import regolic.asts.core.Trees.{Formula, Term, Variable}
  import regolic.asts.core.Manip._
  import regolic.asts.fol.Manip._

  def fromIntTerm(t: Term): Polynomial[Integer] = {
    require(isPolynomial(t))
    null
  }

  def fromRealTerm(t: Term): Polynomial[Rational] = {
    require(isPolynomial(t))
    val variables = vars(t)
    require(variables.size == 1)
    new Polynomial(polynomialForm(t, variables.head))
  }

  //Is polynomial (accepting multiple variables)
  //do not require the polynomial to be in a standard form
  def isPolynomial(term: Term): Boolean = term match {
    case Var(_) | Num(_) => true
    case Add(ts) => ts.forall(isPolynomial(_))
    case Sub(t1, t2) => isPolynomial(t1) && isPolynomial(t2)
    case Mul(ts) => ts.forall(isPolynomial(_))
    case Neg(t) => isPolynomial(t)
    case Div(t1, Num(_)) => isPolynomial(t1)
    case Pow(t1, Num(r)) => isPolynomial(t1) && r.isInteger
   
    case _ => false
  }

  /*
   * return an*x^n + ... + a0*x^0, with an != 0 and x being the head variable
   * note that all these terms appears explicitly in the returned tree, they are not simplified
   * note also that a_i could be a complex polynomial consisting of other variables, in that case, it will be
   * recursively put in polynomialForm according to the rest of the list of variables. If the list is empty no change
   * is done to the term.
   *
   * Note that there will be one level of nested Add and Mul for each variable in the list, even if the coefficient
   * do not contains any of the variables. This will be applied to each coefficient.
   */
  def polynomialForm(term: Term, variable: Variable): List[Rational] = {
    require(isPolynomial(term)) //this requires make sure that there won't be any n^x in the expanded form

    def containsNTimesVar(t: Term, degree: Int): Boolean = 
      count(t, (_: Formula) => false, (t: Term) => t == variable) == degree

    def unify(ts: List[Term], degree: Int): List[Rational] = if(ts.isEmpty) Nil else {
      val (thisDegree, otherDegree) = ts.partition(x => containsNTimesVar(x, degree))
      val coeff: Rational = {
        val coeffs = thisDegree.map {
          case Mul(ts) => {
            val ts0 = ts.filterNot(_ == variable)
            ts0.foldLeft(Rational.one)((acc, t) => acc * RealEval(t))
          }
        }
        coeffs.foldLeft(Rational.zero)((acc, t) => acc + t)
      }
      coeff :: unify(otherDegree, degree + 1)
    }

    val Add(ts) = expandedForm(term)
    unify(ts, 0).reverse match {
      case Nil => List(Rational.zero)
      case xs => xs
    }
  }

}
