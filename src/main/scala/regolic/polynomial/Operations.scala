package regolic.polynomial

import regolic.asts.core.Trees._
import regolic.asts.theories.real.Trees._
import regolic.asts.theories.real.Manip._

object Operations {

  //TODO: probably better to have two arguments rather than a Div

  def euclidianDivision(term: Term): (Term, Term) = {
    require(isRational(term))
    val Div(numerator@Add(numerators), denominator@Add(denominators)) = term
    val Mul(List(leadNumeratorCoeff, Pow(variable@Var(_), Num(leadNumeratorDegree)))) = numerators.head
    val Mul(List(leadDenominatorCoeff, Pow(v2, Num(leadDenominatorDegree)))) = denominators.head
    assert(variable == v2)
    assert(leadNumeratorDegree.isInteger && leadDenominatorDegree.isInteger)

    if(leadNumeratorDegree < leadDenominatorDegree) {
      (Zero(), numerator)
    }
    else {
      val newLeadCoeff = simplify(Div(leadNumeratorCoeff, leadDenominatorCoeff))
      val newLeadDegree = Num(leadNumeratorDegree - leadDenominatorDegree)
      val leadQuotient = Mul(List(newLeadCoeff, Pow(variable, newLeadDegree)))

      val multQuotient = Mul(List(leadQuotient, Add(denominators)))
      val remainder = Sub(numerator, multQuotient)

      val (recQuotient, recRemainder) = euclidianDivision(Div(polynomialForm(remainder, variable), denominator))

      (polynomialForm(Add(List(recQuotient, leadQuotient)), variable), recRemainder)
    }
  }

}
