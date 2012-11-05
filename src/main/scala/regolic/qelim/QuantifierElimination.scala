package regolic.qelim

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip.prenexNormalForm

abstract class QuantifierElimination {

  //apply full quantifier elimination to a formula, return a quantifier free
  //equivalent formula. Note that this will take care of any combination of
  //quantifiers
  //defaut implementation will use elimExistential, but optimized version
  //can be redefined for each theory
  def apply(formula: Formula): Formula = {
    val prenexFormula = prenexNormalForm(formula)
    def rec(f: Formula): Formula = f match {
      case Forall(x, b) => {
        val qf = rec(b)
        Not(elimExistential(Not(qf), x))
      }
      case Exists(x, b) => {
        val qf = rec(b)
        elimExistential(qf, x)
      }
      case f => f
    }
    rec(prenexFormula)
  }

  //one step of the quantifier elimination, assume the input formula
  //is quantifier free and eliminate the variable that is assumed to
  //be existentially quantified.
  def elimExistential(formula: Formula, variable: Variable): Formula = {
    val (f, _) = constructiveElimExistential(formula, variable)
    f
  }

  //the basic building block, it returns a witness for the variable that prove
  //the existence of a term. It also return an equivalent formula, which simply
  //could be the formula with x substituted by the witness term, but could
  //also be more optimized
  def constructiveElimExistential(formula: Formula, variable: Variable): (Formula, Term)
}
