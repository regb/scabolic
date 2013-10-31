package regolic.smt.qfeuf

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

/*
 * All regular function calls are replaced by calls to "apply", which is a 2-ary
 * function. Functions become arguments of "apply":
 * e.g. g(a, b) => apply(apply(g, a), b)
 */
object Currifier {

  private def curry(t: Term): Term = {
    def makeFuns(terms: List[Term]): Term = {
      terms match {
        case x :: Nil => x
        case x :: xs => Apply(makeFuns(xs), curry(x))
        case _ => throw new Exception("Impossible case when matching terms "+ terms)
      }
    }

    t match {
      case a@Apply(_, _) => a
      case v@Variable(_, _) => v
      case FunctionApplication(funSym@FunctionSymbol(name, paramSorts, returnSort), args) => {
        //val newSort = FunctionSort(TupleSort(paramSorts), returnSort)
        //val newSymbol = FunctionSymbol
        //Apply(
        makeFuns((Variable(name, returnSort) :: args).reverse)
      }
    }
  }

  def apply(t: Term): Term = curry(t)

  def apply(eq: PredicateApplication): PredicateApplication = eq match {
    case Equals(s, t) => Equals(curry(s), curry(t))
  }
}

