package regolic.calculus

import regolic.asts.core.{Trees => CoreT}
import regolic.asts.fol.{Trees => FolT}
import regolic.asts.theories.real.{Trees => RealT}
import regolic.asts.core.Trees.TermQuantifierSymbol
import regolic.asts.core.Trees.TermQuantifierApplication

import regolic.algebra.Rational

object Trees {

  type Term = CoreT.Term
  type Formula = CoreT.Formula

  val RealSort = RealT.RealSort

  val True = FolT.True
  val False = FolT.False
  val Not = FolT.Not
  val Or = FolT.Or
  val And = FolT.And
  val Implies = FolT.Implies
  val Iff = FolT.Iff
  val IfThenElse = FolT.IfThenElse

  val Equals = RealT.Equals

  val LessThan = RealT.LessThan
  val LessEqual = RealT.LessEqual
  val GreaterThan = RealT.GreaterThan
  val GreaterEqual = RealT.GreaterEqual

  type Variable = CoreT.Variable
  val Var = RealT.Var
  val Number = RealT.Num
  val Zero = RealT.Zero
  val One = RealT.One

  val Add = RealT.Add
  val Sub = RealT.Sub
  val Mul = RealT.Mul
  val Div = RealT.Div

  val Pow = RealT.Pow

  val Neg = RealT.Neg
  val Abs = RealT.Abs
  val Floor = RealT.Floor

  val Max = RealT.Max
  val Min = RealT.Min

  case class Sequence(n: Variable, t: Term)
  case class Series(n: Variable, t: Term)
  case class RealFunction(x: Variable, t: Term)

  object SummationSymbol {
    def apply() = TermQuantifierSymbol("\\sigma", List(RealSort(), RealSort(), RealSort()), RealSort())
    def unapply(symb: TermQuantifierSymbol): Boolean = symb match {
      case TermQuantifierSymbol("\\sigma", List(RealSort(), RealSort(), RealSort()), RealSort()) => true
      case _ => false
    }
  }
  object Summation {
    def apply(v: Variable, lb: Term, ub: Term, body: Term) = TermQuantifierApplication(SummationSymbol(), v, List(lb, ub, body))
    def unapply(appli: TermQuantifierApplication): Option[(Variable,  Term, Term, Term)] = appli match {
      case TermQuantifierApplication(SummationSymbol(), v, List(lb, ub, body)) => Some((v, lb, ub, body))
      case _ => None
    }
  }

  def freshVar(prefix: String): Variable = RealT.freshVar(prefix)

}
