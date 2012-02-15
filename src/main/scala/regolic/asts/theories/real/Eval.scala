package regolic.asts.theories.real

import Trees._
import regolic.algebra.Rational
import regolic.asts.core.Trees.{Term, Variable}

/*
   Here we should be using Term for the evaluation because Rational do not cover all of the
   real numbers !
 */

object Eval {

  def apply(t: Term, v: Variable, r: Rational): Rational = eval(t, Map(v -> r))
  def apply(t: Term, context: Map[Variable, Rational]): Rational = eval(t, context)

  private def eval(t: Term, context: Map[Variable, Rational]): Rational = t match {
    case v@Var(_) => context(v)
    case Num(r) => r
    case Add(ts) => ts.foldLeft(Rational.zero)((a, t) => a + eval(t, context))
    case Mul(ts) => ts.foldLeft(Rational.one)((a, t) => a * eval(t, context))
    case Sub(t1, t2) => eval(t1, context) - eval(t2, context)
    case Div(t1, t2) => eval(t1, context) / eval(t2, context)
    case Pow(t1, t2) => eval(t1, context).toPower(eval(t2, context).toInt) 
    case Neg(t) => -eval(t, context)
    case Abs(t) => eval(t, context).abs
    case Floor(t) => eval(t, context).floor
    case Max(ts) => ts.map(t => eval(t, context)).max
    case Min(ts) => ts.map(t => eval(t, context)).min
    case NthRoot(i, t) => {
      val rat = eval(t, context)
      rat.nthRoot(i) match {
        case Some(r) => r
        case None => null //TODO, change return type to Term and put Sqrt(Num(rat))
      }
    }
    case x@_ => sys.error("unexpected: " + x)
  }
}
