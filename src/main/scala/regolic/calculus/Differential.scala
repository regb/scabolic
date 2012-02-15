package regolic.calculus

import regolic.asts.core.Trees._
import regolic.asts.theories.real.Trees._
import regolic.asts.theories.real.Manip._

object Differential {

  def derive(t: Term, x: Variable): Term = {
    def derive0(t: Term): Term = {
      val res = t match {
        case Num(_) => Zero()
        case v@Var(_) if v == x => One()
        case Var(_) => Zero()
        case Add(ts) => Add(ts.map(t => derive0(t)))
        case Sub(t1, t2) => Sub(derive0(t1), derive0(t2))
        case Mul(t :: Nil) => derive0(t)
        case Mul(t :: ts) => Add(List(
              Mul(List(derive0(t), Mul(ts))),
              Mul(List(t, derive0(Mul(ts))))))
        case Div(t1, t2) => Div(
            Sub(
              Mul(List(derive0(t1), t2)), 
              Mul(List(derive0(t2), t1))),
            Mul(List(t2,t2)))
        case Neg(t) => Neg(derive0(t))
        //case Pow(t, n@Num(r)) => Mul(List(derive0(t), n, Pow(t, Num(r-1))))
        case NthRoot(n, t) => Div(
            derive0(t), 
            Mul(List(Num(n), NthRoot(n, Pow(t, Num(n-1))))))
        case exp@Exp(t) => Mul(List(derive0(t), exp))
        case Ln(t) => Mul(List(Div(Num(1), t), derive0(t)))
        case _ => sys.error("unexpected: " + t)
      }
      res
    }

    derive0(toLnAndExp(t))
  }
}
