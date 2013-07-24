package regolic.smt.qfeuf

import regolic.asts.core.Trees._

// TODO try to enforce constant where possible for better type safety
object Currifier {

  private def curry(t: Term): Term = {
    def makeFuns(terms: List[Term]): Term = {
      terms match {
        case x :: Nil => x
        case x :: xs => FunctionApplication(applyFun, List(makeFuns(xs), curry(x)))
        case _ => throw new Exception("impossible case")
      }
    }

    if(t.isInstanceOf[Variable])
      t
    else {
      val FunctionApplication(fun, args) = t
      makeFuns((Variable(fun.name, fun.returnSort) :: args).reverse)
    }
  }

  def apply(eqs: List[(Term, Term)]): List[(Term, Term)] = eqs.map{case (s, t) => (curry(s), curry(t))}
}

