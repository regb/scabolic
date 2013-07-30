package regolic.smt

import regolic.asts.core.Trees._
import regolic.asts.theories.int.Trees.IntSort

package object qfeuf {

  object ApplySymbol {
    def apply(sort: Sort): FunctionSymbol = FunctionSymbol("apply", List(sort, sort), sort)
    def unapply(s: FunctionSymbol): Option[Sort] = s match {
      case FunctionSymbol("apply", List(s1, s2), s3) if s1 == s2 && s2 == s3 => Some(s1)
      case _ => None
    }
  }
  object Apply {
    def apply(t1: Term, t2: Term): FunctionApplication = FunctionApplication(ApplySymbol(t1.sort), List(t1, t2))
    def unapply(pApply: FunctionApplication): Option[(Term, Term)] = pApply match {
      case FunctionApplication(ApplySymbol(_), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }
}

