package regolic.smt.qfeuf

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

/*
 * Flatten nested function calls by introducing auxiliary variables
 * Needs one extra equality compared to "Fast congruence closure with
 * extensions" paper
 */
object Flattener {

  private def freshVar = freshVariable("variable", regolic.asts.theories.int.Trees.IntSort())

  private def extract(f: FunctionApplication, acc: List[PredicateApplication]): List[PredicateApplication] = {
    f match {
      case FunctionApplication(applyFun, List((t1: Variable), (t2: Variable))) => {
        Equals(f, freshVar) :: acc
      }
      case FunctionApplication(applyFun, List((t1: FunctionApplication), (t2: Variable))) => {
        val l = extract(t1, acc)
        val List(_, lVar) = l.head.terms
        Equals(FunctionApplication(applyFun, List(lVar, t2)), freshVar) :: l
      }
      case FunctionApplication(applyFun, List((t1: Variable), (t2: FunctionApplication))) => {
        val r = extract(t2, acc)
        val List(_, rVar) = r.head.terms
        Equals(FunctionApplication(applyFun, List(t1, rVar)), freshVar) :: r
      }
      case FunctionApplication(applyFun, List((t1: FunctionApplication), (t2: FunctionApplication))) => {
        val l = extract(t1, acc)
        val r = extract(t2, l)
        val List(_, lVar) = l.head.terms
        val List(_, rVar) = r.head.terms
        Equals(FunctionApplication(applyFun, List(lVar, rVar)), freshVar) :: r
      }
      case _ => throw new Exception("Unsupported function "+ f)
    }
  }

  private def flatten(eqs: List[PredicateApplication]): List[PredicateApplication] = {
    eqs.flatMap{eq => eq match {
        case Equals((t1: Variable), (t2: Variable)) =>
          Equals(t1, t2) :: Nil
        case Equals((t1: Variable), (t2: FunctionApplication)) => {
          val r = extract(t2, Nil)
          val List(_, rVar) = r.head.terms
          Equals(t1, rVar) :: r
        }
        case Equals((t1: FunctionApplication), (t2: Variable)) => {
          val l = extract(t1, Nil)
          val List(_, lVar) = l.head.terms
          Equals(lVar, t2) :: l
        }
        case Equals((t1: FunctionApplication), (t2: FunctionApplication)) => {
          val l = extract(t1, Nil)
          val r = extract(t2, Nil)
          val List(_, lVar) = l.head.terms
          val List(_, rVar) = r.head.terms
          Equals(lVar, rVar) :: l ::: r
        }
        case _ => throw new Exception("Unsupported terms "+ eq)
      }
    }
  }

  def apply(eqs: List[PredicateApplication]): List[PredicateApplication] = flatten(eqs)

}
