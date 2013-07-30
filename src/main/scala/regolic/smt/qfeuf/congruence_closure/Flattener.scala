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

  private def extract(f: FunctionApplication, acc: List[PredicateApplication] =
    Nil): Pair[List[PredicateApplication], Variable] = {
    f match {
      case Apply((t1: Variable), (t2: Variable)) => {
        val fv = freshVar
        (Equals(f, fv) :: acc, fv)
      }
      case Apply((t1: FunctionApplication), (t2: Variable)) => {
        val (l, lVar) = extract(t1, acc)
        val fv = freshVar
        (Equals(Apply(lVar, t2), fv) :: l, fv)
      }
      case Apply((t1: Variable), (t2: FunctionApplication)) => {
        val (r, rVar) = extract(t2, acc)
        val fv = freshVar
        (Equals(Apply(t1, rVar), fv) :: r, fv)
      }
      case Apply((t1: FunctionApplication), (t2: FunctionApplication)) => {
        val (l, lVar) = extract(t1, acc)
        val (r, rVar) = extract(t2, l)
        val fv = freshVar
        (Equals(Apply(lVar, rVar), fv) :: r, fv)
      }
      case _ => throw new Exception("Unsupported function "+ f)
    }
  }

  private def flatten(eqs: List[PredicateApplication]): List[PredicateApplication] = {
    eqs.flatMap{eq => eq match {
        case Equals((t1: Variable), (t2: Variable)) =>
          Equals(t1, t2) :: Nil
        case Equals((t1: Variable), (t2: FunctionApplication)) => {
          val (r, rVar) = extract(t2)
          Equals(t1, rVar) :: r
        }
        case Equals((t1: FunctionApplication), (t2: Variable)) => {
          val (l, lVar) = extract(t1)
          Equals(lVar, t2) :: l
        }
        case Equals((t1: FunctionApplication), (t2: FunctionApplication)) => {
          val (l, lVar) = extract(t1)
          val (r, rVar) = extract(t2)
          Equals(lVar, rVar) :: l ::: r
        }
        case _ => throw new Exception("Unsupported terms "+ eq)
      }
    }
  }

  def apply(eqs: List[PredicateApplication]): List[PredicateApplication] = flatten(eqs)

}
