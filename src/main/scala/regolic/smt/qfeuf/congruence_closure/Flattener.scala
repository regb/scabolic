package regolic.smt.qfeuf

import regolic.asts.core.Trees._

object Flattener {

  private def freshVar = freshVariable("v", regolic.asts.theories.int.Trees.IntSort())

  private def extract(f: FunctionApplication, acc: List[Equation]): List[Equation] = {
    f match {
      case FunctionApplication(applyFun, List((t1: Variable), (t2: Variable))) => {
        (f, freshVar) :: acc
      }
      case FunctionApplication(applyFun, List((t1: FunctionApplication), (t2: Variable))) => {
        val l = extract(t1, acc)
        (FunctionApplication(applyFun, List(l.head._2, t2)), freshVar) :: l
      }
      case FunctionApplication(applyFun, List((t1: Variable), (t2: FunctionApplication))) => {
        val r = extract(t2, acc)
        (FunctionApplication(applyFun, List(t1, r.head._2)), freshVar) :: r
      }
      case FunctionApplication(applyFun, List((t1: FunctionApplication), (t2: FunctionApplication))) => {
        val l = extract(t1, acc)
        val r = extract(t2, l)
        (FunctionApplication(applyFun, List(l.head._2, r.head._2)), freshVar) :: r
      }
      case _ => throw new Exception("Unsupported function "+ f)
    }
  }

  private def flatten(eqs: List[(Term, Term)]): List[Equation] = {
    eqs.flatMap{eq => eq match {
        case ((t1: Variable), (t2: Variable)) =>
          (t1, t2) :: Nil
        case ((t1: Variable), (t2: FunctionApplication)) => {
          val r = extract(t2, Nil)
          (t1, r.head._2) :: r
        }
        case ((t1: FunctionApplication), (t2: Variable)) => {
          val l = extract(t1, Nil)
          (l.head._2, t2) :: l
        }
        case ((t1: FunctionApplication), (t2: FunctionApplication)) => {
          val l = extract(t1, Nil)
          val r = extract(t2, Nil)
          (l.head._2, r.head._2) :: l ::: r
        }
        case _ => throw new Exception("Unsupported terms "+ eq)
      }
    }
  }

  def apply(eqs: List[(Term, Term)]): List[Equation] = flatten(eqs)

}
