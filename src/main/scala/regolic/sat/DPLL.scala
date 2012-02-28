package regolic.sat

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._

object DPLL extends Solver {

  def isSat(clauses: List[Formula]): Option[Map[PredicateApplication, Boolean]] = {
    val simpleClauses = clauses.map(simplifyOr).filterNot(isTrue)
    val (clauses2, varsMapping) = bcp(simpleClauses)
    if(clauses2.forall(isTrue))
      Some(varsMapping)
    else if(clauses2.exists(isFalse))
      None
    else {
      println(clauses2)
      val chosenVar = clauses2.flatMap(f => predicateVars(f)).head
      val left = isSat(clauses2.map(f => subst(f, chosenVar, True())))
      val right = isSat(clauses2.map(f => subst(f, chosenVar, False())))
      (left, right) match {
        case (Some(m1), _) => Some((m1 ++ varsMapping) + (chosenVar -> true))
        case (_, Some(m2)) => Some((m2 ++ varsMapping) + (chosenVar -> false))
        case (None, None) => None
      }
    }
  }

  private def simplifyOr(or: Formula): Formula = or match {
    case Or(Nil) => False()
    case Or(fs) if fs.exists(isTrue) => True()
    case Or(fs) if fs.exists(isFalse) => fs.filterNot(isFalse) match {
      case Nil => False()
      case fs2 => Or(fs2)
    }
    case _ => or
  }

  def bcp(clauses: List[Formula]): (List[Formula], Map[PredicateApplication, Boolean]) = {
    def unitClause(f: Formula) = f match {
      case Or(List(Var(_))) => true
      case Or(List(Not(Var(_)))) => true
      case Var(_) => true
      case Not(Var(_)) => true
      case _ => false
    }
    clauses.find(unitClause) match {
      case None => (clauses, Map())
      case Some(o) => {
        val p = o match {
          case Or(List(p)) => p
          case p => p
        }
        val (substClauses, mappedVar) = p match {
          case Not(p@Var(_)) => (clauses.map(f => subst(f, p, False())), Map[PredicateApplication, Boolean](p -> false))
          case p@Var(_) => (clauses.map(f => subst(f, p, True())), Map[PredicateApplication, Boolean](p -> true))
        }
        val simpleClauses = substClauses.map(f => simplifyOr(f))
        val res = simpleClauses.filterNot(isTrue)
        if(res.exists(isFalse))
          (res, mappedVar)
        else {
          val (finalClauses, finalMap) = bcp(res)
          (finalClauses, finalMap ++ mappedVar)
        }
      }
    }
  }

  private def isTrue(f: Formula): Boolean = f match {
    case True() => true
    case Not(False()) => true
    case _ => false
  }
  private def isFalse(f: Formula): Boolean = f match {
    case False() => true
    case Not(True()) => true
    case _ => false
  }

}
