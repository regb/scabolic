package regolic.resolution

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._

object Resolution {

  def apply(clauses: List[Formula]): Boolean = {
    clauses.foreach(f => assert(f match { case Or(_) => true case _ => false }))

    var base: Set[List[Formula]] = clauses.map{
      case Or(lits) => lits
      case _ => sys.error("")
    }.toSet

    var newDerivation = true
    var foundContradiction = false

	
    while(newDerivation && !foundContradiction) {
      println("Base of knowledge is: " + base)
      newDerivation = false

      base.flatMap(l1 => base.map(l2 => (l1, l2))).foreach{ case (cl1, cl2) => {
        resolvent(cl1, cl2) match {
          case Some(res) =>
            if(!base.contains(res)) {
              base = base + res
              newDerivation = true
            }
            if(res == Nil) foundContradiction = true
          case None =>
        }
      }}
      
    }

    println("Final Base: " + base)

    foundContradiction
  }

  def unify(p1: PredicateApplication, p2: PredicateApplication): Option[Map[Variable, Term]] = {
    val (PredicateApplication(s1, args1), PredicateApplication(s2, args2)) = (p1, p2)
    if(s1 != s2) None else args1.zip(args2).foldLeft(Some(Map()): Option[Map[Variable, Term]])((acc, p) => unify(p._1, p._2, acc))
  }

  def unify(t1: Term, t2: Term, osubst: Option[Map[Variable, Term]] = Some(Map())): 
        Option[Map[Variable, Term]] = if(osubst == None) None else {
    val subst: Map[Variable, Term] = osubst.get
    (t1, t2) match {
      case (v1@Variable(_, _), t2) => {
        if(v1 == t2) osubst 
        else if(!contains(substitute(t2, subst), v1)) subst.get(v1) match {
          case Some(s) => unify(s, t2, Some(subst))
          case None => Some(subst + (v1 -> t2))
        } 
        else None
      }
      case (t1, v2@Variable(_, _)) => {
        if(t1 == v2) osubst 
        else if(!contains(substitute(t1, subst), v2)) subst.get(v2) match {
          case Some(s) => unify(t1, s, Some(subst))
          case None => Some(subst + (v2 -> t1))
        }
        else None
      }
      case (FunctionApplication(s1, args1), FunctionApplication(s2, args2)) if s1 == s2 =>
        args1.zip(args2).foldLeft(Some(subst): Option[Map[Variable, Term]])((acc, p) => unify(p._1, p._2, acc))
      case _ => None
    }
  }

  def resolvent(clause1: List[Formula], clause2: List[Formula]): Option[List[Formula]] = {

    def rec(leftClause1: List[Formula], rightClause1: List[Formula],
            leftClause2: List[Formula], rightClause2: List[Formula]): Option[List[Formula]] = {
      (rightClause1, rightClause2) match {
        case ((lit1@PredicateApplication(_, _)) :: rest1, Not(lit2@PredicateApplication(_, _)) :: rest2) => 
          unify(lit1, lit2) match {
            case None => rec(lit1 :: leftClause1, rest1, leftClause2, Not(lit2) :: rest2)
            case Some(subst) =>  Some((leftClause1 ::: leftClause2 ::: rest1 ::: rest2).map(substitute(_, subst)))
          }
        case (Not(lit1@PredicateApplication(_, _)) :: rest1, (lit2@PredicateApplication(_, _)) :: rest2) => 
          unify(lit1, lit2) match {
            case None => rec(lit1 :: leftClause1, rest1, leftClause2, Not(lit2) :: rest2)
            case Some(subst) =>  Some((leftClause1 ::: leftClause2 ::: rest1 ::: rest2).map(substitute(_, subst)))
          }
        case (head :: rest1, rest2) => rec(head :: leftClause1, rest1, leftClause2, rest2)
        case (Nil, head::rest2) => rec(Nil, clause1, head :: leftClause2, rest2)
        case (Nil, Nil) => None
      }
    }

    val resolv = rec(Nil, clause1, Nil, clause2).map(_.distinct)

    resolv match {
      case Some(clause) => 
        if(
        clause.exists(lit1 => clause.exists(lit2 => (lit1, lit2) match {
          case (Not(l1), l2) if l1 == l2 => true
          case (l1, Not(l2)) if l1 == l2 => true
          case _ => false
        }))) 
          None 
        else 
          Some(clause)
      case None => None
    }

  }


  def test() {

    val a = PredicateApplication(PredicateSymbol("A", Nil), Nil)
    val b = PredicateApplication(PredicateSymbol("B", Nil), Nil)
    val c = PredicateApplication(PredicateSymbol("C", Nil), Nil)
    val d = PredicateApplication(PredicateSymbol("D", Nil), Nil)
    val e = PredicateApplication(PredicateSymbol("E", Nil), Nil)

      val f1 = Or(List(a, Not(c), b))
      val f2 = Or(List(e, c, d))
      val f3 = Or(List(Not(b), c))
      val f4 = Or(List(Not(c)))

    val f = List(f1, f2)
    apply(f)
  }

}
