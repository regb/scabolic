package regolic.sat

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._

import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer

trait Solver {

  object Var {
    def apply(name: String): PredicateApplication = PredicateApplication(PredicateSymbol(name, List()), List())
    def unapply(p: PredicateApplication): Option[String] = p match {
      case True() => None
      case False() => None
      case PredicateApplication(PredicateSymbol(name, List()), List()) => Some(name)
      case _ => None
    }
  }

  private var freshVarCount = -1
  def freshVar(): PredicateApplication = { freshVarCount += 1; Var("p_" + freshVarCount) }

  def subst(f: Formula, p: PredicateApplication, newF: Formula): Formula = mapPostorder(f, (f2: Formula) => f2 match {
    case p2@Var(_) if p == p2 => newF
    case f2 => f2
  }, (t: Term) => t)

  def predicateVars(f: Formula): Set[PredicateApplication] = foldPostorder(f, Set[PredicateApplication]())((a, f) => f match {
      case v@Var(_) => a + v
      case _ => a
    }, (a, t) => a)


  def equisatCNF(formula: Formula): List[Formula] = {
    val representations = new HashMap[Formula, PredicateApplication]
    val constraints = new ListBuffer[Formula]

    //for each subformula, create a new representation and add the constraints while returning the representation
    def inductionStep(subForm: Formula): Formula = subForm match {
      case Not(f) => {
        val repr = freshVar()
        constraints += Or(Not(repr), Not(f))
        constraints += Or(repr, f)
        repr
      }
      case And(fs) => {
        val repr = freshVar()
        for(f <- fs)
          constraints += Or(Not(repr), f)
        constraints += Or(repr :: fs.map(Not(_)))
        repr
      }
      case Or(fs) => {
        val repr = freshVar()
        constraints += Or(Not(repr) :: fs)
        for(f <- fs)
          constraints += Or(repr, Not(f))
        repr
      }
      case Implies(f1, f2) => {
        val repr = freshVar()
        constraints += Or(Not(repr), Not(f1), f2)
        constraints += Or(repr, f1)
        constraints += Or(repr, Not(f2))
        repr
      }
      case Iff(f1, f2) => {
        val repr = freshVar()
        constraints += Or(Not(repr), Not(f1), f2)
        constraints += Or(Not(repr), f1, Not(f2))
        constraints += Or(repr, Not(f1), Not(f2))
        constraints += Or(repr, f1, f2)
        repr
      }
      case _ => subForm
    }

    val repr = mapPostorder(formula, inductionStep _, (t: Term) => t)
    constraints += repr
     
    constraints.toList
  }

  def isSat(clauses: List[Formula]): Option[Map[PredicateApplication, Boolean]]
  def isSat(f: Formula): Option[Map[PredicateApplication, Boolean]] = {
    if(isConjunctiveNormalForm(f)) {
      val And(fs) = f
      isSat(fs)
    } else {
      val initialVars: Set[PredicateApplication] = predicateVars(f)
      val equisatFormulas = equisatCNF(f)
      isSat(equisatFormulas) match {
        case None => None
        case Some(map) => Some(map.filter{ case (v, _) => initialVars.contains(v) })
      }
    }
  }

}
