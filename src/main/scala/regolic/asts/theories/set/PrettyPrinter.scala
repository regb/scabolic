package regolic.asts.theories.set

import Trees._
import regolic.asts.core.Trees.{Term, Formula}
import regolic.asts.fol

object PrettyPrinter {

  private val UNIONSTR = "\u222A"
  private val INTERSTR = "\u2229"
  private val INCLSTR = "\u2282"
  private val INCLEQSTR = "\u2286"
  private val NOTSTR = "\u00AC"

  def apply(term: Term): String = fol.PrettyPrinter.termPrinter(term, defaultFormulaPrinter, defaultTermPrinter)

  private def defaultFormulaPrinter(f: Formula): Option[String] = f match {
    case Include(s1, s2) => Some("(" + apply(s1) + " " + INCLSTR + " " + apply(s2) + ")")
    case IncludeEq(s1, s2) => Some("(" + apply(s1) + " " + INCLEQSTR + " " + apply(s2) + ")")
    case _ => None
  }

  private def defaultTermPrinter(t: Term): Option[String] = t match {
    case Constructor(name, Seq()) => Some(name + "()")
    case Constructor(name, sts) => Some(name + sts.map(apply).mkString("(", ", ", ")"))
    case Union(sts) => Some(sts.map(apply).mkString("(", " " + UNIONSTR + " ", ")"))
    case Intersection(sts) => Some(sts.map(apply).mkString("(", " " + INTERSTR + " ", ")"))
    case Complement(s) => Some(NOTSTR + apply(s))
    case Var(name) => Some(name)
    case Empty() => Some("0")
    case Universe() => Some("1")
    case _ => None
  }
}
