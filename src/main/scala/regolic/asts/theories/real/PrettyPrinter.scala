package regolic.asts.theories.real

import Trees._
import regolic.asts.core.Trees.{Term, Formula}
import regolic.asts.fol

object PrettyPrinter {

  private val LTSTR  = "<"
  private val LESTR  = "\u2264"
  private val GTSTR  = ">"
  private val GESTR  = "\u2265"
  private val ADDSTR = "+"
  private val SUBSTR = "-"
  private val MULSTR = "*"
  private val DIVSTR = "/"
  private val POWSTR = "^"

  def apply(formula: Formula): String = fol.PrettyPrinter.formulaPrinter(formula, defaultFormulaPrinter, defaultTermPrinter)
  def apply(term: Term): String = fol.PrettyPrinter.termPrinter(term, defaultFormulaPrinter, defaultTermPrinter)

  private def defaultFormulaPrinter(formula: Formula): Option[String] = formula match {
    case LessThan(t1, t2) => Some("(" + apply(t1) + " " + LTSTR + " " + apply(t2) + ")")
    case LessEqual(t1, t2) => Some("(" + apply(t1) + " " + LESTR + " " + apply(t2) + ")")
    case GreaterThan(t1, t2) => Some("(" + apply(t1) + " " + GTSTR + " " + apply(t2) + ")")
    case GreaterEqual(t1, t2) => Some("(" + apply(t1) + " " + GESTR + " " + apply(t2) + ")")
    case _ => None
  }

  private def defaultTermPrinter(term: Term): Option[String] = term match {
    case Num(n) => Some(n.toString)
    case Var(id) => Some(id)
    case Add(ts) => Some(ts.map(apply).mkString("(", " " + ADDSTR + " ", ")"))
    case Sub(t1, t2) => Some("(" + apply(t1) +  " " + SUBSTR + " " + apply(t2) + ")")
    case Mul(ts) => Some(ts.map(apply).mkString("(", MULSTR, ")"))
    case Div(t1, t2) => Some("(" + apply(t1) +  " " + DIVSTR + " " + apply(t2) + ")")
    case Pow(t1, t2) => Some("(" + apply(t1) +  " " + POWSTR + " " + apply(t2) + ")")
    case _ => None
  }

}
