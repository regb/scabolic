package regolic.asts.theories.int

import Trees._
import regolic.asts.core.Trees.{Term, Formula}

object PrettyPrinter {

  private val LTSTR  = " < "
  private val LESTR  = " \u2264 "
  private val GTSTR  = " > "
  private val GESTR  = " \u2265 "
  private val ADDSTR = " + "
  private val SUBSTR = " - "
  private val MULSTR = " * "

  def apply(term: Term): String = regolic.asts.fol.PrettyPrinter.termPrinter(term, defaultFormulaPrinter, defaultTermPrinter)

  private def defaultFormulaPrinter(formula: Formula): Option[String] = formula match {
    case LessThan(t1, t2) => Some("(" + apply(t1) + LTSTR + apply(t2) + ")")
    case LessEqual(t1, t2) => Some("(" + apply(t1) + LESTR + apply(t2) + ")")
    case GreaterThan(t1, t2) => Some("(" + apply(t1) + GTSTR + apply(t2) + ")")
    case GreaterEqual(t1, t2) => Some("(" + apply(t1) + GESTR + apply(t2) + ")")
    case _ => None
  }

  private def defaultTermPrinter(term: Term): Option[String] = term match {
    case Add(ts) => Some(ts.map(apply).mkString("(", ADDSTR, ")"))
    case Sub(t1, t2) => Some("(" + apply(t1) + SUBSTR + apply(t2) + ")")
    case Mul(ts) => Some(ts.map(apply).mkString("(", MULSTR, ")"))
    case MulConst(t, n) => Some("(" + apply(t) + MULSTR + n + ")")
    case _ => None
  }

}
