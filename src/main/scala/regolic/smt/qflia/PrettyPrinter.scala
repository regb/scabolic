package regolic.smt.qflia

import Trees._

object PrettyPrinter {

/*
  def apply(form: Formula): String = asts.fol.printers.PrettyPrinter.termPrinter(term, defaultFormulaPrinter, defaultTermPrinter)
  def apply(term: Term): String = asts.fol.printers.PrettyPrinter.termPrinter(term, defaultFormulaPrinter, defaultTermPrinter)

  private def defaultFormulaPrinter(formula: FolT.Formula): Option[String] = formula match {
    case LessThan(t1, t2) => Some("(" + apply(t1) + LTSTR + apply(t2) + ")")
    case LessEqual(t1, t2) => Some("(" + apply(t1) + LESTR + apply(t2) + ")")
    case GreaterThan(t1, t2) => Some("(" + apply(t1) + GTSTR + apply(t2) + ")")
    case GreaterEqual(t1, t2) => Some("(" + apply(t1) + GESTR + apply(t2) + ")")
    case _ => None
  }

  private def defaultTermPrinter(term: Term): Option[String] = term match {
    case Add(ts) => Some(ts.map(apply).mkString("(", ADDSTR, ")"))
    case Sub(t1, t2) => Some("(" + apply(t1) + SUBSTR + apply(t2) + ")")
    case Mul(t, n) => Some("(" + apply(t) + MULSTR + n + ")")
    case _ => None
  }
  */

}
