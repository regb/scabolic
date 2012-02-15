package regolic.smt.smtlib

import Trees._

object SMTLIBPrinter {

/*
  def apply(formula: Formula): String = formulaPrinter(formula, _ => None, _ => None)
  def apply(term: Term): String = termPrinter(term, _ => None, _ => None)

  def formulaPrinter(formula: Formula, dfp: (Formula) => Option[String], dtp: (Term) => Option[String]): String = {
    def fdfp(f: Formula): Option[String] = dfp(f) match {
      case o@Some(s) => o
      case None => defaultFormulaPrinter(f, dfp, dtp)
    }
    def fdtp(t: Term): Option[String] = dtp(t) match {
      case o@Some(s) => o
      case None => defaultTermPrinter(t, dfp, dtp)
    }
    PrefixPrinter.formulaPrinter(formula, fdfp, fdtp)
  }
  def termPrinter(term: Term, dfp: (Formula) => Option[String], dtp: (Term) => Option[String]): String = {
    def fdfp(f: Formula): Option[String] = dfp(f) match {
      case o@Some(s) => o
      case None => defaultFormulaPrinter(f, dfp, dtp)
    }
    def fdtp(t: Term): Option[String] = dtp(t) match {
      case o@Some(s) => o
      case None => defaultTermPrinter(t, dfp, dtp)
    }
    PrefixPrinter.termPrinter(term, fdfp, fdtp)
  }

  private def defaultFormulaPrinter(formula: Formula, dfp: (Formula) => Option[String], dtp: (Term) => Option[String]): Option[String] = formula match {
    case FVariable(n) => Some("$" + n)
    case _ => None
  }

  private def defaultTermPrinter(term: Term, dfp: (Formula) => Option[String], dtp: (Term) => Option[String]): Option[String] = term match {
    case Variable(n, _) => Some("?" + n)
    case _ => None
  }
  */
}
