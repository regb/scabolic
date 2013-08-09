package regolic
package printers

import asts.core.Trees._

object SmtLib2 {

  import sexpr.SExprs._

  def toSExpr(f: Formula): SExpr = f match {
    case ConnectiveApplication(sym, args) => SList(SSymbol(sym.name) :: args.map(toSExpr))
    case PredicateApplication(sym, args) => SList(SSymbol(sym.name) :: args.map(toSExpr))
    case QuantifierApplication(sym, v, f) => sys.error("unsupported: " + f)
  }

  def toSExpr(t: Term): SExpr = t match {
    case FunctionApplication(sym, args) => SList(SSymbol(sym.name) :: args.map(toSExpr))
    case ITE(c, t, e) => SList(SSymbol("ite"), toSExpr(c), toSExpr(t), toSExpr(e))
    case Variable(name, _) => SSymbol(name)
    case TermQuantifierApplication(sym, v, ts) => sys.error("unsupported: " + t)
  }

  def apply(f: Formula): String = {
    sexpr.PrettyPrinter(toSExpr(f))
  }

}
