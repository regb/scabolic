package regolic
package printers

import asts.core.Trees._

//object SmtLib2 {
//
//  import sexpr.SExprs._
//
//  def toSExpr(f: Formula): SExpr = f match {
//    case ConnectiveApplication(sym, args) => SList(SSymbol(sym.name) :: args.map(toSExpr))
//    case PredicateApplication(sym, args) => SList(SSymbol(sym.name) :: args.map(toSExpr))
//    case QuantifierApplication(sym, v, f) => sys.error("unsupported: " + f)
//  }
//
//  def toSExpr(t: Term): SExpr = t match {
//    case FunctionApplication(sym, args) => SList(SSymbol(sym.name) :: args.map(toSExpr))
//    case ITE(c, t, e) => SList(SSymbol("ite"), toSExpr(c), toSExpr(t), toSExpr(e))
//    case Variable(name, _) => SSymbol(name)
//    case TermQuantifierApplication(sym, v, ts) => sys.error("unsupported: " + t)
//  }
//
//  def apply(f: Formula): String = {
//    sexpr.PrettyPrinter(toSExpr(f))
//  }
//
//  def litToSExpr(lit: dpllt.Literal): SExpr = {
//    def transformLit(lit: dpllt.Literal): SExpr = lit match {
//      case dpllt.PropositionalLiteral(id, 1) => 
//        SSymbol("p_" + id) 
//      case smt.qfeuf.Literal(Left((a, b)), _, true, _) => 
//        SList(List(SSymbol("="), SSymbol("c_" + a), SSymbol("c_" + b)))
//      case smt.qfeuf.Literal(Right((f, a, b)), _, true, _) => 
//        SList(List(SSymbol("="), 
//                   SList(List(SSymbol("apply"), SSymbol("c_" + f), SSymbol("c_" + a))),
//                   SSymbol("c_" + b)))
//    }
//    if(lit.polarity) 
//      transformLit(lit) 
//    else
//      SList(List(SSymbol("not"), transformLit(lit.pos)))
//  }
//
//  def conjunctionToSExpr(lits: Set[dpllt.Literal]): SExpr = {
//    if(lits.isEmpty) SSymbol("true") else SList(SSymbol("and") :: lits.toList.map(lit => litToSExpr(lit)))
//  }
//
//  def cnfToSExpr(clauses: Set[Set[dpllt.Literal]]): SExpr = {
//    SList(SSymbol("and") :: clauses.toList.map(clause => 
//      SList(SSymbol("or") :: clause.toList.map(lit => litToSExpr(lit)))))
//  }
//
//  def cnf(clauses: Set[Set[dpllt.Literal]]): String = sexpr.PrettyPrinter(cnfToSExpr(clauses))
//  def conjunction(lits: Set[dpllt.Literal]): String = sexpr.PrettyPrinter(conjunctionToSExpr(lits))
//
//}
