package regolic.smt.parser

import SMTLIB1Trees._

object Printer {

  def apply(bench: Benchmark): String = {

/*
    val (name, logic, status, extrafuns, extrapreds, annotations, assumptions, formula) = 
      (bench.name, bench.logic, bench.status, bench.extraFuns, bench.extraPreds, bench.annotations, bench.assumptions, bench.formula)

    def printAttribute(attribute: BenchAttribute): String = (attribute match {
      case l: LogicAttribute => ":logic " + (l match {
        case QF_BV => "QF_BV"
        case QF_FP => "QF_FP"
        case QF_LIA => "QF_LIA"
      })
      case s: StatusAttribute => ":status " + (s match {
        case Sat => "sat"
        case Unsat => "unsat"
        case Unknown => "unknown"
      })
      case ExtraFunsAttribute(symbols) => ":extrafuns (" + (symbols.foldLeft(""){case (a,s) => a + " " + printExtraFunSymbol(s)}) + ")"
      case ExtraPredsAttribute(symbols) => ":extrapreds (" + (symbols.foldLeft(""){case (a,s) => a + " " + printExtraPredSymbol(s)}) + ")"
      case AnnotationAttribute(attribute, o) => ":" + attribute + (o match {
          case Some(s) => " {" + s + "}"
          case None => ""
        })
      case AssumptionAttribute(formula) => ":assumption " + printFormula(formula)
      case FormulaAttribute(formula) => ":formula " + printFormula(formula)
    }) + "\n"

    def printFormula(formula: Formula): String = logic match {
      case QF_LIA => asts.theories.qflia.printers.SMTLIBPrinter(formula)
    }

    def printSort(sort: Sort): String = logic match {
      case QF_LIA => asts.theories.qflia.printers.SMTLIBPrinter.sortPrinter(sort)
    }

    def printExtraPredSymbol(predSymbol: PredicateSymbol): String = (predSymbol.argSorts.map(printSort)).mkString("(" + predSymbol.name + " ", " ", ")") 

    def printExtraFunSymbol(funSymbol: FunctionSymbol): String = (funSymbol.argSorts.map(printSort)).mkString("(" + funSymbol.name + " ", " ", " " + printSort(funSymbol.returnSort) + ")")

    ("(benchmark " + name + "\n\n" +
      printAttribute(logic) + "\n" + (status match {
        case Some(st) => printAttribute(st) + "\n"
        case None => ""
      }) + "\n" +
      ((extrafuns.map(printAttribute)).mkString("")) + "\n" +
      ((extrapreds.map(printAttribute)).mkString("")) + "\n\n" +
      ((annotations.map(printAttribute)).mkString("")) + "\n\n" +
      ((assumptions.map(printAttribute)).mkString("")) + "\n\n" +
      printAttribute(formula) + "\n)")
      */
      sys.error("not supported")
  }

}
