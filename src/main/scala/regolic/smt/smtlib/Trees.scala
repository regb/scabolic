package regolic.smt.smtlib

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.HashMap
import regolic.asts.core.Trees._

object Trees {

  case class Benchmark(name: String, attributes: List[BenchAttribute]) {

    private var _logic: Option[LogicAttribute] = None
    private var _status: Option[StatusAttribute] = None
    private var _extraFuns: ListBuffer[ExtraFunsAttribute] = new ListBuffer[ExtraFunsAttribute]
    private var _extraPreds: ListBuffer[ExtraPredsAttribute] = new ListBuffer[ExtraPredsAttribute]
    private var _extraSorts: ListBuffer[ExtraSortsAttribute] = new ListBuffer[ExtraSortsAttribute]
    private var _assumptions: ListBuffer[AssumptionAttribute] = new ListBuffer[AssumptionAttribute]
    private var _formula: Option[FormulaAttribute] = None
    private var _annotations: ListBuffer[AnnotationAttribute] = new ListBuffer[AnnotationAttribute]

    attributes.foreach{
      case (l: LogicAttribute) => if(_logic == None) _logic = Some(l) else throw new Exception("Only one logic attribute allowed")
      case (st: StatusAttribute) => if(_status == None) _status = Some(st) else throw new Exception("Only one status attribute allowed")
      case (ef: ExtraFunsAttribute) => _extraFuns.append(ef)
      case (ep: ExtraPredsAttribute) => _extraPreds.append(ep)
      case (es: ExtraSortsAttribute) => _extraSorts.append(es)
      case (as: AssumptionAttribute) => _assumptions.append(as)
      case (f: FormulaAttribute) => if(_formula == None) _formula = Some(f) else throw new Exception("Only one formula attribute allowed")
      case (an: AnnotationAttribute) => _annotations.append(an)
    }

    /* check the benchmark is well formed */
    if(_logic == None) throw new Exception("Logic not set")
    if(_formula == None) throw new Exception("Formula not set")

    lazy val logic: LogicAttribute = _logic.get
    lazy val status: Option[StatusAttribute] = _status
    lazy val extraFuns: List[ExtraFunsAttribute] = _extraFuns.toList
    lazy val extraPreds: List[ExtraPredsAttribute] = _extraPreds.toList
    lazy val extraSorts: List[ExtraSortsAttribute] = _extraSorts.toList
    lazy val assumptions: List[AssumptionAttribute] = _assumptions.toList
    lazy val formula: FormulaAttribute = _formula.get 
    lazy val annotations: List[AnnotationAttribute] = _annotations.toList


    def getFormula: Formula = formula.formula

    def getAssumptions: List[Formula] = assumptions.map(a => a.formula)

    def getExtraFunsSymbols: List[FunctionSymbol] = extraFuns.flatMap{case ExtraFunsAttribute(symbs) => symbs}

  }

  trait BenchAttribute

  trait LogicAttribute extends BenchAttribute
  case object QF_BV extends LogicAttribute
  case object QF_FP extends LogicAttribute
  case object QF_LIA extends LogicAttribute

  trait StatusAttribute extends BenchAttribute
  case object Sat extends StatusAttribute
  case object Unsat extends StatusAttribute
  case object Unknown extends StatusAttribute

  case class ExtraFunsAttribute(symbols: List[FunctionSymbol]) extends BenchAttribute
  case class ExtraPredsAttribute(symbols: List[PredicateSymbol]) extends BenchAttribute
  case class ExtraSortsAttribute(sorts: List[Sort]) extends BenchAttribute

  case class AssumptionAttribute(formula: Formula) extends BenchAttribute
  case class FormulaAttribute(formula: Formula) extends BenchAttribute

  case class AnnotationAttribute(attribute: String, userValue: Option[String]) extends BenchAttribute

}
