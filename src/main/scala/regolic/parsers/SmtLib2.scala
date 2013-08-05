package regolic.parsers

import scala.collection.mutable.ListBuffer

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.asts.theories.int.{Trees => IntTrees}
import regolic.asts.theories.real.{Trees => RealTrees}
import regolic.asts.theories.array.{Trees => ArrayTrees}

import regolic.sexpr
import regolic.sexpr.SExprs._

object SmtLib2 {

  object Trees {
    sealed abstract class Command
    case class SetLogic(logic: Logic) extends Command
    case class Assert(formula: Formula) extends Command
    case class Push(n: Int) extends Command
    case class Pop(n: Int) extends Command
    case object CheckSat extends Command
    case object Exit extends Command

    sealed abstract trait Logic
    case object QF_UF extends Logic
    case object QF_LRA extends Logic
    case object QF_AX extends Logic
    case object QF_A extends Logic

    object Logic {
      def fromString(logic: String): Logic = logic match {
        case "QF_UF"  => QF_UF
        case "QF_LRA" => QF_LRA
        case "QF_AX"  => QF_AX
        case "QF_A"   => QF_A
      }
    }
  }

  import Trees._

  private var funSymbols: Map[String, FunctionSymbol] = Map()

  def apply(input: java.io.Reader): List[Command] = {

    funSymbols = Map()

    val l = new sexpr.Lexer(input)
    val p = new sexpr.Parser(l)

    var cmds: ListBuffer[Command] = ListBuffer()

    var expr = p.parse
    while(expr != null) {

      expr match {
        case SList(List(SSymbol("set-logic"), SSymbol(logic))) => 
          cmds.append(SetLogic(Logic.fromString(logic)))
        case SList(List(SSymbol("declare-sort"), SSymbol(sort), SInt(arity))) => 
          ()
        case SList(List(SSymbol("declare-fun"), SSymbol(fun), SList(sorts), sort)) => {
          val paramSorts = sorts map parseSort
          val returnSort = parseSort(sort)
          funSymbols += (fun -> FunctionSymbol(fun, paramSorts, returnSort))
        }
        case SList(List(SSymbol("assert"), term)) =>
          cmds.append(Assert(parseFormula(term)))
        case SList(List(SSymbol("check-sat"))) =>
          cmds.append(CheckSat)
        case SList(List(SSymbol("exit"))) =>
          cmds.append(Exit)

      //case push: PushCommand => {
      //  val n = push.numeral_.toInt
      //  cmds.append(Push(n))
      //}
      //case pop: PopCommand => {
      //  val n = pop.numeral_.toInt
      //  cmds.append(Pop(n))
      //}
        case _ => ()
      }

      expr = p.parse
    }

    cmds.toList
  }

  private def parseSort(sExpr: SExpr): Sort = sExpr match {
    case SSymbol(s) => Sort(s, List())
    case SList(SSymbol(s) :: ss) => Sort(s, ss map parseSort)
    case _ => sys.error("Error in parseSort: unexpected sexpr: " + sExpr)
  }

  def parseFormula(sExpr: SExpr): Formula = sExpr match {
    case SSymbol("true") => True()
    case SSymbol("false") => False()
    case SList(List(SSymbol("not"), t)) => Not(parseFormula(t))
    case SList(SSymbol("and") :: ts) => And(ts map parseFormula)
    case SList(SSymbol("or") :: ts) => Or(ts map parseFormula)
    case SList(List(SSymbol("=>"), t1, t2)) => Implies(parseFormula(t1), parseFormula(t2))
    case SList(List(SSymbol("ite"), t1, t2, t3)) => IfThenElse(parseFormula(t1), parseFormula(t2), parseFormula(t3))
    case SList(SSymbol(pred) :: ts) => applyPredicateSymbol(pred, ts map parseTerm)
  }

  def parseTerm(sExpr: SExpr): Term = sExpr match {
    case SList(SSymbol(fun) :: ts) => applyFunctionSymbol(fun, ts map parseTerm)
    case SInt(n) => IntTrees.Num(n)
    case SDouble(d) => RealTrees.Num(d)
    case SSymbol(sym) => Variable(sym, funSymbols(sym).returnSort)
  }

  def applyFunctionSymbol(sym: String, args: Seq[Term]): FunctionApplication = {

    val funSym = sym match {
      case "+" => args(0).sort match {
        case IntTrees.IntSort() => IntTrees.AddSymbol(args.size)
        case RealTrees.RealSort() => RealTrees.AddSymbol(args.size)
      }
      case "*" => args(0).sort match {
        case IntTrees.IntSort() => IntTrees.MulSymbol(args.size)
        case RealTrees.RealSort() => RealTrees.MulSymbol(args.size)
      }
      case "-" => args(0).sort match {
        case IntTrees.IntSort() => if(args.size == 1) IntTrees.NegSymbol() else IntTrees.SubSymbol()
        case RealTrees.RealSort() => if(args.size == 1) RealTrees.NegSymbol() else RealTrees.SubSymbol()
      }
      case "div" => args(0).sort match {
        case IntTrees.IntSort() => IntTrees.DivSymbol()
        case RealTrees.RealSort() => RealTrees.DivSymbol()
      }
      case "mod" => IntTrees.ModSymbol()
      case "abs" => IntTrees.AbsSymbol()
      case "select" => {
        val ArrayTrees.ArraySort(from, to) = args(0).sort
        ArrayTrees.SelectSymbol(from, to)
      }
      case "store" => ArrayTrees.StoreSymbol(args(1).sort, args(2).sort)
      case _ => funSymbols(sym)
    }

    FunctionApplication(funSym, args.toList)
  }

  def applyPredicateSymbol(sym: String, args: Seq[Term]): PredicateApplication = {

    //TODO: make sure second args type match first one
    val predSym = sym match {
      case "<" => args(0).sort match {
        case IntTrees.IntSort() => IntTrees.LessThanSymbol()
        case RealTrees.RealSort() => RealTrees.LessThanSymbol()
      }
      case "<=" => args(0).sort match {
        case IntTrees.IntSort() => IntTrees.LessEqualSymbol()
        case RealTrees.RealSort() => RealTrees.LessEqualSymbol()
      }
      case ">" => args(0).sort match {
        case IntTrees.IntSort() => IntTrees.GreaterThanSymbol()
        case RealTrees.RealSort() => RealTrees.GreaterThanSymbol()
      }
      case ">=" => args(0).sort match {
        case IntTrees.IntSort() => IntTrees.GreaterEqualSymbol()
        case RealTrees.RealSort() => RealTrees.GreaterEqualSymbol()
      }
      case "=" => EqualsSymbol(args(0).sort)
    }

    PredicateApplication(predSym, args.toList)
  }


}
