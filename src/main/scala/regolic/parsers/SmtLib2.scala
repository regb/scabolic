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
          cmds.append(Assert(parseFormula(term, Map())))
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

  def parseVarBindings(bindings: List[SExpr], scope: Map[String, Either[Formula, Term]]): Map[String, Either[Formula, Term]] =
    bindings.map{ case SList(List(SSymbol(v), t)) => (v, parseFormulaTerm(t, scope)) }.toMap

  def parseFormulaTerm(sExpr: SExpr, scope: Map[String, Either[Formula, Term]]): Either[Formula, Term] = {
    try {
      Left(parseFormula(sExpr, scope))
    } catch {
      case (_: Throwable) => Right(parseTerm(sExpr, scope))
    }
  }

  def parseFormula(sExpr: SExpr, scope: Map[String, Either[Formula, Term]]): Formula = sExpr match {
    case SList(List(SSymbol("let"), SList(varBindings), t)) => {
      val newMap = parseVarBindings(varBindings, scope)
      parseFormula(t, scope ++ newMap)
    }
    case SSymbol("true") => True()
    case SSymbol("false") => False()
    case SSymbol(sym) => scope.get(sym) match {
      case None => sys.error("no def for variable: " + sym)
      case Some(Left(f)) => f
      case Some(Right(t)) => sys.error("unexpected term in formula variable: " + t)
    }
    case SList(List(SSymbol("not"), t)) => Not(parseFormula(t, scope))
    case SList(SSymbol("and") :: ts) => And(ts.map(parseFormula(_, scope)))
    case SList(SSymbol("or") :: ts) => Or(ts.map(parseFormula(_, scope)))
    case SList(List(SSymbol("=>"), t1, t2)) => Implies(parseFormula(t1, scope), parseFormula(t2, scope))
    case SList(List(SSymbol("ite"), t1, t2, t3)) => 
      IfThenElse(parseFormula(t1, scope), parseFormula(t2, scope), parseFormula(t3, scope))
    //TODO: xor
    case SList(SSymbol("distinct") :: ss) => {
      val ts = ss.map(s => parseTerm(s, scope))
      And(ts.tails.flatMap(subSeqs => 
        if(subSeqs.isEmpty) Nil 
        else subSeqs.tail.map(t => Not(Equals(subSeqs.head, t)))
      ).toList)
    }
    case SList(SSymbol(pred) :: ts) => applyPredicateSymbol(pred, ts.map(parseTerm(_, scope)))
  }

  def parseTerm(sExpr: SExpr, scope: Map[String, Either[Formula, Term]]): Term = sExpr match {
    case SList(List(SSymbol("let"), SList(varBindings), t)) => {
      val newMap = parseVarBindings(varBindings, scope)
      parseTerm(t, scope ++ newMap)
    }
    case SList(SSymbol(fun) :: ts) => applyFunctionSymbol(fun, ts.map(parseTerm(_, scope)))
    case SInt(n) => IntTrees.Num(n)
    case SDouble(d) => RealTrees.Num(d)
    case SSymbol(sym) => scope.get(sym) match {
      case None => Variable(sym, funSymbols(sym).returnSort)
      case Some(Right(t)) => t
      case Some(Left(f)) => sys.error("unexpected formula in term variable: " + f)
    }
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
