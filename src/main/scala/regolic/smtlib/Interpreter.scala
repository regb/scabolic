package regolic
package smtlib

import scala.collection.TraversableOnce

import regolic.asts.core.Trees.{Sort => TSort, _}
import regolic.asts.fol.Trees._
import regolic.asts.theories.int.{Trees => IntTrees}
import regolic.asts.theories.real.{Trees => RealTrees}
import regolic.asts.theories.array.{Trees => ArrayTrees}

import regolic.sexpr
import regolic.sexpr.SExprs._

import util.Logger

import Commands._

/*
 * We assume symbols declaration are valid at the top level and are not scope (stack/frame) specific
 * (Even Z3 is not supporting that)
 * Though, we might want to actually support this as that is the standard and may not be that difficult to implement
 */
class Interpreter(implicit val context: Context) {

  private val logger = context.logger
  private implicit val tag = Logger.Tag("SMTLIB Interpreter")

  private var funSymbols: Map[String, FunctionSymbol] = Map()
  private var predSymbols: Map[String, PredicateSymbol] = Map()

  private val solver = new cafesat.Solver
  private var expectedResult: Option[Boolean] = None

  def eval(command: Command): CommandResponse = {
    logger.info("Evaluating command: " + command)
    val res = command match {
      case SetLogic(_) => ()
      case DeclareSort(SSymbol(name), arity) => ()
      case DeclareFun(SSymbol(name), sorts, sort) => {
        val paramSorts = sorts map parseSort
        val returnSort = parseSort(sort)
        if(returnSort == TSort("BOOL", List()))
          predSymbols += (name -> PredicateSymbol(name, paramSorts.toList))
        else
          funSymbols += (name -> FunctionSymbol(name, paramSorts.toList, returnSort))
      }
      case Pop(n) => solver.pop(n)
      case Push(n) => (1 to n).foreach(_ => solver.push())
      case Assert(f) => solver.assertCnstr(parseFormula(f, Map()))
      case SetInfo(attr) => attr match {
        case Attribute("STATUS", Some(SSymbol("SAT"))) => {
          if(expectedResult != None)
            logger.warning("Setting status multiple times")
          expectedResult = Some(true)
        }
        case Attribute("STATUS", Some(SSymbol("UNSAT"))) => {
          if(expectedResult != None)
            logger.warning("Setting status multiple times")
          expectedResult = Some(false)
        }
        case Attribute("STATUS", v) => {
          logger.warning("set-info status set to unsupported value: " + v)
          expectedResult = None
        }
        case Attribute("SOURCE", Some(SSymbol(src))) => ()
        case Attribute("SMT-LIB-VERSION", Some(SDouble(ver))) => ()
        case Attribute("CATEGORY", Some(SString(cat))) => ()
        case Attribute(key, value) =>
          logger.warning("unsupported set-info attribute with key: " + key + " and value: " + value)
      }
      case CheckSat => {
        val result = solver.check()
        val resultString = result match {
          case Some(true) => {
            if(expectedResult == Some(false))
              "sat | should be unsat"
            else
              "sat"
          }           
          case Some(false) if expectedResult == Some(true) => "unsat | should be sat"
          case Some(false) => "unsat"
          case None => "unknown"
        }
        println(resultString)
      }
      case Exit => {
        sys.exit()
      }
      case cmd =>
        logger.warning("Ignoring unsuported command: " + cmd)
    }
    logger.info("Result is: " + res)
    null
  }

  private def parseSort(sExpr: SExpr): TSort = sExpr match {
    case SSymbol(s) => TSort(s, List())
    case SList(SSymbol(s) :: ss) => TSort(s, ss map parseSort)
    case _ => sys.error("Error in parseSort: unexpected sexpr: " + sExpr)
  }

  def parseVarBindings(bindings: List[SExpr], scope: Map[String, Either[Formula, Term]]): Map[String, Either[Formula, Term]] =
    bindings.map{ case SList(List(SSymbol(v), t)) => (v, parseFormulaTerm(t, scope)) }.toMap

  def parseFormulaTerm(sExpr: SExpr, scope: Map[String, Either[Formula, Term]]): Either[Formula, Term] = {
    try {
      Left(parseFormula(sExpr, scope))
    } catch {
      case (ex: Throwable) => Right(parseTerm(sExpr, scope))
    }
  }

  def parseFormula(sExpr: SExpr, scope: Map[String, Either[Formula, Term]]): Formula = sExpr match {
    case SList(List(SSymbol("LET"), SList(varBindings), t)) => {
      val newMap = parseVarBindings(varBindings, scope)
      parseFormula(t, scope ++ newMap)
    }
    case SSymbol("TRUE") => True()
    case SSymbol("FALSE") => False()
    case SSymbol(sym) => scope.get(sym) match {
      case None => PredicateApplication(predSymbols(sym), List())
      case Some(Left(f)) => f
      case Some(Right(t)) => sys.error("unexpected term in formula variable: " + t)
    }
    case SList(List(SSymbol("NOT"), t)) => Not(parseFormula(t, scope))
    case SList(SSymbol("AND") :: ts) => And(ts.map(parseFormula(_, scope)))
    case SList(SSymbol("OR") :: ts) => Or(ts.map(parseFormula(_, scope)))
    case SList(List(SSymbol("=>"), t1, t2)) => Implies(parseFormula(t1, scope), parseFormula(t2, scope))
    case SList(List(SSymbol("ITE"), t1, t2, t3)) => 
      IfThenElse(parseFormula(t1, scope), parseFormula(t2, scope), parseFormula(t3, scope))
    //TODO: xor
    case SList(SSymbol("DISTINCT") :: ss) => {
      val ts = ss.map(s => parseTerm(s, scope))
      And(ts.tails.flatMap(subSeqs => 
        if(subSeqs.isEmpty) Nil 
        else subSeqs.tail.map(t => Not(Equals(subSeqs.head, t)))
      ).toList)
    }
    case SList(SSymbol(pred) :: ts) => applyPredicateSymbol(pred, ts.map(parseTerm(_, scope)))
  }

  def parseTerm(sExpr: SExpr, scope: Map[String, Either[Formula, Term]]): Term = sExpr match {
    case SList(List(SSymbol("LET"), SList(varBindings), t)) => {
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
      case _ => predSymbols(sym)
    }

    PredicateApplication(predSym, args.toList)
  }

}


object Interpreter {

  /*
   * Execute the Script and output results on stdout
   */
  def execute(commands: TraversableOnce[Command])(implicit context: Context): Unit = {
    val interpreter = new Interpreter
    for(command <- commands) {
      val res = interpreter.eval(command)
      //TODO: if printable
      println(res)
    }
  }

}
