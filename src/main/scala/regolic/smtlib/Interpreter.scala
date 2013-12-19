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

import java.io.OutputStream
import java.io.FileOutputStream
import java.io.PrintStream

/*
 * We assume symbols declaration are valid at the top level and are not scope (stack/frame) specific
 * (Even Z3 is not supporting that)
 * Though, we might want to actually support this as that is the standard and may not be that difficult to implement
 *
 * :print-success is at false by default, although the SMTLIB standard seems to assume it to be true by default. It seems more reasonnable to not print 'success' on each command
 */
class Interpreter(implicit val context: Context) {

  private var logger = context.logger
  private implicit val tag = Logger.Tag("SMTLIB Interpreter")

  private var funSymbols: Map[String, FunctionSymbol] = Map()
  private var predSymbols: Map[String, PredicateSymbol] = Map()

  private val solver = new cafesat.Solver
  private var expectedResult: Option[Boolean] = None

  private var regularOutput: PrintStream = System.out
  private var loggingOutput: PrintStream = System.err

  private var printSuccess: Boolean = false

  //make a new logger according to current SMT options
  //private val: Logger = new Logger {
  //  override def output(msg: String): Unit = loggingOutput.println(msg)



  //}

  def eval(command: Command): CommandResponse = {
    logger.info("Evaluating command: " + command)
    val res = command match {
      case SetLogic(QF_UF) => Success
      case SetLogic(_) => Unsupported
      case DeclareSort(SSymbol(name), arity) => Success
      case DeclareFun(SSymbol(name), sorts, sort) => {
        val paramSorts = sorts map parseSort
        val returnSort = parseSort(sort)
        if(returnSort == TSort("BOOL", List()))
          predSymbols += (name -> PredicateSymbol(name, paramSorts.toList))
        else
          funSymbols += (name -> FunctionSymbol(name, paramSorts.toList, returnSort))
        Success
      }
      case Pop(n) => {
        try {
          solver.pop(n)
          Success
        } catch {
          case (e: Exception) => Error("Cannot pop " + n + " scope frames")
        }
      }
      case Push(n) => {
        (1 to n).foreach(_ => solver.push())
        Success
      }
      case Assert(f) => {
        solver.assertCnstr(parseFormula(f, Map()))
        Success
      }
      case SetInfo(attr) => evalAttribute(attr)
      case SetOption(option) => evalOption(option)
      case CheckSat => {
        val result = solver.check()
        result match {
          case Some(true) => {
            if(expectedResult == Some(false))
              Error("result is sat, but :status info requires unsat")
            else
              SatStatus
          }           
          case Some(false) if expectedResult == Some(true) =>
            Error("result is unsat, but :status info requires sat")
          case Some(false) =>
            UnsatStatus
          case None => 
            UnknownStatus
        }
      }
      case Exit => {
        sys.exit()
        Success
      }
      case cmd => {
        logger.warning("Ignoring unsuported command: " + cmd)
        Unsupported
      }
    }
    logger.info("Command response: " + res)
    if(res != Success || printSuccess)
      regularOutput.println(res)
    res
  }

  private def evalOption(option: SMTOption): CommandResponse = option match {
    case RegularOutputChannel(channel) => {
      if(channel == "stdout") {
        regularOutput = System.out
        Success
      } else {
        try {
          //TODO: close regularOutput if not stdout/stderr
          val tmp = new PrintStream(new FileOutputStream(channel))
          regularOutput = tmp
          Success
        } catch {
          case (e: Exception) => {
            logger.warning("Could not open regular output file <" + channel + ">: " + e.getMessage)
            Error("Could not set regular output at: " + channel)
          }
        }
      }

    }
    case PrintSuccess(bv) => {
      printSuccess = bv
      Success
    }
    case _ => {
      logger.warning("ignoring unsupported option: " + option)
      Unsupported
    }
    
  }
  private def evalAttribute(attr: Attribute): CommandResponse = attr match {
    case Attribute("STATUS", Some(SSymbol("SAT"))) => {
      if(expectedResult != None)
        logger.warning("Setting status multiple times")
      expectedResult = Some(true)
      Success
    }
    case Attribute("STATUS", Some(SSymbol("UNSAT"))) => {
      if(expectedResult != None)
        logger.warning("Setting status multiple times")
      expectedResult = Some(false)
      Success
    }
    case Attribute("STATUS", v) => {
      logger.warning("set-info status set to unsupported value: " + v)
      expectedResult = None
      Error("set-info :status with invalid value: " + v)
    }
    case Attribute("SOURCE", Some(SSymbol(src))) => {
      Success
    }
    case Attribute("SMT-LIB-VERSION", Some(SDouble(ver))) => {
      Success
    }
    case Attribute("CATEGORY", Some(SString(cat))) => {
      Success
    }
    case Attribute(key, value) => {
      logger.warning("Ignoring unsupported set-info attribute with key: " + key + " and value: " + value)
      Unsupported
    }
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
      interpreter.eval(command)
    }
  }

}
