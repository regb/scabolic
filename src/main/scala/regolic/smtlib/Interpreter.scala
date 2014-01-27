package regolic
package smtlib

import regolic.asts.core.Trees.{Sort => TSort, _}
import regolic.asts.fol.Trees._
import regolic.asts.theories.int.{Trees => IntTrees}
import regolic.asts.theories.real.{Trees => RealTrees}
import regolic.asts.theories.array.{Trees => ArrayTrees}

import util.Logger

import _root_.smtlib.{Interpreter => AbstractInterpreter, _}
import Commands._
import CommandResponses._
import sexpr.SExprs._

import java.io.OutputStream
import java.io.FileOutputStream
import java.io.PrintStream

/*
 * We assume symbols declaration are valid at the top level and are not scope (stack/frame) specific
 * (Even Z3 is not supporting that)
 * Though, we might want to actually support this as that is the standard and may not be that difficult to implement
 *
 * Note that despite returning the command response, the interpreter should handle the printing
 * of those responses itself. That is because it needs to handle the verbosity and *-output-channel
 * options commands, and will do the correct printing depending on the internal state.
 * The responses are returned as a way to progamatically communicate with a solver.
 */
class Interpreter(implicit val context: Context) extends AbstractInterpreter {

  /*
   * TODO: ignoring logger from context because the SMTLIB scripting language provides option
   * to configure its own, as well as standard defaults. How to make it more configurable by still
   * using the context ?
   */

  /*
   * TODO: it should be an error not to define logic, only set/get-info and set/get-option and exit
   * are allowed (according to the standard) before a set-logic. Z3 allows to skip the set-logic.
   */
  private var logic: Option[Logic] = None

  /*
   * Standard options
   */
  private var interactiveMode: Boolean = false
  //Default (standard) is true unless a Settings overwrite it
  private var printSuccess: Boolean = Settings.printSuccess.getOrElse(true)

  private var funSymbols: Map[String, FunctionSymbol] = Map()
  private var predSymbols: Map[String, PredicateSymbol] = Map()

  private var expectedResult: Option[Boolean] = None

  private var regularOutput: PrintStream = System.out
  private var regularOutputClosable: Option[PrintStream] = None
  private var loggingOutput: PrintStream = System.err
  private var loggingOutputClosable: Option[PrintStream] = None
  private var loggingLevel: Logger.LogLevel = Logger.NoLogging
  def verbosityToLogLevel(verbosity: Int): Logger.LogLevel = verbosity match {
    case 0 => Logger.NoLogging
    case 1 => Logger.Error
    case 2 => Logger.Warning
    case 3 => Logger.Info
    case 4 => Logger.Debug
    case 5 => Logger.Trace
    case n if n < 0 => Logger.NoLogging
    case n if n > 5 => Logger.Trace
  }


  //The logger closes over the current values for logging level and loggingOutput, set by the interpreter.
  //This actually made me change the definition of logLevel in trait Logger from val to def.
  private val logger = new Logger {
    override def output(msg: String): Unit = loggingOutput.println(msg)

    override def logLevel: Logger.LogLevel = loggingLevel
  }
  private implicit val tag = Logger.Tag("SMTLIB Interpreter")

  private val solver = new cafesat.Solver()(context.copy(logger = this.logger))

  override def eval(command: Command): CommandResponse = {
    logger.info("Evaluating command: " + command)
    val res: CommandResponse = command match {
      case SetLogic(log) => logic match {
        case Some(l) => Error("Logic already set to: " + l)
        case None => {
          log match {
            case QF_UF => 
              logic = Some(QF_UF)
              Success
            case l =>
              logger.warning("Unsupported logic: " + l)
              Unsupported
          }
        }
      }
      case DeclareSort(name, arity) => Success
      case DeclareFun(name, sorts, sort) => {
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
      case GetAssertions if interactiveMode => {
        Unsupported //need to stock stack of assertion sets in the interpreter rather than delegating to the solver
      }
      case GetAssertions => {
        logger.warning("get-assertions can only be used in interactive mode")
        Error("get-assertions can only be used in interactive mode")
      }
      case SetInfo(attr) => evalSetInfo(attr)
      case SetOption(option) => evalSetOption(option)
      case CheckSat => {
        val result = solver.check()
        result match {
          case Some(true) => {
            if(expectedResult == Some(false))
              Error("result is sat, but :status info requires unsat")
            else
              CheckSatResponse(SatStatus)
          }           
          case Some(false) if expectedResult == Some(true) =>
            Error("result is unsat, but :status info requires sat")
          case Some(false) =>
            CheckSatResponse(UnsatStatus)
          case None => 
            CheckSatResponse(UnknownStatus)
        }
      }
      case GetOption(option) => evalGetOption(option)
      case GetInfo(flag) => evalGetInfo(flag)
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
    if(res.isInstanceOf[Error]) {
      //the SMT-LIB standard gives two option on error
      //either exit immediately or continue by ignoring the last command.
      //We will attempt to continue while ignoring the error (no change in internal state)
      logger.info("Command led to error. Ignoring command")
    }
    res
  }

  private def evalGetOption(option: String): CommandResponse = option match {
    case "PRINT-SUCCESS" => GetOptionResponse(SBool(printSuccess))
    case _ => {
      logger.info("Ignoring unsuported option: " + option)
      Unsupported
    }
  }

  private def evalGetInfo(infoFlag: InfoFlag): CommandResponse = infoFlag match {
    case ErrorBehaviourInfoFlag =>
      GetInfoResponse(ErrorBehaviourInfoResponse(ContinueExecutionErrorBehaviour), Seq())
    case NameInfoFlag =>
      GetInfoResponse(NameInfoResponse("CafeSat"), Seq())
    case AuthorsInfoFlag =>
      GetInfoResponse(AuthorsInfoResponse("Régis Blanc and Matthias Schlaipfer"), Seq())
    case VersionInfoFlag =>
      GetInfoResponse(VersionInfoResponse("0.01"), Seq())
    case StatusInfoFlag => {//get status is the current status of the solver, ignoring assertions since last check-sat
      //GetInfoResponse(StatusInfoResponse(status), Seq())
      logger.warning("ignoring unsupported info flag: " + infoFlag)
      Unsupported
    }
    case ReasonUnknownInfoFlag => {
      logger.warning("ignoring unsupported info flag: " + infoFlag)
      Unsupported
    }
    case AllStatisticsInfoFlag => {
      logger.warning("ignoring unsupported info flag: " + infoFlag)
      Unsupported
    }
    case KeywordInfoFlag(keyword) => {
      logger.info("ignoring unsupported info flag: " + keyword)
      Unsupported
    }
  }

  private def evalSetOption(option: SMTOption): CommandResponse = option match {
    case PrintSuccess(bv) => {
      printSuccess = bv
      Success
    }
    case ExpandDefinitions(bv) => {
      logger.warning("ignoring unimplementd :expand-definitions option")
      Unsupported
    }
    case InteractiveMode(bv) => {
      /* TODO: maybe can only be invoked at the very beginning ? */
      interactiveMode = bv
      logger.warning("ignoring unimplementd :interactive-mode option")
      Unsupported
    }
    case ProduceProofs(bv) => {
      logger.warning("ignoring unimplementd :produce-proofs option.")
      Unsupported
    }
    case ProduceUnsatCores(bv) => {
      logger.warning("ignoring unimplementd :produce-unsat-cores option.")
      Unsupported
    }
    case ProduceModels(bv) => {
      logger.warning("ignoring unimplementd :produce-models option.")
      Unsupported
    }
    case ProduceAssignments(bv) => {
      logger.warning("ignoring unimplementd :produce-assingments option.")
      Unsupported
    }
    case RegularOutputChannel(channel) => {
      if(channel == "stdout") {
        regularOutputClosable.foreach(_.close)
        regularOutputClosable = None
        regularOutput = System.out
        Success
      } else if(channel == "stderr") {
        regularOutputClosable.foreach(_.close)
        regularOutputClosable = None
        regularOutput = System.err
        Success
      } else {
        try {
          val tmp = new PrintStream(new FileOutputStream(channel))
          regularOutput = tmp
          regularOutputClosable.foreach(_.close)
          regularOutputClosable = None
          regularOutputClosable = Some(tmp)
          Success
        } catch {
          case (e: Exception) => {
            logger.warning("Could not open regular output file <" + channel + ">: " + e.getMessage)
            Error("Could not set regular output at: " + channel)
          }
        }
      }
    }
    case DiagnosticOutputChannel(channel) => {
      if(channel == "stdout") {
        loggingOutputClosable.foreach(_.close)
        loggingOutputClosable = None
        loggingOutput = System.out
        Success
      } else if(channel == "stderr") {
        loggingOutputClosable.foreach(_.close)
        loggingOutputClosable = None
        loggingOutput = System.err
        Success
      } else {
        try {
          val tmp = new PrintStream(new FileOutputStream(channel))
          loggingOutput = tmp
          loggingOutputClosable.foreach(_.close)
          loggingOutputClosable = None
          loggingOutputClosable = Some(tmp)
          Success
        } catch {
          case (e: Exception) => {
            logger.warning("Could not open logging output file <" + channel + ">: " + e.getMessage)
            Error("Could not set logging output at: " + channel)
          }
        }
      }
    }
    case RandomSeed(n) => {
      logger.warning("ignoring unimplementd :random-seeds option.")
      Unsupported
    }
    case Verbosity(level) => {
      loggingLevel = verbosityToLogLevel(level)
      Success
    }
    case AttributeOption(attr) => {
      logger.info("ignoring unsupported option: " + attr)
      Unsupported
    }
  }

  /*
   * We consider any set-info as metadata for the script, not interpreted by solver
   */
  private def evalSetInfo(attr: Attribute): CommandResponse = attr match {
    //case Attribute("STATUS", Some(SSymbol("SAT"))) => {
    //  if(expectedResult != None)
    //    logger.warning("Setting status multiple times")
    //  expectedResult = Some(true)
    //  Success
    //}
    //case Attribute("STATUS", Some(SSymbol("UNSAT"))) => {
    //  if(expectedResult != None)
    //    logger.warning("Setting status multiple times")
    //  expectedResult = Some(false)
    //  Success
    //}
    //case Attribute("STATUS", v) => {
    //  logger.warning("set-info status set to unsupported value: " + v)
    //  expectedResult = None
    //  Error("set-info :status with invalid value: " + v)
    //}
    //case Attribute("SOURCE", Some(SSymbol(src))) => {
    //  Success
    //}
    //case Attribute("SMT-LIB-VERSION", Some(SDouble(ver))) => {
    //  Success
    //}
    //case Attribute("CATEGORY", Some(SString(cat))) => {
    //  Success
    //}
    case Attribute(key, value) => {
      logger.info("Ignoring metadata set-info attribute with key: " + key + " and value: " + value)
      Success
    }
  }

  def parseSort(sExpr: SExpr): TSort = sExpr match {
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
    AbstractInterpreter.execute(Script(commands))(interpreter)
  }

}
