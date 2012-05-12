package regolic.parsers

import scala.util.parsing.combinator._
import scala.io.Source
import java.io.InputStream
import scala.collection.mutable.ListBuffer

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.asts.theories.int.{Trees => IntTrees}
import regolic.asts.theories.real.{Trees => RealTrees}

import smtlib._
import smtlib.Absyn.{Term => PTerm, Sort => PSort, AssertCommand => PAssertCommand, _}

object SmtLib2 {

  object Trees {
    sealed abstract class Command
    case class SetLogic(logic: Logic) extends Command
    case class Assert(formula: Formula) extends Command
    case class Push(n: Int) extends Command
    case class Pop(n: Int) extends Command
    case object CheckSat extends Command

    sealed abstract trait Logic
    case object QF_UF extends Logic
    case object QF_LRA extends Logic
    case object QF_AX extends Logic
    case object QF_A extends Logic
  }

  import Trees._

  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  private var funSymbols: Map[String, FunctionSymbol] = Map()

  def apply(input: InputStream): List[Command] = {

    funSymbols = Map()

    val l = new Yylex(input)//new java.io.FileReader(filename))
    val p = new parser(l)
    val parseTree = p.pScriptC
    val script = parseTree match {
      case (parseTree : Script) => parseTree
      case _ => throw new FileFormatException("Input is not in valid SMT-LIB 2 format")
    }

    var cmds: ListBuffer[Command] = ListBuffer()

    for (cmd <- script.listcommand_) cmd match {
      case cmd : PAssertCommand => {
        cmds.append(Assert(translateFormula(cmd.term_)))
      }
      case push: PushCommand => {
        val n = push.numeral_.toInt
        cmds.append(Push(n))
      }
      case pop: PopCommand => {
        val n = pop.numeral_.toInt
        cmds.append(Pop(n))
      }
      case check: CheckSatCommand => {
        cmds.append(CheckSat)
      }
      case fundecl: FunctionDeclCommand	=> {
        val name = asString(fundecl.symbol_)
        val returnSort = translateSort(fundecl.sort_)
        val paramSorts = asSortsList(fundecl.mesorts_).map(translateSort).toList
        funSymbols += (name -> FunctionSymbol(name, paramSorts, returnSort))
      }
      case log: SetLogicCommand => {
        val logicString = asString(log.symbol_)
        val logic = logicString match {
          case "QF_UF" => QF_UF
          case "QF_LRA" => QF_LRA
          case "QF_AX" => QF_AX
          case "QF_A" => QF_A
          case _ => sys.error("Unsupported logic: " + logicString)
        }
        cmds.append(SetLogic(logic))
      }
      case _ => //do nothing
    }

    cmds.toList
  }

  def translateFormula(t: PTerm): Formula = t match {
      case (t: ConstantTerm) => sys.error("not supported")
      case (t: NullaryTerm) => translateFormulaApp(t.symbolref_, List())
      case (t: FunctionTerm) => translateFormulaApp(t.symbolref_, t.listterm_)
      case (t: QuantifierTerm) => {
        val variables = t.listsortedvariablec_.map{
          case binder : SortedVariable => {                                                                               
            val sort = translateSort(binder.sort_)
            Variable(asString(binder.symbol_), sort)
          }
          case _ => sys.error("not supported")
        }
        val body = translateFormula(t.term_)
        t.quantifier_ match {
          case _: AllQuantifier =>
            variables.foldLeft(body)((fAcc, v) => Forall(v, fAcc))
          case _: ExQuantifier =>
            variables.foldLeft(body)((fAcc, v) => Exists(v, fAcc))
        }
      }
  }

  def translateTerm(t: PTerm): Term = t match {
      case (t: ConstantTerm) => translateSpecConstant(t.specconstant_)
      case (t: NullaryTerm) => translateTermApp(t.symbolref_, List())
      case (t: FunctionTerm) => translateTermApp(t.symbolref_, t.listterm_)
  }

  def translateSpecConstant(c: SpecConstant) = c match {
    case (c: NumConstant) => IntTrees.Num(BigInt(c.numeral_))
  }

  def translateTermApp(symbol: SymbolRef, args: Seq[PTerm]): Term = symbol match {
    case PlainSymbol(sym) => applyFunctionSymbol(sym, args.map(translateTerm))
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
      case _ => funSymbols(sym)
    }

    FunctionApplication(funSym, args.toList)
  }

  def applyPredicateSymbol(sym: String, args: Seq[Term]): PredicateApplication = {

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


  def translateFormulaApp(symbol: SymbolRef, args: Seq[PTerm]): Formula = symbol match {
    case PlainSymbol("true") => True()
    case PlainSymbol("false") => False()
    case PlainSymbol("not") => Not(translateFormula(args.head))
    case PlainSymbol("and") => And(args.map(arg => translateFormula(arg)).toList)
    case PlainSymbol("or") => Or(args.map(arg => translateFormula(arg)).toList)
    case PlainSymbol("=>") => Implies(translateFormula(args(0)), translateFormula(args(1)))
    case PlainSymbol("ite") => IfThenElse(translateFormula(args(0)), translateFormula(args(1)), translateFormula(args(2)))
    case PlainSymbol(sym) => applyPredicateSymbol(sym, args.map(translateTerm))
  }

  def translateSort(sort: PSort): Sort = sort match {
    case (s: IdentSort) => Sort(asString(s.identifier_), List())
    case _ => sys.error("not supported")
  }
  def asSortsList(sorts: MESorts): Seq[PSort] = sorts match {
    case (noSorts: NoSorts) => Seq()
    case (someSorts: SomeSorts) => someSorts.listsort_
  }

  private object PlainSymbol {
    def unapply(s : SymbolRef) : scala.Option[String] = s match {
      case s : IdentifierRef => s.identifier_ match {
        case id : SymbolIdent => id.symbol_ match {
          case s : NormalSymbol => Some(s.normalsymbolt_)
          case _ => None
        }
        case _ => None
      }
      case _ => None
    }
  }

  private def asString(s: SymbolRef): String = s match {
    case (id: IdentifierRef) => asString(id.identifier_)
    case (castId: CastIdentifierRef) => asString(castId.identifier_)
  }
  private def asString(id: Identifier): String = id match {
    case (id: SymbolIdent) => asString(id.symbol_)
    case (id: IndexIdent) => asString(id.symbol_) + ((id.listindexc_ map (_.asInstanceOf[Index].numeral_)) mkString "_")
  }
  private def asString(s: Symbol): String = s match {
    case (s: NormalSymbol) => s.normalsymbolt_
    case (s: QuotedSymbol) => s.quotedsymbolt_
  }
  
}
