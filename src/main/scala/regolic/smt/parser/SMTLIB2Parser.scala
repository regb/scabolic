package regolic.smt.parser

import scala.util.parsing.combinator._
import scala.io.Source

import regolic.asts.fol.Trees.{Equals => FolEquals, _}
import regolic.asts.core.Trees._
import regolic.asts.theories.int.Trees._

import smtlib._
import smtlib.Absyn.{Term => PTerm, Sort => PSort, _}

class SMTLIB2Parser(filename: String) {

  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  val l = new Yylex(new java.io.FileReader(filename))
  val p = new parser(l)
  val parseTree = p.pScriptC
  val script = parseTree match {
    case parseTree : Script => parseTree
    case _ => throw new Exception("Input is not an SMT-LIB 2 file")
  }

  for (cmd <- script.listcommand_) cmd match {
    case cmd : AssertCommand => {
      println(translateFormula(cmd.term_))
    }
    case _ => //do nothing
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
    case c: NumConstant => Num(BigInt(c.numeral_))
  }

  def translateTermApp(symbol: SymbolRef, args: Seq[PTerm]): Term = symbol match {
    case PlainSymbol("+") => Add(args.map(arg => translateTerm(arg)).toList)
    case PlainSymbol("-") if args.length == 1 => Neg(translateTerm(args(0)))
    case PlainSymbol("-") => Sub(translateTerm(args(0)), translateTerm(args(1)))
    case PlainSymbol("*") => Mul(args.map(arg => translateTerm(arg)).toList)
    case PlainSymbol("div") => Div(translateTerm(args(0)), translateTerm(args(1)))
    case PlainSymbol("mod") => Mod(translateTerm(args(0)), translateTerm(args(1)))
    case PlainSymbol("abs") => Abs(translateTerm(args(0)))
    case id => Variable(asString(id), Sort("Int"))
  }


  def translateFormulaApp(symbol: SymbolRef, args: Seq[PTerm]): Formula = symbol match {
    case PlainSymbol("true") => True()
    case PlainSymbol("false") => False()
    case PlainSymbol("not") => Not(translateFormula(args.head))
    case PlainSymbol("and") => And(args.map(arg => translateFormula(arg)).toList)
    case PlainSymbol("or") => Or(args.map(arg => translateFormula(arg)).toList)
    case PlainSymbol("=>") => Implies(translateFormula(args(0)), translateFormula(args(1)))
    case PlainSymbol("ite") => IfThenElse(translateFormula(args(0)), translateFormula(args(1)), translateFormula(args(2)))

    //predicates
    case PlainSymbol("=") => {
      val t1 = translateTerm(args(0))
      val t2 = translateTerm(args(1))
      Equals(t1, t2)
    }
    case PlainSymbol("<") => LessThan(translateTerm(args(0)), translateTerm(args(1)))
    case PlainSymbol("<=") => LessEqual(translateTerm(args(0)), translateTerm(args(1)))
    case PlainSymbol(">") => GreaterThan(translateTerm(args(0)), translateTerm(args(1)))
    case PlainSymbol(">=") => GreaterEqual(translateTerm(args(0)), translateTerm(args(1)))
  }

  def translateSort(sort: PSort): Sort = sort match {
    case (s: IdentSort) => Sort(asString(s.identifier_))
    case _ => sys.error("not supported")
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
