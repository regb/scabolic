package regolic.smt.smtlib

import scala.util.parsing.combinator._
import scala.io.Source

import Trees._
import regolic.asts.fol.Trees._
import regolic.asts.core.Trees._

/* 
 * This parser is based on the grammar of the 1.2 version of the SMTLIB format found at this url:
 * http://combination.cs.uiowa.edu/smtlib/papers.html
 *
 * Note also that we only parse benchmarks and we don't attempt to parse theory description file
 * 
 */

class Parser(filename: String) extends RegexParsers {

  /* Parse a full benchmark, do not interpret any symbol of any logic, 
     a parser for the logic should process the resulting Benchmark */
  def parse(): Trees.Benchmark = {
    val bench = parseAll(benchmark, Source.fromFile(filename).bufferedReader)
    bench.get
  }

  /*
   *** The grammar of the smt-lib benchmark format ***
   *
   * We rewrite here the grammar from the paper. It is slighly modified in order to be more adapted
   * to Scala but should be equivalent.
   *
   * "" or '' are used to surround syntaxic word that must be present, they have the same meaning, 
   * normal names are rule names.
   * The name used are consistent with the rules written in the parser generator, the syntax is
   * close to the mathematical definition with <|> standing for union, < > standing for concatenation,
   * <*> standing for star operator. We use <rule+> for <rule rule*>.
   * It is assumed that between each concatenation there could be any number of white space.
   * Parenthesis are used to break the normal precedence of operators.
   * 
   *  
   * benchmark         ::= "(" "benchmark" identifier benchAttribute+ ")"
   * benchAttribute    ::= ":logic" identifier 
   *                    |  ":assumption" formula
   *                    |  ":formula" formula
   *                    |  ":status" status
   *                    |  ":extrasorts" "(" sortSymb+ ")"
   *                    |  ":extrafuns" "(" funSymbDecl+ ")"
   *                    |  ":extrapreds" "(" predSymbDecl+ ")"
   *                    |  ":notes" '"' stringContent '"' 
   *                    |  annotation
   * status            ::= "sat" | "unsat" | "unknown"
   * predSymbDecl      ::= "(" predSymb sortSymb* annotation* ")"
   * funSymbDecl       ::= "(" ( funSymb sortSymb+ annotation*
   *                           | numeral sortSymb annotation*
   *                           | rational sortSymb annotation* ) ")"
   * stringContent     ::= any sequence of printable characters where every occurrence
   *                       of double quotes (") is preceded by a backslash ( \ )
   * formula           ::= atom | "(" ( connective formula+ annotation*
   *                                  | quantSymb quantVar+ formula annotation*
   *                                  | "let" "(" var term ")" formula annotation*
   *                                  | "flet" "(" fvar formula ")" formula annotation* ) ")"
   * quantVar          ::= "(" var sortSymb ")"
   * quantSymb         ::= "exists" | "forall"
   * connective        ::= "not" | "implies" | "if_then_else" | "and" | "or" | "xor" | "iff"
   * atom              ::= propAtom 
   *                    | "(" propAtom annotation+ ")" 
   *                    | "(" predAtom term+ annotation* ")"
   * propAtom          ::= "true" | "false" | fvar | identifier
   * term              ::= baseTerm
   *                    |  "(" baseTerm annotation+ ")"
   *                    |  "(" funSymb term+ annotation* ")"
   *                    |  "(" "ite" formula term term annotation* ")"
   * baseTerm          ::= var | numeral | rational | identifier
   * annotation        ::= attribute | attribute userValue
   * sortSymb          ::= identifier
   * predSymb          ::= identifier | arithSymb | "distinct"
   * funSymb           ::= identifier | arithSymb
   * arithSymb         ::= ( "=" | "<" | ">" | "&" | "@" | "#" | "+" | "-" | "*" | "/" | "%" | "|" | "~" )+
   * var               ::= "?" simpleIdentifier
   * fvar              ::= "$" simpleIdentifier
   * attribute         ::= ":" simpleIdentifier
   * numeral           ::= 0 | [1-9][0-9]*
   * identifier        ::= simpleIdentifier | indexedIdentifier
   * indexedIdentifier ::= simpleIdentifier "[" numeral (":" numeral)* "]"
   * userValue         ::= "{" any sequence of printable characters where every occurence of braces
   *                           ({}) is preceded by a backslash (\) "}"
   * simpleIdentifier  ::= a sequence of letters, digits, dots (.), single quotes ('), and
   *                       underscores (_), starting with a letter
   *
   */


  private var logicAttribute: Option[LogicAttribute] = None
  private def setLogicAttribute(la: LogicAttribute) = logicAttribute match {
    case None => logicAttribute = Some(la)
    case Some(la) => sys.error("Logic already set")
  }

  private val funSymbMap = new scala.collection.mutable.HashMap[String, FunctionSymbol]
  private val predSymbMap = new scala.collection.mutable.HashMap[String, PredicateSymbol]

  private def putFunSymbMap(f: FunctionSymbol) {
    if(funSymbMap.get(f.name) != None) 
      throw new Exception("Multiple extra fun definition")
    else
      funSymbMap.put(f.name, f)
  }

  private def createFunApplication(symbName: String, args: List[Term]): FunctionApplication = funSymbMap.get(symbName) match {
    case None => logicAttribute match {
      case Some(QF_LIA) => sys.error("not supported")/*symbName match {
        case "+" => asts.theories.qflia.Trees.Add(args)
        case "-" => asts.theories.qflia.Trees.Sub(args.head, args.tail.head)
        case n => try {
          asts.theories.qflia.Trees.Number(BigInt(n)) 
        } catch {
          case _ => error("Unknown function in QF_LIA: " + symbName)
        }
      }*/
      case Some(_) => sys.error("Not supported logic")
      case None => sys.error("logic not set")
    } 
    case Some(f) => FunctionApplication(f, args)
  }


  private def putPredSymbMap(p: PredicateSymbol) {
    if(predSymbMap.get(p.name) != None) 
      throw new Exception("Multiple extra pred definition")
    else
      predSymbMap.put(p.name, p)
  }

  private def createPredApplication(symbName: String, args: List[Term]): PredicateApplication = predSymbMap.get(symbName) match {
    case None => logicAttribute match {
      case Some(QF_LIA) => sys.error("not supported") /*symbName match {
        case ">=" => asts.theories.qflia.Trees.GreaterEqual(args.head, args.tail.head)
        case ">" => asts.theories.qflia.Trees.GreaterThan(args.head, args.tail.head)
        case _ => error("Unknown predicate in QF_LIA: " + symbName)
      }*/
      case Some(_) => sys.error("Not supported logic")
      case None => sys.error("logic not set")
    }
    case Some(p) => PredicateApplication(p, args)
  }

  def benchmark: Parser[Benchmark] = ("(" ~ "benchmark" ~ identifier ~ rep1(benchAttribute) ~ ")") ^^ 
    { case _ ~ _ ~ name ~ attributes ~ _  =>  Benchmark(name, attributes) }

  def benchAttribute: Parser[BenchAttribute] = (
    ":logic" ~ identifier
  | ":assumption" ~ formula
  | ":formula" ~ formula
  | ":status" ~ status
  | ":extrasorts" ~ "(" ~ rep1(sortSymb) ~ ")"
  | ":extrafuns" ~ "(" ~ rep1(funSymbDecl) ~ ")" 
  | ":extrapreds" ~ "(" ~ rep1(predSymbDecl) ~ ")" 
  | ":notes" ~ "\"" ~ stringContent ~"\""
  | annotation
  ) ^^ {
    case ":logic" ~ id => id match {
      case "QF_BV" => {setLogicAttribute(QF_BV); QF_BV}
      case "QF_FP" => {setLogicAttribute(QF_FP); QF_FP}
      case "QF_LIA" => {setLogicAttribute(QF_LIA); QF_LIA}
      case _ => throw new Exception("Not supported logic")
    }
    case ":assumption" ~ (f: Formula) => AssumptionAttribute(f)
    case ":formula" ~ (f: Formula) => FormulaAttribute(f)
    case ":status" ~ (st: StatusAttribute) => st
    case ":extrasorts" ~ _ ~ (sortSymbs: List[_]) ~ _ if sortSymbs.forall(_.isInstanceOf[Sort]) => 
      ExtraSortsAttribute(sortSymbs.asInstanceOf[List[Sort]])
    case ":extrafuns" ~ _ ~ (funSymbsDecl: List[_]) ~ _ if funSymbsDecl.forall(_.isInstanceOf[FunctionSymbol]) => {
      val fsd = funSymbsDecl.asInstanceOf[List[FunctionSymbol]]
      fsd.foreach(putFunSymbMap)
      ExtraFunsAttribute(fsd)
    }
    case ":extrapreds" ~ _ ~ (predSymbsDecl: List[_]) ~ _ if predSymbsDecl.forall(_.isInstanceOf[PredicateSymbol]) => {
      val psd = predSymbsDecl.asInstanceOf[List[PredicateSymbol]]
      psd.foreach(putPredSymbMap)
      ExtraPredsAttribute(psd)
    }
    case ":notes" ~ _ ~ str ~ _ => throw new Exception("Not yet supported") 
    case res @ AnnotationAttribute(_,_) => res
    case res @ _ => sys.error("unexpected attribute: " + res)
  }
  
  def status: Parser[StatusAttribute] = ("sat" | "unsat" | "unknown") ^^ {
    case "sat" => Sat
    case "unsat" => Unsat
    case "unknown" => Unknown
  }

  def predSymbDecl: Parser[PredicateSymbol] = ("(" ~ predSymb ~ rep(sortSymb) ~ rep(annotation) ~ ")") ^^ {
    case _ ~ symb ~ sorts ~ _ ~ _ => PredicateSymbol(symb, sorts)
  }
  /* TODO: not exact */
  def funSymbDecl: Parser[FunctionSymbol] = ("(" ~ funSymb ~ rep1(sortSymb) ~ rep(annotation) ~ ")") ^^ {
    case _ ~ symb ~ sorts ~ _ ~ _ => FunctionSymbol(symb, sorts.init, sorts.last)
  }

  def stringContent: Parser[String] = throw new Exception("Not yet supported")

  def formula: Parser[Formula] = (
   "(" ~ connective ~ rep1(formula) ~ rep(annotation) ~ ")"
  | "(" ~ "let" ~ "(" ~ varr ~ term ~ ")" ~ formula ~ rep(annotation) ~ ")"
  | "(" ~ "flet" ~ "(" ~ fvar ~ formula ~ ")" ~ formula ~ rep(annotation) ~ ")"
  | atom
  ) ^^ {
    case "(" ~ ConnectiveAnd ~ (fs: List[_]) ~ _ ~ ")" => And(fs.asInstanceOf[List[Formula]])
    case "(" ~ ConnectiveOr ~ (fs: List[_]) ~ _ ~ ")" => Or(fs.asInstanceOf[List[Formula]])
    case "(" ~ ConnectiveIff ~ (fs: List[_]) ~ _ ~ ")" => Iff(fs(0).asInstanceOf[Formula], fs(1).asInstanceOf[Formula])
    case "(" ~ ConnectiveImplies ~ (fs: List[_]) ~ _ ~ ")" => Implies(fs(0).asInstanceOf[Formula], fs(1).asInstanceOf[Formula])
    case "(" ~ ConnectiveNot ~ (fs: List[_]) ~ _ ~ ")" => Not(fs(0).asInstanceOf[Formula])
    case "(" ~ ConnectiveITE ~ (fs: List[_]) ~ _ ~ ")" => IfThenElse(fs(0).asInstanceOf[Formula], fs(1).asInstanceOf[Formula], fs(2).asInstanceOf[Formula])
    //case "(" ~ "let" ~ "(" ~ (v: Variable) ~ (t: Term) ~ ")" ~ (f: Formula) ~ _ ~ ")" => Let(v, t, f)
    case "(" ~ "let" ~ "(" ~ (v: Variable) ~ (t: Term) ~ ")" ~ (f: Formula) ~ _ ~ ")" => sys.error("not supported")
    //case "(" ~ "flet" ~ "(" ~ (fv: FVariable) ~ (f1: Formula) ~ ")" ~ (f2: Formula) ~ _ ~ ")" => FLet(fv, f1, f2)
    case "(" ~ "flet" ~ "(" ~ fv ~ (f1: Formula) ~ ")" ~ (f2: Formula) ~ _ ~ ")" => sys.error("not supported")
    case (atom: Formula) => atom
    case res @ _ => throw new Exception("Not yet supported: " + res)
  }

  def quantVar: Parser[Variable] = throw new Exception("Not yet supported")
  def quantSymb: Parser[Any] = throw new Exception("Not yet supported")

  def connective: Parser[Connective] = ("not" | "implies" | "if_then_else" | "and" | "or" | "xor" | "iff") ^^ {
    case "not" => ConnectiveNot
    case "implies" => ConnectiveImplies
    case "if_then_else" => ConnectiveITE
    case "and" => ConnectiveAnd
    case "or" => ConnectiveOr
    case "xor" => ConnectiveXor
    case "iff" => ConnectiveIff
  }

  /* TODO */
  def atom: Parser[Formula] = (propAtom | "(" ~ predSymb ~ rep1(term) ~ rep(annotation) ~ ")") ^^ {
    case (prop: Formula) => prop
    case "(" ~ "=" ~ (ts: List[_]) ~ _ ~ ")" => Equals(ts(0).asInstanceOf[Term], ts(1).asInstanceOf[Term])
    case "(" ~ (symb: String) ~ (terms: List[_]) ~ _ ~ ")" => createPredApplication(symb, terms.asInstanceOf[List[Term]])
  }

  def propAtom: Parser[Formula] = ("true" | "false" | fvar | identifier) ^^ {
    case "true" => True()
    case "false" => False()
    //case f@ FVariable(_) => f
    case (id: String) => createPredApplication(id, Nil)
  }

  def term: Parser[Term] = (
    baseTerm
  | "(" ~ "ite" ~ formula ~ term ~ term ~ rep(annotation) ~ ")"
  | "(" ~ funSymb ~ rep1(term) ~ rep(annotation) ~ ")"
  ) ^^ {
    case (b: Term) => b
    case "(" ~ (fs: String) ~ (terms: List[_]) ~ _ ~ ")" => createFunApplication(fs, terms.asInstanceOf[List[Term]])
    case "(" ~ "ite" ~ (f: Formula) ~ (t1: Term) ~ (t2: Term) ~ _ ~ ")" => ITE(f, t1, t2)
  }

  def baseTerm: Parser[Term] = (varr | numeral | identifier) ^^ {
    case (id: String) => createFunApplication(id, Nil)
    case (v: Variable) => v 
  }


  def annotation: Parser[AnnotationAttribute] = (attribute ~ opt(userValue)) ^^ { case attr ~ o => AnnotationAttribute(attr, o) }

  def sortSymb: Parser[Sort] = identifier ^^ { case id => Sort(id) }
  def predSymb: Parser[String] = (identifier | arithSymb | "distinct") ^^{ case symb => symb}
  def funSymb: Parser[String] = identifier | arithSymb ^^ { case symb => symb}

  def arithSymb: Parser[String] = rep1("=" | "<" | ">" | "&" | "@" | "#" | "+" | "-" | "*" | "/" | "%" | "|" | "~") ^^ {
    case lString => lString.mkString("")
  }

  //def varr: Parser[Variable] = ("?" ~ simpleIdentifier) ^^ { case _ ~ id => Variable(id, logicAttribute match { case Some(QF_LIA) => asts.theories.qflia.Trees.IntSort() case _ => NoneSort() } ) }
  def varr: Parser[Variable] = sys.error("not supported")
  //def fvar: Parser[FVariable] = ("$" ~ simpleIdentifier) ^^ { case _ ~ id => FVariable(id) }
  def fvar = sys.error("not supported")

  def attribute: Parser[String] = { ":" ~ simpleIdentifier } ^^ { case ":" ~ id => id }

  def numeral: Parser[String] = regexNumeral.r ^^ { case n => n }

  def identifier: Parser[String] = (indexedIdentifier | simpleIdentifier) ^^ { case id => id }
  def indexedIdentifier: Parser[String] =
    (simpleIdentifier ~ "[" ~ numeral ~ rep( ":" ~ numeral) ~ "]") ^^ {
      case id ~ "[" ~ n ~ ns ~ "]" => id + "[" + n + ns.mkString("") + "]"
    }

  def userValue: Parser[String] = regexUserValue.r ^^ {case id => id.substring(1, id.size - 1)}
  def simpleIdentifier: Parser[String] = regexSimpleIdentifier.r ^^ {case id => id }

  /*
   * Regex strings
   */

  private val regexUserValue: String = """\{(([^\}\{])|(\\\{)|(\\\}))*\}"""
  private val regexDigitLetterDotSingleQuoteUnderscore: String = """\w|\.|'"""
  //a sequence of letters, digit, dots, single quotes, and underscores, starting with a letter
  private val regexSimpleIdentifier: String = "[a-zA-Z](" + regexDigitLetterDotSingleQuoteUnderscore + ")*"
  //any sequence of printable characters where every occurrence of brace is preceded by a backslash
  //private val regexUserValueContent: String = 
  private val regexNumeral: String = """0|[1-9][0-9]*"""
  //private val regexRational: String = regexNumeral + """\.0*""" + regexNumeral

  private[Parser] abstract class Connective
  private[Parser] case object ConnectiveAnd extends Connective
  private[Parser] case object ConnectiveNot extends Connective
  private[Parser] case object ConnectiveOr extends Connective
  private[Parser] case object ConnectiveImplies extends Connective
  private[Parser] case object ConnectiveIff extends Connective
  private[Parser] case object ConnectiveITE extends Connective
  private[Parser] case object ConnectiveXor extends Connective
  
}
