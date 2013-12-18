package regolic
package smtlib

import regolic.sexpr
import regolic.sexpr.SExprs._

import scala.collection.Iterator

import Commands._

object Parser {
  class UnknownCommand(msg: String) extends Exception(msg)
}

class Parser(input: java.io.Reader) extends Iterator[Command] {

  import Parser._

  private val l = new sexpr.Lexer(input)
  private val p = new sexpr.Parser(l)

  private var nextCommand: SExpr = p.parse

  def parseAll: Seq[Command] = ???

  override def hasNext: Boolean = nextCommand != null

  override def next: Command = {
    val res = nextCommand match {
      case SList(List(SSymbol("SET-LOGIC"), SSymbol(logic))) => 
        SetLogic(Logic.fromString(logic))
      case SList(SSymbol("SET-INFO") :: attr) =>
        SetInfo(parseAttribute(attr))
      case SList(List(SSymbol("DECLARE-SORT"), s@SSymbol(sort), SInt(arity))) => 
        DeclareSort(s, arity.toInt)
      case SList(List(SSymbol("DECLARE-FUN"), s@SSymbol(fun), SList(sorts), sort)) =>
        DeclareFun(s, sorts, sort)
      case SList(List(SSymbol("ASSERT"), term)) =>
        Assert(term)
      case SList(List(SSymbol("CHECK-SAT"))) =>
        CheckSat
      case SList(List(SSymbol("EXIT"))) =>
        Exit
      case SList(List(SSymbol("PUSH"), SInt(n))) => 
        Push(n.toInt)
      case SList(List(SSymbol("POP"), SInt(n))) => 
        Pop(n.toInt)
      case _ =>
        throw new UnknownCommand("Unknown command: " + nextCommand)
    }
    nextCommand = p.parse
    res
  }

  //todo: make sure no nested keyword in value
  private def parseAttribute(ss: List[SExpr]): Attribute = ss match {
    case List(SQualifiedSymbol(None, SSymbol(key))) => Attribute(key, None)
    case List(SQualifiedSymbol(None, SSymbol(key)), v) => Attribute(key, Some(v))
    case _ => sys.error("unexpected: " + ss + " when expecting attribute")
  }

}
