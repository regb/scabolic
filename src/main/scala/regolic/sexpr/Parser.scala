package regolic.sexpr

import Tokens._
import SExprs._

class Parser(lexer: Lexer) {

  private var _currentToken: Token = null
  private var _futureToken: Token = lexer.next
  private def next: Token = {
    if(_futureToken == null)
      throw new java.io.EOFException

    _currentToken = _futureToken 
    _futureToken = lexer.next
    _currentToken
  }
  private def peek: Token = _futureToken
  private def eat(t: Token): Unit = {
    val n = next
    assert(n == t)
  }

  /* 
     Return the next SExpr if there is one, or null if EOF.
     Throw an EOFException if EOF is reached at an unexpected moment (incomplete SExpr).
  */
  def parse: SExpr = if(peek == null) null else {
    next match {
      case OParen => {
        val buffer = new scala.collection.mutable.ListBuffer[SExpr]
        while(peek != CParen) {
          val child: SExpr = parse
          buffer.append(child)
        }
        eat(CParen)
        SList(buffer.toList)
      }
      case IntLit(d) => SInt(d)
      case StringLit(s) => SString(s)
      case SymbolLit(s) => {
        val sym = SSymbol(s)
        if(peek == Colon) {
          eat(Colon)
          next match {
            case SymbolLit(s) => SQualifiedSymbol(Some(sym), SSymbol(s))
            case x => sys.error("Expected a symbol after ':', got: " + x)
          }
        } else sym
      }
      case DoubleLit(d) => SDouble(d)
      case Colon => {
        next match {
          case SymbolLit(s) => SQualifiedSymbol(None, SSymbol(s))
          case x => sys.error("Expected a symbol after ':', got: " + x)
        }
      }
      case CParen => sys.error("Unexpected token: " + CParen)
    }
  }


}
