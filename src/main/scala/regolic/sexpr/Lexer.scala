package regolic.sexpr

import Tokens._

class Lexer(reader: java.io.Reader) {

  private def isNewLine(c: Char) = c == '\n' || c == '\r'
  private def isBlank(c: Char) = c == '\n' || c == '\r' || c == ' '
  private def isSeparator(c: Char) = isBlank(c) || c == ')' || c == '('

  private var _currentChar: Int = -1
  private var _futureChar: Int = reader.read

  private def nextChar: Char = {
    if(_futureChar == -1)
      throw new java.io.EOFException
    _currentChar = _futureChar
    _futureChar = reader.read
    _currentChar.toChar
  }
  private def peek: Int = _futureChar

  /* 
     Return the next token if there is one, or null if EOF.
     Throw an EOFException if EOF is reached at an unexpected moment (incomplete token).
  */
  def next: Token = if(peek == -1) null else {

    var c: Char = nextChar
    while(isBlank(c)) {
      if(peek == -1)
        return null
      c = nextChar
    }

    c match {
      case ';' => {
        while(!isNewLine(nextChar))
          ()
        next
      }
      case '(' => OParen
      case ')' => CParen
      case '"' => {
        val buffer = new scala.collection.mutable.ArrayBuffer[Char]
        var c = nextChar
        while(c != '"') {
          buffer.append(c)
          c = nextChar
        }
        StringLit(new String(buffer.toArray))
      }
      case d if d.isDigit => {
        var intPart: Int = d.asDigit
        while(peek.toChar.isDigit) {
          intPart *= 10
          intPart += nextChar.asDigit
        }
        if(peek != '.')
          IntLit(intPart)
        else {
          nextChar
          var fracPart: Double = 0
          var base = 10
          while(peek.toChar.isDigit) {
            fracPart += nextChar.asDigit
            fracPart *= 10
            base *= 10
          }
          DoubleLit(intPart + fracPart/base)
        }
      }
      case s => {
        val buffer = new scala.collection.mutable.ArrayBuffer[Char]
        buffer.append(s)
        while(!isSeparator(peek.toChar)) {
          buffer.append(nextChar)
        }
        SymbolLit(new String(buffer.toArray))
      }
    }
  }

}
