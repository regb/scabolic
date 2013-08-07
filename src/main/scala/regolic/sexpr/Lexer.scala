package regolic
package sexpr

import Tokens._
import Utils.isDigit

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
      case '#' => {
        val radix = nextChar
        val base: Int = radix match {
          case 'b' => 2
          case 'o' => 8
          case 'x' => 16
          case d if d.isDigit => {
            val r = readInt(d, 10).toInt
            val ending = nextChar
            if(ending != 'r' && ending != 'R')
              sys.error("expected 'r' termination mark for radix")
            r
          }
          case _ => sys.error("unexpected char: " + radix)
        }
        IntLit(readInt(nextChar, base))
      }
      case d if d.isDigit => {
        val intPart = readInt(d, 10)
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
          DoubleLit(intPart.toDouble + fracPart/base)
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

  private def readInt(currentChar: Char, r: Int): BigInt = {
    require(r > 1 && r <= 36)
    var acc: BigInt = currentChar.asDigit //asDigit works for 'A', 'F', ...
    while(isDigit(peek.toChar, r)) {
      acc *= r
      acc += nextChar.asDigit
    }
    acc
  }

}
