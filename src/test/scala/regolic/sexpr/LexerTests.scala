package regolic.sexpr

import Tokens._
import java.io.StringReader

import org.scalatest.FunSuite

class LexerTests extends FunSuite {

  test("lexer") {
    val reader1 = new StringReader("""
      (test "test")
    """)
    val lexer1 = new Lexer(reader1)
    assert(lexer1.next === OParen)
    assert(lexer1.next === SymbolLit("test"))
    assert(lexer1.next === StringLit("test"))
    assert(lexer1.next === CParen)


    val reader2 = new StringReader("""
      ) (  42  42.173
    """)
    val lexer2 = new Lexer(reader2)
    assert(lexer2.next === CParen)
    assert(lexer2.next === OParen)
    assert(lexer2.next === IntLit(42))
    assert(lexer2.next === DoubleLit(42.173))

    val reader3 = new StringReader("""
      ) ;(  42  42.173
      12 "salut" ; """)
    val lexer3 = new Lexer(reader3)
    assert(lexer3.next === CParen)
    assert(lexer3.next === IntLit(12))
    assert(lexer3.next === StringLit("salut"))
  }
}
