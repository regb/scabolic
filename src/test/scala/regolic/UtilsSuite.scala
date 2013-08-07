package regolic

import org.scalatest.FunSuite


class UtilsSuite extends FunSuite {

  import Utils._
  test("isDigit") {
    assert(isDigit('0', 10))
    assert(isDigit('1', 10))
    assert(isDigit('5', 10))
    assert(isDigit('9', 10))
    assert(!isDigit('a', 10))
    assert(!isDigit(0.toChar, 10))

    assert(isDigit('7', 8))
    assert(isDigit('0', 8))
    assert(isDigit('3', 8))
    assert(!isDigit('9', 8))
    assert(!isDigit('a', 8))
    assert(!isDigit('A', 8))

    assert(isDigit('0', 2))
    assert(isDigit('1', 2))
    assert(!isDigit('2', 2))
    assert(!isDigit('a', 2))

    assert(isDigit('7', 16))
    assert(isDigit('0', 16))
    assert(isDigit('3', 16))
    assert(isDigit('9', 16))
    assert(isDigit('a', 16))
    assert(isDigit('A', 16))
    assert(isDigit('C', 16))
    assert(isDigit('F', 16))
    assert(isDigit('f', 16))
    assert(!isDigit('g', 16))
    assert(!isDigit('z', 16))
    assert(!isDigit('Z', 16))
  }

}
