package regolic.algebra

import org.scalatest.FunSuite

class RationalSuite extends FunSuite {
  
  def r(n: BigInt) = Rational(n)
  def r(n: BigInt, d: BigInt) = Rational(n, d)


  test("basic representation") {
    assert(r(0).numerator === 0)
    assert(r(0).denominator === 1)
    assert(r(1).numerator === 1)
    assert(r(1).denominator === 1)
    assert(r(2).numerator === 2)
    assert(r(2).denominator === 1)

    assert(r(0,1).numerator === 0)
    assert(r(0,1).denominator === 1)
    assert(r(1,1).numerator === 1)
    assert(r(1,1).denominator === 1)
    assert(r(2,1).numerator === 2)
    assert(r(2,1).denominator === 1)
    assert(r(1,2).numerator === 1)
    assert(r(1,2).denominator === 2)
  }

  test("String based constructor") {
    assert(r(1) === Rational("1"))
    assert(r(1) === Rational("1/1"))
    assert(r(2) === Rational("2"))
    assert(r(2) === Rational("2/1"))
    assert(r(1,2) === Rational("1/2"))
    assert(r(2,3) === Rational("2/3"))
    assert(r(13,27) === Rational("13/27"))

  }

  test("gcd representation positive num and denum") {
    assert(r(4,2).numerator === 2)
    assert(r(4,2).denominator === 1)
    assert(r(2,4).numerator === 1)
    assert(r(2,4).denominator === 2)
    assert(r(0,3).numerator === 0)
    assert(r(0,3).denominator === 1)
    assert(r(24,6).numerator === 4)
    assert(r(24,6).denominator === 1)
    assert(r(32,20).numerator === 8)
    assert(r(32,20).denominator === 5)
  }

  test("gcd representation positive and negative num and denum") {
    assert(r(0, -4).numerator === 0)
    assert(r(0, -4).denominator === 1)
    assert(r(-2,1).numerator === -2)
    assert(r(-2,1).denominator === 1)
    assert(r(2,-1).numerator === -2)
    assert(r(2,-1).denominator === 1)
    assert(r(6,-3).numerator === -2)
    assert(r(6,-3).denominator === 1)
    assert(r(-32,20).numerator === -8)
    assert(r(-32,20).denominator === 5)
    assert(r(-6, -4).numerator === 3)
    assert(r(-6, -4).denominator === 2)
  }

  test("equals") {
    assert(r(1) === r(1))
    assert(r(0) === r(0))
    assert(r(1,1) === r(1))
    assert(r(2,1) === r(2))
    assert(r(5,2) === r(5,2))
    assert(r(4,2) === r(4,2))
    assert(r(4,2) === r(2,1))
    assert(r(4,2) === r(2))
    assert(r(44, 20) === r(11,5))
  }

  test("addition") {
    assert(r(1) + r(1) === r(2))
    assert(r(1,2) + r(1,2) === r(1))
    assert(r(3,2) + r(5,2) === r(8,2))
    assert(r(1) + r(5,3) === r(8, 3))
  }

  test("subtraction") {
    assert(r(1) - r(0) === r(1))
    assert(r(2) - r(1) === r(1))
    assert(r(3,2) - r(3,2) === r(0))
    assert(r(7,3) - r(3,2) === r(5,6))
    assert(r(3) - r(3,2) != r(7,2))
  }

  test("multiplication") {
    assert(r(1) * r(3,2) === r(3,2))
    assert(r(3,2) * r(2,3) === r(1))
    assert(r(4,3) * r(2,5) === r(8, 15))
    assert(r(0) * r(1,2) === r(0))
  }

  test("division") {
    assert(r(1) / r(1) === r(1))
    assert(r(4) / r(2) === r(2))
    assert(r(4,3) / r(2) === r(2,3))
  }
}
