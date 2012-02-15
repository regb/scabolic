package regolic.algebra

import org.scalatest.FunSuite

class MatrixSuite extends FunSuite {

  def r(n: BigInt) = Rational(n)
  def r(n: BigInt, d: BigInt) = Rational(n, d)

  def s2m(str: String): Matrix[Rational] = new Matrix(str.split(',').map(s => s.split(' ').map(n => Rational(n))))

  val m0 = s2m("0 0," +
               "0 0")
  val m1 = s2m("1 2 3," +
               "4 5 6," +
               "7 8 9")
  val m2 = s2m("2 5 1," +
               "1 2 1," +
               "3 2 4")
  val m3 = s2m("1 0," +
               "0 2")
  val m4 = s2m("-1 0," +
               "0 -2")
  val m3xm4 = s2m("-1 0," +
                  "0 -4")
  val m1plusm2 = s2m("3 7 4," +
                  "5 7 7," +
                  "10 10 13")
  val m1xm2 = s2m("13 15 15," +
                  "31 42 33," +
                  "49 69 51")

  val gauss1 = s2m("2 4 6 38," +
                   "1 3 3 21," +
                   "2 4 7 42")
  val gauss2 = s2m("1 0 0 3," +
                   "0 1 0 2," +
                   "0 0 1 4")
  val gauss3 = s2m("1 3 3 21," +
                   "2 4 7 42," +
                   "2 4 6 38")

  test("representation") {
    assert(m1(0,0) === r(1))
    assert(m1(0,1) === r(2))
    assert(m1(0,2) === r(3))
    assert(m1(1,0) === r(4))
    assert(m1(1,1) === r(5))
    assert(m1(1,2) === r(6))
    assert(m1(2,0) === r(7))
    assert(m1(2,1) === r(8))
    assert(m1(2,2) === r(9))
  }

  test("equals") {
    assert(m1 === m1)
    assert(m2 === m2)
    assert(s2m("1 2,1 2") === s2m("1 2,1 2"))
    assert(s2m("2") === s2m("2"))
    assert(s2m("1 2,2 1") != s2m("1 2,1 2"))
    assert(m0 == m0.zero)
  }

  test("addition") {
    assert(m1plusm2 === m1 + m2)
    assert(m0 === m3 + m4)
  }

  test("multiplication") {
    assert(m1xm2 === m1 * m2)
    assert(m3xm4 === m3 * m4)
  }

  test("gauss") {
    val reduct1 = gauss1.gaussJordanElimination 
    assert(reduct1 != None)
    assert(reduct1.get === gauss2)
    val reduct3 = gauss3.gaussJordanElimination
    assert(reduct3 != None)
    assert(reduct3.get === gauss2)
  }

}
