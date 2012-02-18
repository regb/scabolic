package regolic.algebra

import org.scalatest.FunSuite

class VectorSuite extends FunSuite {

  def r(n: BigInt) = Rational(n)
  def r(n: BigInt, d: BigInt) = Rational(n, d)

  def s2m(str: String): Matrix[Rational] = new Matrix(str.split(',').map(s => s.split(' ').map(n => Rational(n))))
  def s2v(str: String): Vector[Rational] = new Vector(str.split(' ').map(n => Rational(n)))

  val v1 = s2v("1 2 3")
  val v2 = s2v("4 5 6")
  val v3 = s2v("7 8 9")

  val m1 = s2m("1 2 3," +
               "4 5 6," +
               "7 8 9")


  test("representation") {
    assert(v1(0) === r(1))
    assert(v1.element(0) === r(1))
    assert(v2(1) === r(5))
    assert(v3(2) === r(9))
    assert(v1.size === 3)
    assert(v2.size === 3)
    assert(v3.size === 3)
    assert(s2v("1 2 3 4 5").size === 5)
  }

  test("equals") {
    assert(s2v("1 2 3") === s2v("1 2 3"))
    assert(s2v("1 3 5") === s2v("1 3 5"))
    assert(s2v("1 2 3 5") === s2v("1 2 3 5"))
    assert(s2v("1 2 5") != s2v("1 3 5"))
  }

  test("matrix to vector") {
    assert(v1 === Vector(s2m("1,2,3")))
    assert(v1 === Vector(s2m("1 2 3")))
    assert(v2 === Vector(s2m("4 5 6")))
    assert(v2 === Vector(s2m("4,5,6")))
    assert(s2v("1 4 7 9") === Vector(s2m("1 4 7 9")))
    assert(s2v("1 4 7 9") === Vector(s2m("1,4,7,9")))
  }

  test("map") {

  }

  test("foldLeft") {

  }

  test("forall") {

  }

  test("exists") {

  }


  test("addition") {
    assert(v1 + v2 === s2v("5 7 9"))
    assert(v1 + v3 === s2v("8 10 12"))
    assert(v2 + v3 === s2v("11 13 15"))
    intercept[IllegalArgumentException]{ v2 + s2v("1 2 3 4") }
  }

  test("negation") {

  }

  test("multiplication by scalar") {

  }

  test("scalar product") {

  }

  test("multiplication by matrix") {

  }
}
