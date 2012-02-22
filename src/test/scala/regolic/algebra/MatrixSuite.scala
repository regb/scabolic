package regolic.algebra

import org.scalatest.FunSuite

class MatrixSuite extends FunSuite {

  def r(n: BigInt) = Rational(n)
  def r(n: BigInt, d: BigInt) = Rational(n, d)

  def s2m(str: String): Matrix[Rational] = new Matrix(str.split(',').map(s => s.split(' ').map(n => Rational(n))))
  def s2v(str: String): Vector[Rational] = new Vector(str.split(' ').map(n => Rational(n)))

  val id2 = s2m("1 0," +
                "0 1")
  val id3 = s2m("1 0 0," +
                "0 1 0," +
                "0 0 1")
  val id4 = s2m("1 0 0 0," +
                "0 1 0 0," +
                "0 0 1 0," +
                "0 0 0 1")

  val v1 = s2v("1 2 3")

  val m0 = s2m("0 0," +
               "0 0")
  val m01 = s2m("0 0 0," +
                "0 0 0")
  val m1 = s2m("1 2 3," +
               "4 5 6," +
               "7 8 9")
  val m1sub01 = s2m("1 2," +
                    "4 5")
  val m1sub02 = s2m("1 3," +
                    "7 9")
  val m1sub12 = s2m("5 6," +
                    "8 9")
  val m1neg = s2m("-1 -2 -3," +
                  "-4 -5 -6," +
                  "-7 -8 -9")
  val m2 = s2m("2 5 1," +
               "1 2 1," +
               "3 2 4")
  val m2neg = s2m("-2 -5 -1," +
                  "-1 -2 -1," +
                  "-3 -2 -4")
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

  val m1xv1 = s2v("14 32 50")

  val m5 = s2m("2 0," +
               "0 4")
  val m5inv = s2m("1/2 0," +
                  "0 1/4")
  val m6 = s2m("2 1," +
               "4 4")
  val m6inv = s2m("1 -1/4," +
                  "-1 1/2")
  val m7 = s2m("3 1," +
               "9 4")
  val m7inv = s2m("4/3 -1/3," +
                  "-3 1")
  val m8 = s2m("1 2 2," +
               "2 2 2," +
               "2 2 1")
  val m8inv = s2m("-1 1 0," +
                  "1 -3/2 1," +
                  "0 1 -1")


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
    intercept[IllegalArgumentException] {
      Matrix(Array(Array(r(1), r(2)), Array(r(3), r(4), r(5))))
    }
    intercept[IllegalArgumentException] {
      Matrix(Array[Array[Rational]]())
    }
    intercept[IllegalArgumentException] {
      Matrix(Array(Array[Rational](), Array[Rational]()))
    }
  }

  test("equals") {
    assert(m1 === m1)
    assert(m2 === m2)
    assert(s2m("1 2,1 2") === s2m("1 2,1 2"))
    assert(s2m("2") === s2m("2"))
    assert(s2m("1 2,2 1") != s2m("1 2,1 2"))
    assert(s2m("1 2 3 4,4 3 2 1") === s2m("1 2 3 4,4 3 2 1"))
  }

  test("toArray") {
    assert(m1 === new Matrix(m1.toArray))
    assert(m2 === new Matrix(m2.toArray))
    assert(m3 === new Matrix(m3.toArray))
    assert(m4 === new Matrix(m4.toArray))
  }

  test("vector to matrix") {
    assert(s2m("1,2,3,4") === Matrix(s2v("1 2 3 4")))
  }

  test("zero") {
    assert(m0 === m0.zero)
    assert(m0 === m3.zero)
    assert(m0 === Matrix.zero[Rational](2))
    assert(m01 === Matrix.zero[Rational](2, 3))
  }

  test("identity") {
    assert(id2 === Matrix.identity[Rational](2))
    assert(id3 === Matrix.identity[Rational](3))
    assert(id4 === Matrix.identity[Rational](4))
  }

  test("submatrix") {
    assert(id2 === id3.subMatrix(List(0, 1), List(0, 1)))
    assert(id2 === id3.subMatrix(0, 2, 0, 2))
    assert(id2 === id4.subMatrix(List(0, 2), List(0, 2)))
    assert(m1sub01 === m1.subMatrix(List(0, 1), List(0, 1)))
    assert(m1sub01 === m1.subMatrix(0, 2, 0, 2))
    assert(m1sub02 === m1.subMatrix(List(0, 2), List(0, 2)))
    assert(m1sub12 === m1.subMatrix(1, 2, 1, 2))

    assert(id4 === id4.subMatrix(List(0, 1, 2, 3), List(0, 1, 2, 3)))
    assert(id4 === id4.subMatrix(0, 4, 0, 4))
  }

  test("row") {
    assert(id4.row(2) === s2v("0 0 1 0"))
    assert(id4.row(0) === s2v("1 0 0 0"))
    assert(m1.row(1) === s2v("4 5 6"))
  }
  test("col") {
    assert(id4.col(2) === s2v("0 0 1 0"))
    assert(id4.col(0) === s2v("1 0 0 0"))
    assert(m1.col(1) === s2v("2 5 8"))
  }

  test("augment") {
    assert(m1.augment(m1) === s2m("1 2 3 1 2 3,4 5 6 4 5 6,7 8 9 7 8 9"))
    assert(id3.augment(id3) === s2m("1 0 0 1 0 0,0 1 0 0 1 0,0 0 1 0 0 1"))
    assert(s2m("0 1 2 4,5 6 7 8").augment(s2m("1,1")) === s2m("0 1 2 4 1,5 6 7 8 1"))
    intercept[IllegalArgumentException] { m1.augment(id2) }
  }

  test("map") {

  }

  test("mapWithIndex") {
    assert(m1.mapWithIndex((el, row, col) => el) === m1)
    assert(m3.mapWithIndex((el, row, col) => el) === m3)
    assert(id2.mapWithIndex((el, row, col) => el * (row+col)) === s2m("0 0,0 2"))
    assert(m1.mapWithIndex((el, row, col) => el + row) === s2m("1 2 3,5 6 7,9 10 11"))
  }

  test("mapRow") {
    assert(m1.mapRow(0, el => el + 2) === s2m("3 4 5,4 5 6,7 8 9"))
  }

  test("mapCol") {
    assert(m1.mapCol(0, el => el + 2) === s2m("3 2 3,6 5 6,9 8 9"))
  }

  test("foldLeft") {

  }

  test("forall") {

  }

  test("exists") {

  }

  test("addition") {
    assert(m1plusm2 === m1 + m2)
    assert(m0 === m3 + m4)
    intercept[IllegalArgumentException] {
      m1 + m3
    }
  }

  test("negation") {
    assert(-m1 === m1neg)
    assert(-m2 === m2neg)
  }

  test("multiplication by matrix") {
    assert(id3 === id3 * id3)
    assert(m1 === id3 * m1)
    assert(m1 === m1 * id3)
    assert(m1xm2 === m1 * m2)
    assert(m3xm4 === m3 * m4)
    intercept[IllegalArgumentException] {
      m1 * m3
    }
    intercept[IllegalArgumentException] {
      s2m("1 2 3,4 5 6") * s2m("2 3 1,5 6 4")
    }
  }

  test("multiplication by vector") {
    assert(v1 === id3*v1)
    assert(v1 === id3(v1))
    assert(m1xv1 === m1*v1)
    assert(m1xv1 === m1(v1))
  }

  test("isNonSingular") {
    assert(id4.isNonSingular)
    assert(m5.isNonSingular)
    assert(m6.isNonSingular)
    assert(m7.isNonSingular)
    assert(m8.isNonSingular)
  }

  test("inverse") {
    assert(id4.inverse == id4)
    assert(m5.inverse == m5inv)
    assert(m6.inverse == m6inv)
    assert(m7.inverse == m7inv)
    assert(m8.inverse == m8inv)
  }

  test("gauss") {
    assert(gauss1.gaussJordanElimination === gauss2)
    assert(gauss3.gaussJordanElimination === gauss2)

  }

}
