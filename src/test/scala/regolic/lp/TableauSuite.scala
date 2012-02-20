package regolic.lp

import regolic.algebra.{Rational, Vector, Matrix}

import org.scalatest.FunSuite

class TableauSuite extends FunSuite {

  def r(n: BigInt) = Rational(n)
  def r(n: BigInt, d: BigInt) = Rational(n, d)

  def s2t(str: String, basis: List[Int]): Tableau = {
    val rows: Array[Array[Rational]] = (str.split(',').map(s => s.split(' ').map(n => Rational(n))))
    val reducedCost = new Vector(rows(0).init)
    val value = rows(0).last
    val matrix = new Matrix(rows.tail)
    val systemMatrix = matrix.subMatrix(0, matrix.nbRow, 0, matrix.nbCol - 1)
    val basisSolution = Vector(matrix.subMatrix(0, matrix.nbRow, matrix.nbCol - 1, 1))
    new Tableau(basis, systemMatrix, reducedCost, basisSolution, value)
  }
  def s2m(str: String): Matrix[Rational] = new Matrix(str.split(',').map(s => s.split(' ').map(n => Rational(n))))
  def s2v(str: String): Vector[Rational] = new Vector(str.split(' ').map(n => Rational(n)))

  val t1 = s2t("-5 -4 -3 0 0 0 0," +
                 "2 3 1 1 0 0 5," +
                 "4 1 2 0 1 0 9," +
                 "3 4 2 0 0 1 10", List(3, 4, 5))
  val newt1 = s2t("0 -11/4 -1/2 0 5/4 0 45/4," +
                  "0 5/2 0 1 -1/2 0 1/2," +
                  "1 1/4 1/2 0 1/4 0 9/4," +
                  "0 13/4 1/2 0 -3/4 1 13/4", List(3, 0, 5))

  val t2 = s2t("0 0 0 -1 -5," +
               "1 0 -1 -2 1," +
               "0 1 2 3 1", List(0, 1))

  val newt2 = s2t("0 1/3 2/3 0 -14/3," +
                  "1 2/3 1/3 0 5/3," +
                  "0 1/3 2/3 1 1/3", List(0, 3))

  test("representation") {
  }

  test("equals") {
    val t1eq = s2t("-5 -4 -3 0 0 0 0," +
                 "2 3 1 1 0 0 5," +
                 "4 1 2 0 1 0 9," +
                 "3 4 2 0 0 1 10", List(3, 4, 5))
    val newt1eq = s2t("0 -11/4 -1/2 0 5/4 0 45/4," +
                      "0 5/2 0 1 -1/2 0 1/2," +
                      "1 1/4 1/2 0 1/4 0 9/4," +
                      "0 13/4 1/2 0 -3/4 1 13/4", List(3, 0, 5))

    assert(t1eq === t1)
    assert(newt1eq === newt1)

  }

  test("findPivot") {
    assert(t1.findPivot === 0)
    assert(t2.findPivot === 3)
  }

  test("findLeavingIndex") {
    assert(t1.findLeavingIndex(t1.findPivot) === 4)
    assert(t2.findLeavingIndex(t2.findPivot) === 1)
  }

  test("changeBasis") {
    assert(t1.changeBasis(0, 4) === newt1)
    assert(t2.changeBasis(3, 1) === newt2)
  }

  test("nextTableau") {
    assert(t1.nextTableau === newt1)
    assert(t2.nextTableau === newt2)
  }


}
