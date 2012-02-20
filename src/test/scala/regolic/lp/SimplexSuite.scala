package regolic.lp

import regolic.algebra.{Rational, Vector, Matrix}
import org.scalatest.FunSuite
import Simplex.{Optimal, Infeasible, Unbounded}

class SimplexSuite extends FunSuite {

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

  val c1 = s2v("1 1 1 0")

  val b1 = s2v("3 2 5 1")

  val A1 = s2m("1 2 3 0," +
               "-1 2 6 0," +
               "0 4 9 0," +
               "0 0 3 1")

  val lp1 = new StandardLinearProgram(c1, A1, b1)

  val c2 = s2v("1 0")
  val b2 = s2v("2 1")
  val A2 = s2m("1 1," +
               "1 0")
  val lp2 = new StandardLinearProgram(c2, A2, b2)

  val c3 = s2v("1 0")
  val b3 = s2v("2 1")
  val A3 = s2m("1 1," +
               "1 1")
  val lp3 = new StandardLinearProgram(c3, A3, b3)

  val c4 = s2v("-1 0")
  val b4 = s2v("2 0")
  val A4 = s2m("1 -1," +
               "0 0")
  val lp4 = new StandardLinearProgram(c4, A4, b4)
  
  test("phaseOne") {
  }

  test("phaseTwo") {
  }

  test("apply") {
    assert(Simplex(lp1) === Optimal(s2v("1/2 5/4 0 1")))
    assert(Simplex(lp2) === Optimal(s2v("1 1")))
    assert(Simplex(lp3) === Infeasible)
    assert(Simplex(lp4) === Unbounded)
  }

}
