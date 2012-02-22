package regolic.equation

import org.scalatest.FunSuite
import regolic.asts.theories.real.Trees._
import regolic.algebra.Rational

class LinearSystemSolverSuite extends FunSuite {

  import LinearSystemSolver._

  val x = Var("x")
  val y = Var("y")
  val z = Var("z")

  test("basic linear equation") {
    val es11 = Equals(y, Add(List(x, Num(2))))
    val es12 = Equals(y, Add(List(z, Num(2))))
    val es13 = Equals(z, Sub(Neg(x), Num(4)))
    val res1 = LinearSystemSolver(List(es11, es12, es13))
    assert(res1.isInstanceOf[Unique])
    val Unique(map1) = res1
    assert(map1(x) === Rational(-2))
    assert(map1(y) === Rational(0))
    assert(map1(z) === Rational(-2))

    val es21 = Equals(Sub(x, y), Num(4))
    val es22 = Equals(
        Add(List(x, Mul(List(y, Num(2))))),
        Num(3))
    val res2 = LinearSystemSolver(List(es21, es22))
    assert(res2.isInstanceOf[Unique])
    val Unique(map2) = res2
    assert(map2(x) === Rational(11, 3))
    assert(map2(y) === Rational(-1, 3))

    val es31 = Equals(y, Add(List(x, Num(2), Mul(List(Num(4), z)))))
    val es32 = Equals(y, Add(List(z, Num(2), Neg(x))))
    val es33 = Equals(z, Add(List(Sub(Neg(x), Num(4)), Mul(List(Num(3), y)))))
    val res3 = LinearSystemSolver(List(es31, es32, es33))
    assert(res3.isInstanceOf[Unique])
    val Unique(map3) = res3
    assert(map3(x) === Rational(3,8))
    assert(map3(y) === Rational(11,8))
    assert(map3(z) === Rational(-1,4))
  }

}
