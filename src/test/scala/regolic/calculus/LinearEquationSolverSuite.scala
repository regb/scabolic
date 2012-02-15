package regolic.calculus

import org.scalatest.FunSuite
import regolic.asts.theories.real.Trees._
import regolic.algebra.Rational

class LinearEquationSolverSuite extends FunSuite {

  val x = Var("x")
  val y = Var("y")
  val z = Var("z")

  test("basic linear equation") {
    val es11 = Equals(y, Add(List(x, Num(2))))
    val es12 = Equals(y, Add(List(z, Num(2))))
    val es13 = Equals(z, Sub(Neg(x), Num(4)))
    val map1 = LinearEquationSolver(List(es11, es12, es13))
    assert(map1(x) === Num(Rational(-2)))
    assert(map1(y) === Num(Rational(0)))
    assert(map1(z) === Num(Rational(-2)))

    val es21 = Equals(Sub(x, y), Num(4))
    val es22 = Equals(
        Add(List(x, Mul(List(y, Num(2))))),
        Num(3))
    val map2 = LinearEquationSolver(List(es21, es22))
    assert(map2(x) === Num(Rational(11, 3)))
    assert(map2(y) === Num(Rational(-1, 3)))

    val es31 = Equals(y, Add(List(x, Num(2), Mul(List(Num(4), z)))))
    val es32 = Equals(y, Add(List(z, Num(2), Neg(x))))
    val es33 = Equals(z, Add(List(Sub(Neg(x), Num(4)), Mul(List(Num(3), y)))))
    val map3 = LinearEquationSolver(List(es31, es32, es33))
    println(map3)
    assert(map3(x) === Num(Rational(3,8)))
    assert(map3(y) === Num(Rational(11,8)))
    assert(map3(z) === Num(Rational(-1,4)))
  }

}
