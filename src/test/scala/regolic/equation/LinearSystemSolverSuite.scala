package regolic.equation

import org.scalatest.FunSuite
import regolic.asts.theories.real.Trees._
import regolic.asts.theories.real.Eval
import regolic.algebra.Rational

class LinearSystemSolverSuite extends FunSuite {

  import LinearSystemSolver._

  val x = Var("x")
  val y = Var("y")
  val z = Var("z")

  test("basic linear equation with unique solution") {
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

    val es51 = Equals(Add(List(x, y)), Zero())
    val es52 = Equals(Add(List(x, Neg(y))), One())
    val es53 = Equals(Mul(List(Num(2), Add(List(x, Neg(y))))), Num(2))
    val res5 = LinearSystemSolver(List(es51, es52, es53))
    assert(res5.isInstanceOf[Unique])
    val Unique(map5) = res5
    assert(map5(x) === Rational(1, 2))
    assert(map5(y) === Rational(-1, 2))
  }

  test("basic linear equation infeasible") {
    val es41 = Equals(Add(List(x, y)), Zero())
    val es42 = Equals(Add(List(x, y)), One())
    val res4 = LinearSystemSolver(List(es41, es42))
    assert(res4 == Infeasible)
  }

  test("basic linear equation infinite solutions") {
    val eq11 = Equals(Add(List(x, y, z)), Zero())
    val eq12 = Equals(Add(List(Neg(x), y, Neg(z))), One())
    val res1 = LinearSystemSolver(List(eq11, eq12))
    assert(res1.isInstanceOf[Infinite])
    val Infinite(freeVars, map1) = res1
    assert(freeVars === List(z))
    assert(Eval(map1(x), Map(z -> Rational(0))) === Rational(-1, 2))
    assert(Eval(map1(y), Map(z -> Rational(0))) === Rational(1, 2))
  }

}
