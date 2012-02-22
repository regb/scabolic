package regolic.asts.theories.real

import org.scalatest.FunSuite
import Trees._
import Manip._
import regolic.algebra.Rational

class ManipSuite extends FunSuite {

  val r0 = Rational(0)
  val r1 = Rational(1)
  val r2 = Rational(2)
  val r3 = Rational(3)
  val r4 = Rational(4)
  val r5 = Rational(5)
  val r19 = Rational(19)
  val r64 = Rational(64)
  val n0 = Num(r0)
  val n1 = Num(r1)
  val n2 = Num(r2)
  val n3 = Num(r3)
  val n4 = Num(r4)
  val n5 = Num(r5)
  val n19 = Num(r19)
  val n64 = Num(r64)
  val x = Var("x")
  val y = Var("y")
  val t1 = Add(List(
    n1,x,n2,Add(List(
      Add(List(n0,n2)),n0))))
  val pt1 = Add(List(
    Mul(List(
      n5, Pow(x, n0))),
    Mul(List(
      n1, Pow(x, n1)))))
  //val t2 = Div(Div(n64,n4),Div(Sub(n19,n3),n3))
  //val pt2 = Add(List(Mul(List(n3, Pow(x, n0)))))
  val t3 = Add(List(
    Mul(List(n2, x)), n1, Mul(List(x, x)), x))
  val pt3 = Add(List(Mul(List(n1, Pow(x, n0))), Mul(List(n3, Pow(x, n1))), Mul(List(n1, Pow(x, n2)))))
  //val t4 = Div(n1, x)
//  val t3 = Sub(Sub(Sub(2,1),Sub(x,2)), Sub(2,1))
//  val t4 = Mul(List(2, Add(List(2, Add(List(1,7,Mul(List(3,x))))))))
//  val t5 = Mul(List(Add(List(Mul(List(Div("a","b"),4)),12,Div(x,2))),Add(List(x,y,1)),4,Div("a","a")))
//  val t6 = List(Add(List(x, 1)), Add(List(y, "z", 2)), Div("a", "b"), 5)
//  val t7 = Add(Add(List(x, 2, 3)) ::  Mul(List(Add(List(y, "z" )), "a" )) :: Nil)
//  val t8 = Div(Mul(List(x, 2)), 2)
//  val t9 = Div(x,0)
//  val t10 = Div(Mul(List(Add(List(x,x)),Add(List(y,1)))), x)
//  val t11 = Mul(List(2,Add(List(0,Mul(List("x1",Mul(List("x2",3,1)),"x3")),3)),Add(List(Mul(List(Mul(List(3,"x4","x5")),Div(3,3),2)),0,3))))
//  val t12 = Mul(List(2,Add(List(1,1)), Add(List(1,1))))
//  val t13 = Add(List("y", 2, Pow("x",3), 0, "x", Pow("z",2), Pow(Add(List("y",1)), 9), Pow("z", 2)))


  test("polynomialForm: basic") {
  /*
    val op1 = polynomialForm(t1, x)
    assert(op1 === pt1)
    //val op2 = polynomialForm(t2, x)
    //assert(op2 === pt2)
    val op3 = polynomialForm(t3, x)
    assert(op3=== pt3)
    */
  }


}
