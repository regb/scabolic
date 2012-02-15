package regolic.calculus

import org.scalatest.FunSuite
import Preamble._
//import Differential._

class DifferentialSuite extends FunSuite {

  //TODO method in asts.theories.real to check whether two terms are equal, maybe returning an Option[Boolean], should be put in the same object as Eval

  val x = Var("x")
  val t1 = x*x*x + 3*x - 2
  val dt1 = 3*x*x + 3

  def testEq(t1: Term, t2: Term): Boolean = {
    val vs1 = vars(t1)
    val vs2 = vars(t2)
    val vs = vs1.intersect(vs2)
      vs.forall(v =>
        (-50 to 50).forall(i =>
          eval(t1, Map(v -> i)) == eval(t2, Map(v -> i))))
  }

  test("derive: simple derivative") {
    val dt = derive(t1, x)
    assert(testEq(dt, dt1)) 
  }

}
