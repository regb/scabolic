package regolic.calculus

import org.scalatest.FunSuite
import Preamble._

class SimpleGosperSuite extends FunSuite {
  /*
  * compute the closed formula of the sum over variable, from 0
  * to upperBound of the expression: 
  * (variable^power) * (expBase^variable)
  * using a simple form of the Gosper algorithm
  * The result is an expression depending of the upperBound variable
  * See the book Concrete Mathematics (Knuth, Graham, ...) (or read the code ...) for detail of the algorithm
  */
  //def apply(variable: Variable, power: Term, expBase: Term, upperBound: Variable): Term = {

  val k = Var("k")
  val n = Var("n")

  def testEq(t1: Term, t2: Term): Boolean = {
    val vs1 = vars(t1)
    val vs2 = vars(t2)
    val vs = vs1.intersect(vs2)
      vs.forall(v =>
        (0 to 100).forall(i =>
          eval(t1, Map(v -> i)) == eval(t2, Map(v -> i))))
  }

  test("basic") {
    val s1 = SimpleGosper(k, 0, 1, n) 
    assert(testEq(s1, n+1))

    val s2 = SimpleGosper(k, 1, 1, n) 
    assert(testEq(s2, n*(n+1)/2))

    val s3 = SimpleGosper(k, 2, 1, n)
    assert(testEq(s3, n*(n+1)*(2*n+1)/6))

    val s4 = SimpleGosper(k, 0, 2, n)
    assert(testEq(s4, (1 - (2 ^ (n + 1))) / (1 - 2)))

    val s5 = SimpleGosper(k, 0, 3, n)
    assert(testEq(s5, (1 - (3 ^ (n + 1))) / (1 - 3)))
  }

}
