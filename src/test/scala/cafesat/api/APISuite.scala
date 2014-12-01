package cafesat.api

import FormulaBuilder._
import Solver._

import org.scalatest.FunSuite


class APISuite extends FunSuite {

  val x1 = propVar()
  val x2 = propVar()

  test("api unsat example") {
    val f1 = (x1 || x2) && !x1
    val result = solveForSatisfiability(f1 && !x2)
    assert(result === None)
  }

  test("Basic boolean operators") {
    val f1 = (x1 || x2) && !x1
    val result = solveForSatisfiability(f1)
    assert(result !== None)
    result.foreach(model => {
      assert(!model(x1))
      assert(model(x2))
    })
  }

  test("Test if and only iff") {
    val f1 = (x1 iff x2) && !x1
    val r1 = solveForSatisfiability(f1 && x2)
    assert(r1 === None)
    val r2 = solveForSatisfiability(f1 && !x2)
    assert(r2 !== None)
    r2.foreach(model => {
      assert(!model(x1))
      assert(!model(x2))
    })
  }

  test("Test xor operator") {
    val f1 = (x1 xor x2) && !x1
    val r1 = solveForSatisfiability(f1 && !x2)
    assert(r1 === None)
    val r2 = solveForSatisfiability(f1 && x2)
    assert(r2 !== None)
    r2.foreach(model => {
      assert(!model(x1))
      assert(model(x2))
    })
  }


  test("Simple circuit") {
    val p = propVar("p")
    val q = propVar("q")
    val np = propVar("p'")
    val nq = propVar("q'")
    val c1 = propVar("c1")
    val c2 = propVar("c2")
    val r = propVar("r")

    val f = (
      (np iff !p) &&
      (nq iff !q) &&
      (c1 iff (!p || q)) &&
      (c2 iff (p || !q)) &&
      (r iff (c1 && c2)) &&
      (!p iff r)
    )

    val r1 = solveForSatisfiability(f && p)
    assert(r1 !== None) 
    r1.foreach(model => {
      assert(model(p))
      assert(!model(q))
      assert(!model(r))
    })

    val r2 = solveForSatisfiability(f && q)
    assert(r2 === None)

  }

}
