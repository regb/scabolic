package cafesat.api

import API._

import org.scalatest.FunSuite


class APISuite extends FunSuite {

  val x1 = boolVar()
  val x2 = boolVar()

  test("api unsat example with assumption") {
    val f1 = (x1 || x2) && !x1
    val result = solveForSatisfiability(f1 && !x2)
    assert(result === None)
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
}
