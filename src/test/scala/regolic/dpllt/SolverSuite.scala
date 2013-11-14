package regolic
package dpllt

import Solver.Results._

import scala.util.Random

import org.scalatest.FunSuite

class SolverSuite extends FunSuite {

  val a = new PropositionalLiteral(0, true) 
  val b = new PropositionalLiteral(1, true) 
  val c = new PropositionalLiteral(2, true) 
  val d = new PropositionalLiteral(3, true) 
  val e = new PropositionalLiteral(4, true) 
  val na = new PropositionalLiteral(0, false) 
  val nb = new PropositionalLiteral(1, false) 
  val nc = new PropositionalLiteral(2, false) 
  val nd = new PropositionalLiteral(3, false) 
  val ne = new PropositionalLiteral(4, false) 

  test("trivial sat propositional problems") {
    val s1 = new Solver(3, new PropositionalSolver)
    s1.addClause(Set(a))
    assert(s1.solve().isInstanceOf[Satisfiable])

    val s2 = new Solver(3, new PropositionalSolver)
    s2.addClause(Set(a, b))
    assert(s2.solve().isInstanceOf[Satisfiable])

    val s3 = new Solver(3, new PropositionalSolver)
    s3.addClause(Set(a))
    s3.addClause(Set(b))
    assert(s3.solve().isInstanceOf[Satisfiable])

    val s4 = new Solver(3, new PropositionalSolver)
    s4.addClause(Set(na))
    assert(s4.solve().isInstanceOf[Satisfiable])

    val s5 = new Solver(3, new PropositionalSolver)
    s5.addClause(Set(na, nb))
    assert(s5.solve().isInstanceOf[Satisfiable])

    val s6 = new Solver(3, new PropositionalSolver)
    s6.addClause(Set(na))
    s6.addClause(Set(nb))
    assert(s6.solve().isInstanceOf[Satisfiable])

    val s7 = new Solver(3, new PropositionalSolver)
    s7.addClause(Set(a))
    s7.addClause(Set(nb))
    assert(s7.solve().isInstanceOf[Satisfiable])

    val s8 = new Solver(3, new PropositionalSolver)
    s8.addClause(Set(na, b))
    assert(s8.solve().isInstanceOf[Satisfiable])
  }

  test("trivial unsat propositional problems") {
    val s1 = new Solver(3, new PropositionalSolver)
    s1.addClause(Set(a))
    s1.addClause(Set(na))
    assert(s1.solve() === Unsatisfiable)

    val s2 = new Solver(3, new PropositionalSolver)
    s2.addClause(Set(a, b))
    s2.addClause(Set(na))
    s2.addClause(Set(nb))
    assert(s2.solve() === Unsatisfiable)

    val s3 = new Solver(3, new PropositionalSolver)
    s3.addClause(Set(a))
    s3.addClause(Set(na, b))
    s3.addClause(Set(nb))
    assert(s3.solve() === Unsatisfiable)
  }

  test("propositional basic sat") {
    val s1 = new Solver(5, new PropositionalSolver)
    s1.addClause(Set(a, b, c))
    s1.addClause(Set(na, nb, nc))
    s1.addClause(Set(a, nb))
    s1.addClause(Set(b, nc))
    s1.addClause(Set(na, nc))
    assert(s1.solve().isInstanceOf[Satisfiable])

    val s2 = new Solver(5, new PropositionalSolver)
    s2.addClause(Set(a, b, c, d))
    s2.addClause(Set(na, nb, ne))
    s2.addClause(Set(a, nb, nc))
    s2.addClause(Set(b, nc, e))
    s2.addClause(Set(na, nc, d, e))
    s2.addClause(Set(a, nc, nd, e))
    s2.addClause(Set(a, b, nd, ne))
    assert(s2.solve().isInstanceOf[Satisfiable])

    val s3 = new Solver(5, new PropositionalSolver)
    s3.addClause(Set(a, b, c, d))
    s3.addClause(Set(a, nb, nc))
    s3.addClause(Set(a, nc, nd, e))
    s3.addClause(Set(a, b, nd, ne))
    s3.addClause(Set(na, nc, d, e))
    s3.addClause(Set(na, nb, ne))
    s3.addClause(Set(na, b, e))
    s3.addClause(Set(na, nb, e))
    s3.addClause(Set(na, b, ne))
    s3.addClause(Set(b, nc, e))
    assert(s3.solve().isInstanceOf[Satisfiable])
  }

  test("propositional basic unsat") {
    val s1 = new Solver(5, new PropositionalSolver)
    s1.addClause(Set(a, b, c))
    s1.addClause(Set(na, nb, nc))
    s1.addClause(Set(a, nb))
    s1.addClause(Set(b, nc))
    s1.addClause(Set(na, nc))
    s1.addClause(Set(na, nb, c))
    s1.addClause(Set(c, b))
    assert(s1.solve() === Unsatisfiable)

    val s3 = new Solver(5, new PropositionalSolver)
    s3.addClause(Set(a, b, c, d))
    s3.addClause(Set(a, nb, nc))
    s3.addClause(Set(a, nc, nd, e))
    s3.addClause(Set(a, b, nd, ne))
    s3.addClause(Set(na, nc, d, e))
    s3.addClause(Set(na, nb, ne))
    s3.addClause(Set(na, b, e))
    s3.addClause(Set(na, nb, e))
    s3.addClause(Set(na, b, ne))
    s3.addClause(Set(b, nc, e))
    s3.addClause(Set(b, nc, ne))
    s3.addClause(Set(b, c, nd))
    s3.addClause(Set(b, c, d))
    s3.addClause(Set(c, a, nd))
    s3.addClause(Set(c, a, d))
    assert(s3.solve() === Unsatisfiable)
  }

}
