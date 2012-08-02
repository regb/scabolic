package regolic.resolution

import org.scalatest.FunSuite

import regolic.asts.core.Trees._
import regolic.asts.fol.Manip._
import regolic.asts.fol.Trees._

class ResolutionSuite extends FunSuite {

  val sort = Sort("sort", List())
  private val x = Variable("x", sort)
  private val y = Variable("y", sort)

  private val cSymbol = FunctionSymbol("c", List(), sort)
  private val c = FunctionApplication(cSymbol, List())
  private val dSymbol = FunctionSymbol("d", List(), sort)
  private val d = FunctionApplication(dSymbol, List())

  private val fSymbol = FunctionSymbol("f", List(sort), sort)
  private def f(t1: Term) = FunctionApplication(fSymbol, List(t1))
  private val gSymbol = FunctionSymbol("f", List(sort, sort), sort)
  private def g(t1: Term, t2: Term) = FunctionApplication(gSymbol, List(t1, t2))

  private val pSymbol = PredicateSymbol("p", List(sort))
  private def p(t1: Term) = PredicateApplication(pSymbol, List(t1))

  private val qSymbol = PredicateSymbol("q", List())
  private val rSymbol = PredicateSymbol("r", List())
  private val sSymbol = PredicateSymbol("s", List())
  private val tSymbol = PredicateSymbol("t", List())
  private val q = PredicateApplication(qSymbol, List())
  private val r = PredicateApplication(rSymbol, List())
  private val s = PredicateApplication(sSymbol, List())
  private val t = PredicateApplication(tSymbol, List())


  test("Unification") {
    val t1 = g(x, f(x))
    val t2 = g(y, y)
    println(Resolution.unify(t1, t2))
  }

}
