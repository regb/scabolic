package regolic.resolution

import org.scalatest.FunSuite

import regolic.asts.core.Trees._
import regolic.asts.fol.Manip._
import regolic.asts.fol.Trees._

class ResolutionSuite extends FunSuite {

  val sort = Sort("sort", List())
  private val x = Variable("x", sort)
  private val y = Variable("y", sort)
  private val z = Variable("z", sort)

  private val cSymbol = FunctionSymbol("c", List(), sort)
  private val c = FunctionApplication(cSymbol, List())
  private val dSymbol = FunctionSymbol("d", List(), sort)
  private val d = FunctionApplication(dSymbol, List())

  private val fSymbol = FunctionSymbol("f", List(sort), sort)
  private def f(t1: Term) = FunctionApplication(fSymbol, List(t1))
  private val gSymbol = FunctionSymbol("g", List(sort, sort), sort)
  private def g(t1: Term, t2: Term) = FunctionApplication(gSymbol, List(t1, t2))

  private val pSymbol = PredicateSymbol("p", List(sort))
  private def p(t1: Term) = PredicateApplication(pSymbol, List(t1))
  private val qSymbol = PredicateSymbol("q", List())
  private def q(t1: Term) = PredicateApplication(qSymbol, List(t1))

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

  test("Resolution") {
    //val f1 = Forall(x, Implies(p(x), q(x)))
    //val f2 = p(c)
    //val f3 = clausalNormalForm(f1)
    //val f4 = clausalNormalForm(f2)
    //println(f3)
    //println(f4)
    //val And(l1) = f3
    //val And(l2) = f4
    //Resolution(Or(List(Not(q(c)))) :: l1 ::: l2)

    //group theory: g is *, c is 1 and f is inverse
    val grp1 = Forall(x, Equals(g(c, x), x))
    val grp2 = Forall(x, Equals(g(f(x), x), c))
    val grp3 = Forall(x, Forall(y, Forall(z, Equals(g(g(x, y), z), g(x, g(y, z))))))

    val assumption = Forall(x, Equals(g(x, x), c))
    val conjecture = Forall(x, Forall(y, Equals(g(x, y), g(y, x))))

    val formula = And(grp1, grp2, grp3, assumption, Not(conjecture))
    println(formula)
    val And(lst1) = clausalNormalForm(grp1)
    val And(lst2) = clausalNormalForm(grp2)
    val And(lst3) = clausalNormalForm(grp3)
    val And(lst4) = clausalNormalForm(assumption)
    val And(lst5) = clausalNormalForm(Not(conjecture))

    val eq1 = Forall(x, Equals(x, x))
    val eq2 = Forall(x, Forall(y, Implies(Equals(x, y), Equals(y, x))))
    val eq3 = Forall(x, Forall(y, Forall(z, Implies(And(Equals(x, y), Equals(y, z)), Equals(x, z)))))
    val And(eqlst1) = clausalNormalForm(eq1)
    val And(eqlst2) = clausalNormalForm(eq2)
    val And(eqlst3) = clausalNormalForm(eq3)

    println(Resolution(lst1 ::: lst2 ::: lst3 ::: lst4 ::: lst5 ::: eqlst1 ::: eqlst2 ::: eqlst3))
  }


}
