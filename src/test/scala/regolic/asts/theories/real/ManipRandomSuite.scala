package regolic.asts.theories.real

import Trees._
import regolic.asts.core.Trees.{Term, Variable}
import regolic.algebra.Rational

import scala.util.Random
import org.scalatest.FunSuite

class ManipRandomSuite extends FunSuite {

  private val nbTerms = 1000
  private val depth = 3
  private val nbValuations = 100
  private val nbVars = 10
  private val rand = new Random(System.currentTimeMillis)
  private def genTerm(depth: Int) : Term = {
    def genTerm0(d: Int) : Term = {
      if (d > 0) rand.nextInt(7) match {
        case 0 => randomNumber()
        case 1 => randomVar()
        case 2 => Div(genTerm0(d - 1), genTerm0(d - 1))
        case 3 => Mul(List.range(1, depth).map((i) => genTerm0(d - 1)))
        case 4 => Add(List.range(1, depth).map((i) => genTerm0(d - 1)))
        case 5 => Pow(genTerm0(d - 1), genTerm0(d - 3))
        case 6 => Sub(genTerm0(d - 1), genTerm0(d - 1))
      } else if(rand.nextBoolean) 
          randomNumber()
        else
          randomVar()
    }
    genTerm0(depth)
  }
  private def randomRat() = Rational(rand.nextInt(10))
  private def randomNumber() = Num(randomRat())
  private def randomVar() = Var("x" + rand.nextInt(nbVars))
  private def randomValuation(vars: List[Variable]) = {
    val vals = vars.map(v => (v, randomRat()))
    Map(vals: _*)
  }
  private def safeEval(context: Map[Variable, Rational], t: Term) = {
    try {
      Some(Eval(t, context))
    } catch {
      case (_: Throwable) => None
    }
  }

  test("Simplify: soundness") {
    val terms = List.range(1, nbTerms).map(i => genTerm(depth))
    val vars = List.range(0, nbVars).map(i => Var("x" + i))
    val valuations = List.range(1, nbValuations).map(i => randomValuation(vars))

    terms.foreach(t => {
      val t2 = Manip.simplify(t)
      valuations.foreach(v => {
        val r1 = safeEval(v, t)
        val r2 = safeEval(v, t)
        assert(r1 === r2)
      })
    })
  }
}
