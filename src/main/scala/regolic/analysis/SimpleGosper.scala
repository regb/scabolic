package regolic.analysis

import Preamble._
import regolic.algebra.Rational
import regolic.equation.LinearSystemSolver

object SimpleGosper {

  /*
  * compute the closed formula of the sum over variable, from 0
  * to upperBound of the expression: 
  * (variable^power) * (expBase^variable)
  * using a simple form of the Gosper algorithm
  * The result is an expression depending of the upperBound variable
  * See the book Concrete Mathematics (Knuth, Graham, ...) for detail of the algorithm
  */
  def apply(variable: Variable, power: Term, expBase: Term, upperBound: Variable): Term = {

    val h = (variable ^ power) * (expBase ^ variable)
    val polynomeQ = expBase
    val generalY = generatePolynomial(variable, power match {
        case Num(Rational(n, d)) if d == 1 => n.intValue + 1
        case _ => sys.error("not expected")
      })
    val listVars = vars(generalY).filterNot(_ == variable)
    val gosperRhs = polynomeQ*substitute(generalY, variable, variable + 1) - generalY
    val polynomialFormRhs = polynomialForm(gosperRhs, variable)

    def generateEquations(polynomial: Term): List[Formula] = polynomial match {
      case Add(Mul(t :: Pow(_, n@Num(_)) :: Nil) :: ms) => Equals(t, if(n==power) 1 else 0) :: generateEquations(Add(ms))
      case Add(Nil) => Nil
      case _ => sys.error("unexpected error, todo " + polynomial)
    }

    val lEquations = generateEquations(polynomialFormRhs)
    val map = LinearSystemSolver(lEquations)
    val nMap = listVars.foldLeft(map)((amap, v) => if(!amap.contains(v)) amap + (v -> 0) else amap)
    val polynomeY = substitute(generalY, nMap)

    //TODO
    val g = (h*polynomeY) / (polynomeQ*substitute(polynomeY, variable, variable + 1) - polynomeY)

    //hack for the base cases, don't know why it worked... Laura didn't neither
    val g0 = substitute(g, variable, 3) - substitute(h, variable, 0) - substitute(h, variable, 1) - substitute(h, variable, 2)
    val gnp1 = substitute(g, variable, upperBound + 1)

    val res = gnp1 - g0

    simplify(res)
  }


  private def generatePolynomial(v: Variable, degree: Int): Term = {
    def iter(d: Int, acc: List[Term]): List[Term] =
      if(d == 0) 
        freshVar("c") :: acc 
      else 
        iter(d-1, Mul(List(freshVar("c"), Pow(v, Num(Rational(d))))) :: acc)
    Add(iter(degree, Nil))
  }
      

}
