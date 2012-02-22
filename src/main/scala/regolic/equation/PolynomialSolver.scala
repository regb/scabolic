package regolic.equation

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.theories.real.Trees._
import regolic.asts.theories.real.Manip._

object PolynomialSolver {

  //finds all roots of a given polynome
  def polynomialRoots(polynomial: Term): Set[(Term, Int)] = {
    sys.error("TODO")
    //require(isSingleVarPolynomial(polynomial))
    //val variables = vars(polynomial)
    //assert(variables.size == 1)
    //val variable = variables.toList.head
    //val stdForm = polynomialForm(polynomial, variable)
    //stdForm match {
    //  case Add(List(Mul(List(Num(coeff), _)))) => 
    //    sys.error("Cannot find roots for a polynomial of degree 0")
    //  case Add(List(
    //        Mul(List(Num(coeff0), _)), 
    //        Mul(List(Num(coeff1), _)))) => Set( (Num(-coeff0/coeff1), 1) )
    //  case Add(List(
    //        Mul(List(Num(c), _)),
    //        Mul(List(Num(b), _)),
    //        Mul(List(Num(a), _)))) => {
    //    val discriminant = b*b - 4*a*c
    //    if(discriminant < 0) Set()
    //    else if(discriminant == 0) Set( (Num(-b/2*a), 2) )
    //    else Set(
    //          (Div(Sub(Num(-b), Sqrt(Num(discriminant))), Num(2*a)), 1),
    //          (Div(Add(List(Num(-b), Sqrt(Num(discriminant)))), Num(2*a)), 1))
    //  }
    //  case Add(List( //depressed cubic polynomial: x^3 + ax + b
    //        Mul(List(Num(b), _)),
    //        Mul(List(Num(a), _)),
    //        Mul(List(Zero(), _)),
    //        Mul(List(One(), _)))) => {
    //    //cardano's method
    //    /*
    //    val v = variable //can take the same variable for the sub polynomial to be solved, doesn't matter
    //    val quadraticEq = Add(List(
    //          Mul(List(v, v)),
    //          Mul(List(Num(-b), v)),
    //          Num(-(a*a*a)/27)))
    //    val roots = polynomialRoots(quadraticEq)
    //    val oneRoot = roots.find{ case (r, _) => true }.get._1
    //    val t = Mul(List(oneRoot, oneRoot, oneRoot))
    //    val s = Div(Num(a), Mul(List(Num(3), t)))
    //    val depressedRoot = Mul(List(t, s))
    //    Set((depressedRoot, 1))
    //    */
    //    //TODO
    //    sys.error("Cubic roots are not implemented yet")
    //  }
    //  case _ => sys.error("Cannot handle such polynomials")
    //}
  }


}
