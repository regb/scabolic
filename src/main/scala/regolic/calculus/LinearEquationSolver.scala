package regolic.calculus

import regolic.calculus.Trees._
import regolic.asts.core.{Manip => CoreM}
import regolic.algebra.Rational
import regolic.algebra.Matrix
import regolic.asts.theories.real.Eval
import regolic.asts.theories.real.Manip._

import scala.collection.mutable.HashMap

object LinearEquationSolver {

  class LinearEquation(eq: Formula) {

  }

  def apply(equations: List[Formula]): Map[Variable, Term] = {

    def coeffVar(v: Variable, t: Term): Rational = if(CoreM.contains(t, v)) polynomialForm(t, v) match {
      case Add(h :: Mul(coeff :: Pow(v2, Number(r)) :: Nil) :: Nil) if v2==v && r.isOne => Eval(coeff, Map())
      case Add(Mul(coeff :: Pow(v2, Number(r)) :: Nil) :: Nil) if v2==v && r.isZero => Rational(0)
      case x => sys.error("not linear expression: " + t)
    } else Rational(0)

    val lhSides = equations.map{ case Equals(t1, t2) => Sub(t1, t2) case _ => sys.error("unexpected") }
    val nbEqus = lhSides.length
    val listVars = CoreM.vars(And(equations)).toList
    val nbVars = listVars.length
    val cstsRhs: List[Rational] = lhSides.map(t => -Eval(t, Map(listVars.map(v => (v, Rational(0))): _*)))
    val matrixList: List[List[Rational]] = lhSides.map(lhs => listVars.map(v => coeffVar(v, lhs)))
    val augmentedMatrixList: List[List[Rational]] = List.range(0, matrixList.length).map(i => matrixList(i) ::: List(cstsRhs(i))) 
    val matrixArray = augmentedMatrixList.map(l => l.toArray).toArray
    val matrix = new Matrix[Rational](matrixArray)
    matrix.gaussJordanElimination match {
      case Some(reducedMatrix) => {
        val map = new HashMap[Variable, Term]
        var r = 0;
        var c = 0;
        while(c < nbVars && r < nbEqus) {
          if(reducedMatrix(r, c).isZero) {
            map.put(listVars(c), Zero())
            c = c+1
          } else {
            map.put(listVars(c), Number(reducedMatrix(r, nbVars)))
            r += 1
            c += 1
          }
        }
        if(r < nbEqus) {
          while(r < nbEqus) {
            if(reducedMatrix(r, nbVars).isZero) 
              r += 1 
            else 
              sys.error("no solution to the equation: " + equations)
          }
        } else if(c < nbVars) {
          while(c < nbVars) {
            map.put(listVars(c), Zero())
            c += 1
          }
        }
        Map(map.toList: _*)
      }
      case None => sys.error("non linear")
    }
  }

}
