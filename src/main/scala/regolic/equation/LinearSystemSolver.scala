package regolic.equation

import regolic.algebra.Rational
import regolic.algebra.Matrix
import regolic.algebra.Vector
import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees.And
import regolic.asts.theories.real.Eval
import regolic.asts.theories.real.Manip._
import regolic.asts.theories.real.Trees._

import scala.collection.mutable.HashMap

object LinearSystemSolver {

  def apply(equations: List[PredicateApplication]): Map[Variable, Term] = {
    require(equations.forall{ case Equals(_, _) => true case _ => false })

    def coeffVar(v: Variable, t: Term): Rational = if(!contains(t, v)) Rational.zero else polynomialForm(t, v) match {
      case Add(Mul(coeff :: Pow(v2, Num(r)) :: Nil) :: rest :: Nil) if v2==v && r.isOne => Eval(coeff, Map())
      case Add(Mul(coeff :: Pow(v2, Num(r)) :: Nil) :: Nil) if v2==v && r.isZero => Rational.zero
      case _ => throw new IllegalArgumentException("not a linear expression: " + t)
    }

    val lhSides: Array[Term] = equations.map{ case Equals(t1, t2) => Sub(t1, t2) }.toArray
    val nbEqus = lhSides.length
    val allVars: Array[Variable] = equations.map(vars).flatten.distinct.toArray
    val nbVars = allVars.length
    val cstsRhs: Vector[Rational] = Vector(lhSides.map(t => -Eval(t, Map(allVars.map(v => (v, Rational(0))): _*))))
    val matrixCoef: Matrix[Rational] = Matrix(lhSides.map(lhs => allVars.map(v => coeffVar(v, lhs))))
    val augmentedMatrixCoef: Matrix[Rational] = matrixCoef.augment(cstsRhs)
    augmentedMatrixCoef.gaussJordanElimination match {
      case Some(reducedMatrix) => {
        val map = new HashMap[Variable, Term]
        var r = 0;
        var c = 0;
        while(c < nbVars && r < nbEqus) {
          if(reducedMatrix(r, c).isZero) {
            map.put(allVars(c), Zero())
            c = c+1
          } else {
            map.put(allVars(c), Num(reducedMatrix(r, nbVars)))
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
            map.put(allVars(c), Zero())
            c += 1
          }
        }
        Map(map.toList: _*)
      }
      case None => sys.error("non linear")
    }
  }

}
