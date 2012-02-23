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
import scala.collection.mutable.ListBuffer

object LinearSystemSolver {

  sealed trait Result
  case object Infeasible extends Result
  case class Unique(map: Map[Variable, Rational]) extends Result
  case class Infinite(freeVars: List[Variable], map: Map[Variable, Term]) extends Result

  def apply(equations: List[PredicateApplication]): Result = {
    require(equations.forall{ case Equals(_, _) => true case _ => false })
    println("Solving: " + equations.mkString("\n"))

    def coeffVar(v: Variable, t: Term): Rational = if(!contains(t, v)) Rational.zero else polynomialForm(t, v) match {
      case Add(Mul(coeff :: Pow(v2, Num(r)) :: Nil) :: rest :: Nil) if v2==v && r.isOne => Eval(coeff, Map())
      case Add(Mul(coeff :: Pow(v2, Num(r)) :: Nil) :: Nil) if v2==v && r.isZero => Rational.zero
      case _ => throw new IllegalArgumentException("not a linear expression: " + t)
    }

    val lhSides: Array[Term] = equations.map{ case Equals(t1, t2) => Sub(t1, t2) }.toArray
    val nbEqus = lhSides.length
    val allVars: Array[Variable] = equations.map(vars).flatten.distinct.toArray
    println("list of variables: " + allVars.mkString(" "))
    val nbVars = allVars.length
    val cstsRhs: Vector[Rational] = Vector(lhSides.map(t => -Eval(t, Map(allVars.map(v => (v, Rational(0))): _*))))
    val matrixCoef: Matrix[Rational] = Matrix(lhSides.map(lhs => allVars.map(v => coeffVar(v, lhs))))
    val augmentedMatrixCoef: Matrix[Rational] = matrixCoef.augment(cstsRhs)
    println("the matrix: " + augmentedMatrixCoef)
    val reducedMatrix = augmentedMatrixCoef.gaussJordanElimination
    println("Here is the reduced Matrix:\n" + reducedMatrix)

    val freeVars = new ListBuffer[Variable]
    val map = new HashMap[Variable, Term]
    var isInfeasible = false
    for(row <- 0 until reducedMatrix.nbRow) {
      val pivot = reducedMatrix.row(row).indexOf(Rational.one)
      if(pivot == -1) {
        //this should nnly happen if the row has all zeros or all zeros except for the augmented column which takes another value
        assert((0 until (reducedMatrix.nbCol-1)).forall(i => reducedMatrix(row, i) == Rational.zero))
        if(reducedMatrix(row, reducedMatrix.nbCol-1) != Rational.zero)
          isInfeasible = true
      } else if(pivot == reducedMatrix.nbCol - 1) {
        //in that case it means the row contains all zeros and a one in the augmented column, thus infeasible 
        isInfeasible = true
      } else {
        val constraint: Term = Sub(
          Num(reducedMatrix(row, reducedMatrix.nbCol-1)),
          Add(reducedMatrix.row(row).toList.zipWithIndex.map {
            case (coef, i) => 
              if(i != pivot && coef != Rational.zero && i < nbVars) Mul(List(Num(coef), allVars(i))) else Zero()
          }))
        println("variable " + allVars(pivot) + " is constrained to be: " + constraint)
        map.put(allVars(pivot), constraint)
      }
    }

    val fixedVars = map.keySet
    if(isInfeasible)
      Infeasible
    else if(fixedVars.size == nbVars)//.forall(t => !exists(t, { case Var(_) => true case _ => false })))
      Unique(map.toMap.map{ case (v, t) => (v, Eval(t, Map())) })
    else
      Infinite(allVars.toList -- fixedVars.toList, map.toMap.map{ case (v, t) => (v, simplify(t)) })

  }

  //Arbitrarly return one valid assignment if there exists some
  def findAssignment(equations: List[PredicateApplication]): Option[Map[Variable, Rational]] = apply(equations) match {
    case Infeasible => None
    case Unique(map) => Some(map)
    case Infinite(freeVars, map) => {
      val freeVarsAssignment = freeVars.map(v => (v, Rational(0))).toMap
      Some(map.map{ case (v, t) => (v, Eval(t, freeVarsAssignment)) })
    }
  }

}
