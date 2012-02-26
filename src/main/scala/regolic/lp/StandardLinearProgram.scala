package regolic.lp

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.theories.real.Trees._
import regolic.asts.theories.real.Manip._
import regolic.asts.theories.real.Eval

import regolic.algebra.Rational
import regolic.algebra.Vector
import regolic.algebra.Matrix

import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer

//a standard linear program is a canonical form of a linear program where we try to minimize 
//a function c.x under some constraints that can be writen Ax = b with x >= 0
//c, b and A are standard names in that situation, so we make use of them

class StandardLinearProgram(val c: Vector[Rational], val A: Matrix[Rational], val b: Vector[Rational]) {

  val nbConstraints = b.size
  val nbVariables = c.size

  require(A.nbRow == nbConstraints && A.nbCol == nbVariables)

  override def toString = {
    "min: " + c.toArray.zipWithIndex.map{ case (r, i) => r.toString + "*x_" + i }.mkString(" + ") + "\nsubject to:\n" +
    A.toRows.zipWithIndex.map{ case (row, index) => row.toArray.zipWithIndex.map{ case (r, i) => r.toString + "*x_" + i }.mkString(" + ") + " = " + b(index) }.mkString("\n")
  }

}

object StandardLinearProgram {


  private def coefVar(v: Variable, t: Term): Rational = if(!contains(t, v)) Rational.zero else polynomialForm(t, v) match {
    case Add(Mul(coeff :: Pow(v2, Num(r)) :: Nil) :: rest :: Nil) if v2==v && r.isOne => Eval(coeff, Map())
    case Add(Mul(coeff :: Pow(v2, Num(r)) :: Nil) :: Nil) if v2==v && r.isZero => Rational.zero
    case _ => throw new IllegalArgumentException("not a linear expression: " + t)
  }

  /*
   * this takes a relaxed format with an objective function writen as a Term with variables and some constraints written as:
   * ti <= bi,
   * ti >= bi or
   * ti = bi
   * and transform this linear program in standard form.
   *
   * The returned array indicates the corresponding vector of variables and the Map gives a mapping from some original variables
   * that have been transformed to an expression of two fresh variables. if we have (v -> (v1, v2)) in the mapping, this means that
   * v has been replaced by v1-v2 in the linear program
   *
   */
  def fromMin(objectiveFunction: Term, constraints: List[PredicateApplication]): (StandardLinearProgram, Array[Variable], Map[Variable, (Variable, Variable)]) = {
    val initialVars: Set[Variable] = (vars(objectiveFunction) ++ constraints.map(vars).flatten)
    val (boundedVarsEq, restConstraints) = constraints.partition{
      case GreaterEqual(Var(_), Zero()) => true
      case LessEqual(Zero(), Var(_)) => true
      case _ => false
    }
    val boundedVars = boundedVarsEq.map{
      case GreaterEqual(v@Var(_), _)=> v
      case LessEqual(_, v@Var(_)) => v
    }

    val allVars: ListBuffer[Variable] = new ListBuffer
    allVars ++= boundedVars
    val varMapping: HashMap[Variable, (Variable, Variable)] = new HashMap

    val unboundedVars = initialVars.filterNot(v => boundedVars.contains(v))
    unboundedVars.foreach(v => {
      val v1 = freshVariable(v)
      val v2 = freshVariable(v)
      varMapping.put(v, (v1, v2))
      allVars += v1
      allVars += v2
    })

    val var2Terms = varMapping.map{case (v, (v1, v2)) => (v, Sub(v1, v2))}.toMap
    val boundedConstraints = restConstraints.map(c => substitute(c, var2Terms))
    val boundedObjectiveFunction = substitute(objectiveFunction, var2Terms)

    val finalConstraints = boundedConstraints.map{
      case LessEqual(t, n@Num(_)) => {
        val slackVar = freshVar()
        allVars += slackVar
        Equals(Add(t, slackVar), n)
      }
      case GreaterEqual(t, Num(r)) => {
        val slackVar = freshVar()
        allVars += slackVar
        Equals(Add(Neg(t), slackVar), Num(-r))
      }
      case eq@Equals(_, Num(_)) => eq
      case _ => throw new IllegalArgumentException
    }

    val (coefTerms, constraintsTerms) = finalConstraints.map{ case Equals(t, Num(r)) => (t, r) }.unzip
    val allVarsArray = allVars.toArray

    val matrixCoef: Matrix[Rational] = Matrix(coefTerms.map(t => allVarsArray.map(v => coefVar(v, t))).toArray)
    val vectorConstraints: Vector[Rational] = Vector(constraintsTerms.toArray)
    val vectorObjective: Vector[Rational] = Vector(allVarsArray.map(v => coefVar(v, boundedObjectiveFunction)))
    (new StandardLinearProgram(vectorObjective, matrixCoef, vectorConstraints), allVarsArray, varMapping.toMap)
  }

  def fromMax(objectiveFunction: Term, constraints: List[PredicateApplication]): (StandardLinearProgram, Array[Variable], Map[Variable, (Variable, Variable)]) = {
    val minObjective = Neg(objectiveFunction)
    fromMin(minObjective, constraints)
  }

}
