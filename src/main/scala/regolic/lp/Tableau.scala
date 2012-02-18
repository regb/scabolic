package regolic.lp

import regolic.algebra.{Rational, Matrix, Vector}

class Tableau(val basis: List[Int], val systemMatrix: Matrix[Rational], reducedCost: Vector[Rational], value: Rational) {

  
  def isOptimal: Boolean = reducedCost.forall(el => el >= 0)

  def nextTableau: Tableau = {
    null
  }

  private def findNewBasis: Int = {
    val localIndex = reducedCost.indexWhere(el => el < 0) //index local to the reducedCost vector without zeros elements of the basis
    //building global index
    var globalIndex = basis.foldLeft(localIndex)((currentIndex, basisIndex) =>
      if(basisIndex <= currentIndex) currentIndex + 1 else currentIndex
    )
    globalIndex
  }

}
