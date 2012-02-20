package regolic.lp

import regolic.algebra.{Rational, Matrix, Vector}

class Tableau(val basis: List[Int], val systemMatrix: Matrix[Rational], val reducedCost: Vector[Rational], val basisSolution: Vector[Rational], val value: Rational) {

  
  def isOptimal: Boolean = reducedCost.forall(el => el >= 0)

  def isUnbounded(pivot: Int): Boolean = systemMatrix.col(pivot).forall(_ <= 0)

  def nextTableau: Tableau = {
    val pivot = this.findPivot
    val leavingIndex = this.findLeavingIndex(pivot)
    val newTableau = this.changeBasis(pivot, leavingIndex)
    newTableau
  }

  //the pivot will be the left most negative value (according to Bland's rule)
  def findPivot: Int = {
    val minIndex = reducedCost.indexWhere(_ < 0)
    require(minIndex != -1)
    minIndex
  }

  //in case of tie, we will pick the toppest one (according to Bland's rule) 
  def findLeavingIndex(pivot: Int): Int = {
    val pivotCol = systemMatrix.col(pivot)
    var minIndex = -1
    var min: Rational = null
    val dim = basis.size
    for(i <- 0 until dim) {
      if(pivotCol(i) > Rational.zero) {
        val newMin = basisSolution(i) / pivotCol(i)
        //the tie rule simply means keeping the first one we encountered, because we examined from the toppest basis
        if(min == null || newMin < min) {
          min = newMin
          minIndex = i
        }
      }
    }
    require(minIndex != -1)
    basis(minIndex)
  }

  def changeBasis(pivot: Int, removed: Int): Tableau = {
    val indexOne = basis.indexOf(removed)
    val newBasis = basis.updated(indexOne, pivot)

    //first divide the row to make a one in the pivot position
    val newMatrix = systemMatrix.mapRow(indexOne, el => el / systemMatrix(indexOne, pivot))
    //then we should apply row operation to set everything else in the pivot column to 0
    val finalSystemMatrix = newMatrix.mapWithIndex((el, row, col) => if(row != indexOne) el - (newMatrix(row, pivot) * newMatrix(indexOne, col)) else el)

    val newBasisSolution = basisSolution.mapWithIndex((el, index) =>
      if(index == indexOne)
        el/systemMatrix(indexOne, pivot)
      else
        el - (systemMatrix(index, pivot)*(basisSolution(indexOne)/systemMatrix(indexOne, pivot)))
    )

    val newReducedCost = reducedCost - (finalSystemMatrix.row(indexOne)*reducedCost(pivot))
    val newValue = value - (newBasisSolution(indexOne) * reducedCost(pivot))

    new Tableau(newBasis, finalSystemMatrix, newReducedCost, newBasisSolution, newValue)
  }

  override def toString: String = {
    val firstRow = reducedCost.toArray.mkString(" ") + " | " + value + "\n"
    val horizontalSep = "_____________________________________\n"
    val rest = (0 until systemMatrix.nbRow).map( row => 
      systemMatrix.row(row).toArray.mkString(" ") + " | " + basisSolution(row)
    ).mkString("\n")
    firstRow + horizontalSep + rest
  }

  override def equals(that: Any): Boolean = that match {
    case (thatT: Tableau) => {
      basis == thatT.basis &&
      systemMatrix == thatT.systemMatrix &&
      reducedCost == thatT.reducedCost &&
      basisSolution == thatT.basisSolution &&
      value == thatT.value
    }
    case _ => false
  }

}
