package regolic.lp

import regolic.algebra.{Matrix, Rational, Vector}

object Simplex {

  trait Result
  case object Unbounded extends Result
  case object Infeasible extends Result
  case class Optimal(assignment: Vector[Rational]) extends Result

  def apply(lp: StandardLinearProgram): Result = phaseOne(lp) match {
    case None => Infeasible
    case Some(tableau) => phaseTwo(tableau) match {
      case None => Unbounded
      case Some(tableau) => {
        //this is an optimal tableau
        Optimal(Vector((0 until tableau.systemMatrix.nbCol).map(i => 
            if(tableau.basis.contains(i)) tableau.basisSolution(tableau.basis.indexOf(i)) else Rational(0)
        ).toArray))
      }
    }
  }

  def phaseOne(lp: StandardLinearProgram): Option[Tableau] = {
    val nbRow = lp.A.nbRow
    val basis = (lp.A.nbCol until (lp.A.nbCol + nbRow)).toList
    val extendedId = Matrix.identity[Rational](nbRow)
    val extendedSystemMatrix = lp.A.augment(extendedId)
    val reducedCost = Vector(lp.A.toCols.map(vector => -(vector.sum))).augment(Vector.zero[Rational](nbRow))
    val value = -(lp.b.sum)
    var tableau = new Tableau(basis, extendedSystemMatrix, reducedCost, lp.b, value)

    while(!tableau.isOptimal) {
      tableau = tableau.nextTableau
    }

    if(!tableau.value.isZero) 
      None
    else {
      var newSystemMatrix = tableau.systemMatrix.subMatrix(0, nbRow, 0, lp.A.nbCol)
      var newBasisSolution = tableau.basisSolution
      var newBasis = tableau.basis
      while(newBasis.exists(basis.contains(_))) {
        val row = newBasis.indexWhere(basis.contains(_))
        require(newSystemMatrix.row(row).forall(_ == Rational.zero) && newBasisSolution(row).isZero)
        newBasis = newBasis.filterNot(_ == newBasis(row))
        val rowsToKeep = (0 until newSystemMatrix.nbRow).filterNot(_ == row).toList
        newSystemMatrix = newSystemMatrix.subMatrix(rowsToKeep, (0 until newSystemMatrix.nbCol).toList)
        newBasisSolution = newBasisSolution.subVector(rowsToKeep)
      }

      val newReducedCost = newBasis.zipWithIndex.foldLeft(lp.c){
        case (rc, (b, i)) => rc - newSystemMatrix.row(i)*lp.c(b)
      }
      val newValue = newBasis.zipWithIndex.foldLeft(Rational.zero){
        case (rat, (b, i)) => rat - newBasisSolution(i)*lp.c(b)
      }

      val newTableau = new Tableau(newBasis, newSystemMatrix, newReducedCost, newBasisSolution, newValue)

      Some(newTableau)
    }
  }

  def phaseTwo(initialTableau: Tableau): Option[Tableau] = {
    var tableau = initialTableau

    while(!tableau.isOptimal && !tableau.isUnbounded(tableau.findPivot)) {
      tableau = tableau.nextTableau
    }
    if(tableau.isOptimal) Some(tableau) else None
  }

}
