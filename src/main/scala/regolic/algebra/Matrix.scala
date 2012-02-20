package regolic.algebra

import regolic.tools.ArrayTools

class Matrix[T <: Field[T]](m: Array[Array[T]])(implicit field: Field[T], man: ClassManifest[T]) extends LinearMap[Matrix[T], T, Vector[T], Vector[T]] {

  val nbRow = m.length
  require(nbRow > 0)
  val nbCol = m(0).length
  require(nbCol > 0)

  require(ArrayTools.isSquare(m, nbRow, nbCol))

  private val matrix = ArrayTools.matrixCopy(m)

  def apply(row: Int, col: Int): T = matrix(row)(col)
  def apply(row: Int): Vector[T] = this.row(row)
  def apply(vector: Vector[T]): Vector[T] = this * vector

  def toArray = ArrayTools.matrixCopy(matrix)

  def subMatrix(rows: List[Int], cols: List[Int]): Matrix[T] = {
    val subMat = Array.ofDim[T](rows.size, cols.size)
    rows.zipWithIndex.foreach{ case (row, i) =>
      cols.zipWithIndex.foreach{ case (col, j) =>
        subMat(i)(j) = matrix(row)(col)
      }
    }
    new Matrix(subMat)
  }
  def subMatrix(fromRow: Int, nbRow: Int, fromCol: Int, nbCol: Int): Matrix[T] = {
    val subMat = Array.ofDim[T](nbRow, nbCol)
    var row = fromRow
    var col = fromCol
    val toRow = fromRow + nbRow
    val toCol = fromCol + nbCol
    var i,j = 0
    while(row < toRow) {
      col = fromCol
      j = 0
      while(col < toCol) {
        subMat(i)(j) = matrix(row)(col)
        j += 1
        col += 1
      }
      i += 1
      row += 1
    }
    new Matrix(subMat)
  }

  def row(r: Int): Vector[T] = Vector(subMatrix(r, 1, 0, nbCol))
  def col(c: Int): Vector[T] = Vector(subMatrix(0, nbRow, c, 1))

  lazy val zero = this.map(el => field.zero)
  def +(mat: Matrix[T]): Matrix[T] = {
    require(ArrayTools.isSquare(mat.toArray, nbRow, nbCol))
    var row = 0
    var col = 0
    val newMat = Array.ofDim[T](nbRow, nbCol)
      while(row < nbRow) {
      col = 0
      while(col < nbCol) {
        newMat(row)(col) = matrix(row)(col) + mat(row,col)
        col += 1
      }
      row += 1
    }
    new Matrix(newMat)
  }
  def unary_-(): Matrix[T] = this.map(el => -el)

  def *(mat: Matrix[T]): Matrix[T] = {
    require(nbCol == mat.nbRow)
    val newRow = nbRow
    val newCol = mat.nbCol
    var row = 0
    var col = 0
    var k = 0
    var sum = field.zero
    val newMat = Array.ofDim[T](newRow, newCol)
      while(row < newRow) {
      col = 0
      while(col < newCol) {
        k = 0
        sum = field.zero
        while(k < nbCol) {
          sum = sum + (matrix(row)(k) * mat(k,col)) 
          k += 1
        }
        newMat(row)(col) = sum 
        col += 1
      }
      row += 1
    }
    new Matrix(newMat)
  }
  def *(vec: Vector[T]): Vector[T] = Vector(this * Matrix(vec))
  def *(scalar: T): Matrix[T] = {
    var i,j = 0
    val res = Array.ofDim[T](nbRow, nbCol)
      while(i < nbRow) {
      j = 0
      while(j < nbCol) {
        res(i)(j) = matrix(i)(j) * scalar
        j += 1
      }
      i += 1
    }
    new Matrix(res)
  }

  def transpose: Matrix[T] = new Matrix(matrix.transpose)

  def map[S <: Field[S]](f: ((T) => (S)))(implicit fi: Field[S], m: ClassManifest[S]): Matrix[S] = {
    val newArray = matrix.map(x => x.map(y => f(y)))
    new Matrix(newArray)
  }

  //foldLeft on the matrix, the order is: row by row starting at the first one then going from
  //the first column to the last, then the second row ...
  def foldLeft[S](z: S)(f: (S, T) => S): S = matrix.foldLeft(z)((acc, arr) => arr.foldLeft(acc)(f))

  def forall(p: (T) => Boolean): Boolean = foldLeft(true)((b, e) => b && p(e))
  def exists(p: (T) => Boolean): Boolean = foldLeft(false)((b, e) => b || p(e))

  def augment(mat: Matrix[T]): Matrix[T] = {
    require(nbRow == mat.nbRow)
    val newMatrix = Array.ofDim(nbRow, nbCol + mat.nbCol)
    for(i <- 0 until nbRow) {
      for(j <- 0 until nbCol)
        newMatrix(i)(j) = matrix(i)(j)
      for(j <- 0 until mat.nbCol)
        newMatrix(i)(j+nbCol) = mat(i, j)
    }
    new Matrix(newMatrix)
  }

  //not a very efficient algorithm on big matrices, but I heard determinant are not of much use anyway
  def determinant: T = {
    require(nbRow == nbCol)
    val allIndices = (0 until nbRow)
    val row = 0
    val indicesWithoutRow = allIndices.filterNot(_ == row).toList
    var determinant: T = field.zero
    for(j <- 0 until nbCol) {
      if(j % 2 == 0)
        determinant += matrix(row)(j) * subMatrix(indicesWithoutRow, allIndices.filterNot(_ == j).toList).determinant
      else
        determinant += (-field.one) * matrix(row)(j) * subMatrix(indicesWithoutRow, allIndices.filterNot(_ == j).toList).determinant
    }
    determinant
  }

  def isNonSingular: Boolean = {
    try { 
      this.inverse
      true
    } catch {
      case _ => false
    }
  }

  def inverse: Matrix[T] = {
    require(nbRow == nbCol)
    val idMatrix = Matrix.identity[T](nbRow)
    val augmentedMatrix = this.augment(idMatrix)
    val reducedMatrix = augmentedMatrix.gaussJordanElimination match {
      case None => {require(false); idMatrix}
      case Some(m) => m
    }
    require(reducedMatrix.subMatrix(0, nbRow, 0, nbCol) == idMatrix)
    reducedMatrix.subMatrix(0, nbRow, nbCol, nbCol)
  }

  def gaussianElimination: Option[Matrix[T]] = {
    val matArray = matrix.toArray
    var r = 0
    var c = 0

    while (r < nbRow && c < nbCol) {
      val pivot = findPivot(r, c)
      if (pivot == -2)
        return None
      else if(pivot == -1)
        c += 1
      else {
        ArrayTools.swapRows(matArray, r, pivot)
        val divisor = matArray(r)(c)
        ArrayTools.mapElements(matArray(r), ((x: T) => x/divisor), c, nbCol)
        var i = r + 1
        while (i < nbRow) {
          var j = 0
          val mul = matArray(i)(c)
          while (j < nbCol) {
            matArray(i)(j) = matArray(i)(j) - mul * matArray(r)(j)
            j += 1
          }
          i += 1
        }
      }
      r += 1
      c += 1
    }
    Some(new Matrix(matArray))
  }

  def gaussJordanElimination: Option[Matrix[T]] = this.gaussianElimination match {
    case None => None
    case Some(echelonMat) => {
      val matArray = echelonMat.toArray
      val row = echelonMat.nbRow
      val col = echelonMat.nbCol
      var r = row - 1
      while(r > 0) {

        var c = 0
        var found = false
        //find the pivot
        while(c < col && !found) {
          (matArray(r)(c) == field.zero) match {
            case true => c += 1
            case false => found = true
          }
        }

        if(c != col) {
          var i = r - 1
          while(i >= 0) {
            val mul = matArray(i)(c)
            var j = 0
            while(j < col) {
              matArray(i)(j) = matArray(i)(j) - mul * matArray(r)(j)
              j += 1
            }
            i -= 1
          }	
        }
        r -= 1
      }
      Some(new Matrix(matArray))
    }
  }

  override def equals(that: Any): Boolean = that match {
    case (thatM: Matrix[_]) => 
      ArrayTools.matrixForAll[Any](matrix.asInstanceOf[Array[Array[Any]]], thatM.toArray.asInstanceOf[Array[Array[Any]]], (x: Any, y: Any) => x == y)
    case _ => false
  }

  //TODO
  override def hashCode: Int = {
    0
  }

  override def toString: String = {
    var str = "\n"
    var i,j = 0
    while(i < nbRow) {
      j = 0
      while(j < nbCol) {
        str += matrix(i)(j).toString + " "
        j += 1
      }
      str += "\n"
      i += 1
    }
    str
  }

  private def findPivot(fromRow: Int, col: Int): Int = {
    var pivot = -1	
    var row = fromRow
    while(row < matrix.length) {
      if(matrix(row)(col) != field.zero) 
        return row
      row += 1
    }
    pivot
  }

}

object Matrix {

  //convert the vector to a one column matrix
  def apply[F <: Field[F]](vec: Vector[F])(implicit field: Field[F], man: ClassManifest[F]): Matrix[F] = try {
    val vecArray: Array[F] = vec.toArray
    val nbElements = vecArray.size
    val matArray: Array[Array[F]] = Array.ofDim(nbElements, 1)
    for(i <- 0 until nbElements)
      matArray(i)(0) = vecArray(i)
    new Matrix(matArray)
  }
  def apply[F <: Field[F]](mat: Array[Array[F]])(implicit field: Field[F],  man: ClassManifest[F]): Matrix[F] =
    new Matrix(mat)

  def identity[T <: Field[T]](n: Int)(implicit field: Field[T], man: ClassManifest[T]): Matrix[T] = {
    val matrix = Array.ofDim[T](n, n)
    for(i <- 0 until n)
      for(j <- 0 until n)
        if(i == j) matrix(i)(j) = field.one else matrix(i)(j) = field.zero
    new Matrix(matrix)
  }

  def zero[T <: Field[T]](n: Int)(implicit field: Field[T], man: ClassManifest[T]): Matrix[T] = Matrix.zero(n, n)
  def zero[T <: Field[T]](n: Int, m: Int)(implicit field: Field[T], man: ClassManifest[T]): Matrix[T] = {
    val matrix = Array.ofDim[T](n, m)
    for(i <- 0 until n)
      for(j <- 0 until m)
        matrix(i)(j) = field.zero
    new Matrix(matrix)
  }

}
