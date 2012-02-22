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

  def toCols: Array[Vector[T]] = {
    val a = Array.ofDim[Vector[T]](nbCol)
    for(j <- 0 until nbCol)
      a(j) = this.col(j)
    a
  }
  def toRows: Array[Vector[T]] = {
    val a = Array.ofDim[Vector[T]](nbRow)
    for(i <- 0 until nbRow)
      a(i) = this.row(i)
    a
  }

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
  def mapWithIndex[S <: Field[S]](f: ((T, Int, Int) => (S)))(implicit fi: Field[S], m: ClassManifest[S]): Matrix[S] = {
    val newArray = Array.ofDim[S](nbRow, nbCol)
    for(row <- 0 until nbRow)
      for(col <- 0 until nbCol)
        newArray(row)(col) = f(matrix(row)(col), row, col)
    new Matrix(newArray)
  }

  def mapRow(row: Int, f: (T) => T) = {
    val newArray = ArrayTools.matrixCopy(matrix)
    newArray(row) = newArray(row).map(f)
    new Matrix(newArray)
  }

  def mapCol(col: Int, f: (T) => T) = {
    val newArray = ArrayTools.matrixCopy(matrix)
    for(row <- 0 until nbRow)
      newArray(row)(col) = f(matrix(row)(col))
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
  //augment with a vertical vector (interpret the vector as a one column matrix)
  def augment(vec: Vector[T]): Matrix[T] = {
    require(nbRow == vec.size)
    val newMatrix = Array.ofDim(nbRow, nbCol + 1)
    for(i <- 0 until nbRow) {
      for(j <- 0 until nbCol)
        newMatrix(i)(j) = matrix(i)(j)
      newMatrix(i)(nbCol) = vec(i)
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
    val reducedMatrix = augmentedMatrix.gaussJordanElimination
    require(reducedMatrix.subMatrix(0, nbRow, 0, nbCol) == idMatrix)
    reducedMatrix.subMatrix(0, nbRow, nbCol, nbCol)
  }


  //warning, this is kind of a low level code (for the Scala standard that is), that is probably going to be more efficient and it
  //is hidden behind a function code abstraction anyway.
  def gaussianElimination: Matrix[T] = {
    import ArrayTools.swapRows

    val matArray = matrix.toArray
    var nr = nbRow
    var nc = nbCol

    for(r <- 0 until nr) {
      var allZeros = true
      for(c <- 0 until nc if allZeros)
        if(matArray(r)(c) != field.zero) allZeros = false
      if(allZeros) {
        swapRows(matArray, r, nr - 1)
        nr = nr - 1
      }
    }

    var r = 0
    var c = 0
    while (r < nr && c < nc) {

      var pivot = -1 
      var allZeros = true
      for(i <- r until nr if allZeros) {
        if(matArray(i)(c) != field.zero) {
          allZeros = false
          pivot = i
        }
      }

      if(pivot == -1)
        c += 1
      else {

        if(pivot != r)
          swapRows(matArray, r, pivot)

        val divisor = matArray(r)(c)
        ArrayTools.mapElements(matArray(r), ((x: T) => x/divisor), c, nc)

        for(i <- (r+1) until nr) {
          val mul = matArray(i)(c)
          for(j <- c until nc)
            matArray(i)(j) = matArray(i)(j) - mul * matArray(r)(j)
        }

        r += 1
        c += 1
      }
    }
    new Matrix(matArray)
  }

  def gaussJordanElimination: Matrix[T] = {
    val echelonMat = this.gaussianElimination
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
    new Matrix(matArray)
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
  def zero[T <: Field[T]](n: Int, m: Int)(implicit field: Field[T], man: ClassManifest[T]): Matrix[T] =
    new Matrix(Array.fill[T](n, m)(field.zero))

}
