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
  def apply(vec: Vector[T]): Vector[T] = Vector(this * Matrix(vec))

  def toArray = ArrayTools.matrixCopy(matrix)

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

  def row(r: Int): Matrix[T] = subMatrix(r, 1, 0, nbCol)
  def col(c: Int): Matrix[T] = subMatrix(0, nbRow, c, 1)

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

  def map[S <: Field[S]](f: ((T) => (S)))(implicit fi: Field[S], m: ClassManifest[S]): Matrix[S] = {
    val newArray = matrix.map(x => x.map(y => f(y)))
    new Matrix(newArray)
  }

  def foldLeft[S](z: S)(f: (S, T) => S): S = matrix.foldLeft(z)((acc, arr) => arr.foldLeft(acc)(f))

  def forall(p: T => Boolean): Boolean = foldLeft(true)((b, e) => b && p(e))

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
    str + "\n"
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

}

object Matrix {

  def apply[F <: Field[F]](vec: Vector[F])(implicit field: Field[F], man: ClassManifest[F]) = 
    new Matrix(vec.toArray.map(x => Array(x)))
  def apply[F <: Field[F]](mat: Array[Array[F]])(implicit field: Field[F],  man: ClassManifest[F]) =
    new Matrix(mat)

}
