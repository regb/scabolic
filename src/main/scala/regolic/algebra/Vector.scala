package regolic.algebra

import regolic.tools.ArrayTools

class Vector[T <: Field[T]](v: Array[T])(implicit field: Field[T], man: ClassManifest[T]) extends VectorSpace[Vector[T], T] {

  private val nbElement = v.length
  require(nbElement > 0)

  private val vector: Array[T] = ArrayTools.arrayCopy(v)

  def toArray: Array[T] = ArrayTools.arrayCopy(vector)

  def element(index: Int): T = vector(index)
  def apply(index: Int): T = vector(index)

  def size: Int = nbElement

  def +(vec: Vector[T]): Vector[T] = {
    require(nbElement == vec.size)
    val res = new Array[T](nbElement)
      var i = 0
    while(i < nbElement) {
      res(i) = vector(i) + vec.element(i)
      i += 1
    }
    new Vector(res)
  }


  def unary_-() = this.map(el => -el)

  //TODO add this to the vector space trait
  def -(vec: Vector[T]): Vector[T] = this + (-vec)

  lazy val zero = this.map(el => field.zero)

  def *(vec: Vector[T]): T = {
    require(nbElement == vec.size)
    var res = field.zero
    var i = 0
    while(i < nbElement) {
      res = res + (vector(i) * vec.element(i))
      i += 1
    }
    res
  }
  def *(scalar: T): Vector[T] = {
    var i = 0
    val res = new Array[T](nbElement)
      while(i < nbElement) {
      res(i) = vector(i) * scalar
      i += 1
    }
    new Vector(res)
  }
  def *(mat: Matrix[T]): Vector[T] = Vector(Matrix(this).transpose * mat)

  def map[S <: Field[S]](f: (T) => S)(implicit fi: Field[S], m: ClassManifest[S]): Vector[S] = new Vector(vector.map(f))
  def mapWithIndex[S <: Field[S]](f: ((T, Int) => (S)))(implicit fi: Field[S], m: ClassManifest[S]): Vector[S] = {
    val newArray = Array.ofDim[S](size)
    for(i <- 0 until size)
      newArray(i) = f(vector(i), i)
    new Vector(newArray)
  }

  def foldLeft[S](z: S)(f: (S, T) => S): S = vector.foldLeft(z)(f)
  def forall(f: (T) => Boolean): Boolean = vector.forall(f)
  def exists(f: (T) => Boolean): Boolean = vector.exists(f)

  //return first index that verify the predicate, or -1 if none does
  def indexWhere(f: (T) => Boolean): Int = vector.indexWhere(f)

  def augment(vec: Vector[T]): Vector[T] = {
    val newVector = Array.ofDim(size + vec.size)
    for(i <- 0 until size)
      newVector(i) = vector(i)
    for(i <- 0 until vec.size)
      newVector(i + size) = vec(i)
    new Vector(newVector)
  }

  def subVector(elements: List[Int]): Vector[T] = {
    val newVector = Array.ofDim[T](elements.size)
    elements.zipWithIndex.map {
      case (el, i) => newVector(i) = vector(el)
    }
    new Vector(newVector)
  }

  def subVector(from: Int, nbElement: Int): Vector[T] = {
    val newVector = Array.ofDim[T](nbElement)
    for(i <- 0 until nbElement)
      newVector(i) = vector(from + i)
    new Vector(newVector)
  }

  def min: T = vector.min
  def minIndex: Int = {
    val minValue = this.min
    this.indexWhere(_ == minValue) 
  }
  def max: T = vector.max
  def maxIndex: Int = {
    val maxValue = this.max
    this.indexWhere(_ == maxValue) 
  }

  def sum: T = vector.foldLeft(field.zero)((acc, el) => acc + el)
  def prod: T = vector.foldLeft(field.one)((acc, el) => acc * el)

  override def equals(that: Any): Boolean = that match {
    case (thatV: Vector[_]) => vector.size == thatV.vector.size && vector.zip(thatV.vector).forall{ case (e1, e2) => e1 == e2 }
    case _ => false
  }


  //TODO
  override def hashCode: Int = {
    0
  }

  override def toString: String = {
    var str = "(" + vector(0).toString
    var i = 1
    while(i < nbElement) {
      str += ", " + vector(i).toString
      i += 1
    }
    str += ")"
    str
  }
}

object Vector {

  def apply[F <: Field[F]](mat: Array[F])(implicit field: Field[F],  man: ClassManifest[F]): Vector[F] = new Vector(mat)
  //try to use the matrix as a vector, if it has one column or one row
  def apply[T <: Field[T]](m: Matrix[T])(implicit field: Field[T], man: ClassManifest[T]): Vector[T] = {
    require(m.nbCol == 1 || m.nbRow == 1)
    if(m.nbCol == 1)
      new Vector(m.toArray.map{case Array(el) => el})
    else
      new Vector(m.toArray(0))
  }

  def zero[T <: Field[T]](n: Int)(implicit field: Field[T], man: ClassManifest[T]): Vector[T] = 
        new Vector(Array.fill[T](n)(field.zero))

}
