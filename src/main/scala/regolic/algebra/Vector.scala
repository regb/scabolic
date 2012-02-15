package regolic.algebra

import regolic.tools.ArrayTools

class Vector[T <: Field[T]](v: Array[T])(implicit field: Field[T], man: ClassManifest[T]) extends VectorSpace[Vector[T], T] {

  private val nbElement = vector.length
  require(nbElement > 0)

  private val vector = ArrayTools.arrayCopy(v)

  def toArray = ArrayTools.arrayCopy(vector)

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
  def unary_-() = this.map(el => -el)
  lazy val zero = this.map(el => field.zero)

  def *(scalar: T): Vector[T] = {
    var i = 0
    val res = new Array[T](nbElement)
      while(i < nbElement) {
      res(i) = vector(i) * scalar
      i += 1
    }
    new Vector(res)
  }

  def map[S <: Field[S]](f: (T) => S)(implicit fi: Field[S], m: ClassManifest[S]): Vector[S] = new Vector(vector.map(f))

  override def equals(that: Any): Boolean = that match {
    case (thatV: Vector[_]) => vector == thatV.vector
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

  def apply[T <: Field[T]](m: Matrix[T])(implicit field: Field[T], man: ClassManifest[T]): Vector[T] = {
    require(m.nbCol == 1)
    new Vector(m.toArray.map{case Array(el) => el})
  }

}
