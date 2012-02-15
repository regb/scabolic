package regolic.algebra

trait VectorSpace[T, F <: Field[F]] {

  /*
   * A vector space provides an associative and commutative 
   * addition on vectors, a multiplication by a scalar,
   * an inverse (additive) operation and a zero element for the addition.
   */

  def +(v: T): T
  def unary_-(): T
  val zero: T

  def *(scalar: F): T

}
