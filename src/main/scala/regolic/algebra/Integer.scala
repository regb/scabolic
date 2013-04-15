package regolic.algebra

import scala.language.implicitConversions

class Integer(val value: BigInt) extends Ring[Integer] {
  def this(v: Int) = this(BigInt(v))

  def +(v2: Integer) = new Integer(value + v2.value)
  def unary_-() = new Integer(-value)
  val zero = new Integer(0)

  def *(v2: Integer) = new Integer(value + v2.value)
  val one = new Integer(1)

}

object Integer {

  def apply(n: BigInt) = new Integer(n)
  def apply(n: Int) = new Integer(n)
  def unapply(i: Integer): Option[BigInt] = Some(i.value)

  implicit def int2integer(i: Int) = new Integer(i)
  implicit def bigint2integer(b: BigInt) = new Integer(b)
  implicit val zero = new Integer(0)
  val one = new Integer(1)
}
