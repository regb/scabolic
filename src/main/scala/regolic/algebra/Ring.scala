package regolic.algebra

trait Ring[T <: Ring[T]] {
  
  /*
   * addition: 
   * associativity, commutativity, identity element existence and inverse element for all t
   * 
   * multiplication:
   * associativity and identity element existence 
   *
   * forall t,t'. t.zero = t'.zero
   * forall t. exists t'. t + t' = t.zero
   * forall t,t',t''. (t + t') + t'' = t + (t' + t'')
   * forall t,t'. t + t' = t' + t
   * forall t. t + t.zero = t
   *
   * forall t,t'. t.one = t'.one
   * forall t. t * t.one = t
   * forall t,t',t''. (t * t') * t'' = t * (t' * t'')
   *
   */
  def +(t: T): T
  def unary_-(): T
  val zero: T

  def *(t: T): T
  val one: T

  def -(t: T): T = this + (-t)
  def isZero: Boolean = this.zero == this
  def isOne: Boolean = this.one == this
}
