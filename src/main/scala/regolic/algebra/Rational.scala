package regolic.algebra

import regolic.tools.Math

import scala.language.implicitConversions

class Rational private (num: BigInt, denom: BigInt) extends Field[Rational] with Ordered[Rational] {

  require(denom != 0)

  private val theGcd: BigInt = num.gcd(denom)
  private val (newNum, newDenom) = (num, denom) match {
    case (n, d) if n < 0 && d < 0 => (num.abs/theGcd, denom.abs/theGcd)
    case (n, d) if n > 0 && d < 0 => (-num/theGcd, denom.abs/theGcd)
    case (n, _) if n == 0 => (BigInt(0), BigInt(1))
    case (n, d) => (num/theGcd, denom/theGcd)
  }

  def numerator: BigInt = newNum
  def denominator: BigInt = newDenom

  lazy val zero = new Rational(0,1)
  override def isZero = numerator == 0
  def +(rat: Rational) = new Rational(numerator*rat.denominator + rat.numerator*denominator, denominator*rat.denominator)
  def unary_-(): Rational = new Rational(-numerator, denominator)
  override def -(rat: Rational) = new Rational(numerator*rat.denominator - rat.numerator*denominator, denominator*rat.denominator)

  lazy val one = new Rational(1,1)
  override def isOne = numerator == 1 && denominator == 1
  def *(rat: Rational) = new Rational(numerator*rat.numerator, denominator*rat.denominator)
  def inverse = new Rational(denominator, numerator)
  override def /(rat: Rational) = new Rational(numerator*rat.denominator, denominator*rat.numerator)

  def toPower(num: BigInt): Rational = new Rational(numerator.pow(num.intValue), denominator.pow(num.intValue))
  lazy val abs: Rational = new Rational(numerator.abs, denominator.abs)
  lazy val floor: Rational = new Rational(this.toBigInt, 1)

  def sqrt: Option[Rational] = nthRoot(2)

  //a bit of theory here: 
  //  first you can distribute the root to the numerator and denominator
  //  if a nth root of an integer is not an integer, then it is not a rational number
  //So either we find integers root of num and denom, or we return None
  def nthRoot(n: Int): Option[Rational] = {

    def binarySearch(lb: BigInt, ub: BigInt, expected: BigInt): Option[BigInt] = {
      def verifyGuess(guess: BigInt): BigInt = guess.pow(n) - expected

      if(lb >= ub && verifyGuess(ub) != 0) None else {
        val guess: BigInt = (lb + ub)/2
        val cmp = verifyGuess(guess)
        if(cmp == 0) Some(guess)
        else if(cmp > 0) binarySearch(lb, guess - 1, expected)
        else binarySearch(guess+1, ub, expected)
      }
    }

    if(numerator < 0 || denominator < 0) None
    else (binarySearch(0, numerator, numerator), binarySearch(0, denominator, denominator)) match {
      case (Some(n1), Some(n2)) => Some(new Rational(n1, n2))
      case _ => None
    }

  }

  def compare(that: Rational) = ((this.numerator * that.denominator) - (that.numerator * this.denominator)).intValue

  def toInt = numerator.intValue / denominator.intValue
  def toBigInt = numerator / denominator
  def toFloat = (numerator.toFloat)/(denominator.toFloat)
  def toDouble = (numerator.toDouble)/(denominator.toDouble)

  def isInteger = denominator == 1

  override def equals(o: Any) : Boolean = o match {
    case (rat: Rational) => numerator*rat.denominator == denominator * rat.numerator
    case _ => false
  }
  override def toString: String = if(denominator == 1) numerator.toString else numerator + "/" + denominator
}

object Rational {

  def apply(n: BigInt) = new Rational(n, 1)
  def apply(n: BigInt, d: BigInt) = new Rational(n, d)
  def apply(n: String) = n.split('/') match {
    case Array(num) => new Rational(BigInt(num), BigInt(1))
    case Array(num, denom) => new Rational(BigInt(num), BigInt(denom))
    case _ => throw new java.lang.NumberFormatException
  }
  def apply(n: Double) = if(n == 0d) new Rational(0, 1) else {
    val bits: Long = java.lang.Double.doubleToLongBits(n)

    val sign = bits >>> 63
    val exponent = ((bits >>> 52) ^ (sign << 11)) - 1023
    val fraction = bits << 12

    var a = BigInt(1)
    var b = BigInt(1)

    for(i <- 63 to 12 by -1) {
      a = a * 2 + ((fraction >>> i) & 1)
      b *= 2
    }

    if(exponent > 0)
      a *= 1 << exponent;
    else
      b *= 1 << -exponent;

    if (sign == 1)
      a *= -1;

    new Rational(a, b)
  }
  def unapply(r: Rational): Option[(BigInt, BigInt)] = Some(r.numerator, r.denominator)

  implicit def int2rat(i: Int) = new Rational(BigInt(i), BigInt(1))
  implicit def bigint2rat(b: BigInt) = new Rational(b, BigInt(1))
  implicit def double2rat(d: Double) = Rational(d)
  implicit val zero = new Rational(0,1)
  val one = new Rational(1,1)
}
