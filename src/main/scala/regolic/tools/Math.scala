package regolic.tools

object Math {

  def fix[A](fun: (A => A), t: A): A = {
    val t2 = fun(t)
    if (t == t2) t2 else fix(fun, t2)
  }

//  def comp[A,B,C](f: (A => B), g: (C => A)): (C => B) = ((x: C) => f(g(x)))

  def lcm(a: BigInt, b: BigInt) : BigInt = (a * b) / a.gcd(b)
}
