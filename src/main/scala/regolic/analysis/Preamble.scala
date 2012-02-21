package regolic.analysis

import regolic.algebra.Rational
import regolic.asts.core.{Trees => CoreT, Manip => CoreM}
import regolic.asts.core.Trees.PredicateApplication
import regolic.asts.fol.{Trees => FolT, Manip => FolM}
import regolic.asts.theories.real
import real.{Trees => RealT, Manip => RealM}
import regolic.equation.LinearSystemSolver
import regolic.equation.PolynomialSolver
import regolic.simplifier.PolynomialFactorizer

object Preamble {

  type Term = CoreT.Term
  type Variable = CoreT.Variable
  type Formula = CoreT.Formula

  val True = FolT.True
  val False = FolT.False
  val Not = FolT.Not
  val Or = FolT.Or
  val And = FolT.And
  val Implies = FolT.Implies
  val Iff = FolT.Iff
  val IfThenElse = FolT.IfThenElse

  val Equals = FolT.Equals

  val LessThan = RealT.LessThan
  val LessEqual = RealT.LessEqual
  val GreaterThan = RealT.GreaterThan
  val GreaterEqual = RealT.GreaterEqual

  val Var = RealT.Var
  val Num = RealT.Num
  def freshVar(prefix: String): Variable = RealT.freshVar(prefix)

  val Add = RealT.Add
  val Sub = RealT.Sub
  val Mul = RealT.Mul
  val Div = RealT.Div
  val Pow = RealT.Pow
  val Neg = RealT.Neg
  val Abs = RealT.Abs
  val Floor = RealT.Floor
  val Max = RealT.Max
  val Min = RealT.Min

  class TermWrapper(val t: Term) {
    def +(t2: Term) = Add(List(t, t2))
    def -(t2: Term) = Sub(t, t2)
    def *(t2: Term) = Mul(List(t, t2))
    def /(t2: Term) = Div(t, t2)
    def ^(t2: Term) = Pow(t, t2)

    def unary_- = Neg(t)

    def <(t2: Term) = LessThan(t, t2)
    def <=(t2: Term) = LessEqual(t, t2)
    def >(t2: Term) = GreaterThan(t, t2)
    def >=(t2: Term) = GreaterEqual(t, t2)

    def ===(t2: Term) = Equals(t, t2)
  }
  class VariableWrapper(val v: Variable) extends TermWrapper(v)

  implicit def wrapTerm(t: Term): TermWrapper = new TermWrapper(t)
  implicit def unwrapTerm(t: TermWrapper): Term = t.t

  implicit def wrapVar(v: Variable): VariableWrapper = new VariableWrapper(v)
  implicit def unwrapVar(v: VariableWrapper): Variable = v.v

  implicit def str2wrap(id: String): VariableWrapper = new VariableWrapper(Var(id))
  implicit def str2var(id: String): Variable = Var(id)

  implicit def int2wrap(n: Int): TermWrapper = new TermWrapper(Num(Rational(n)))
  implicit def int2num(n: Int): Term = Num(Rational(n))

  implicit def rat2wrap(r: Rational): TermWrapper = new TermWrapper(Num(r))
  implicit def rat2num(r: Rational): Term = Num(r)

  implicit def int2rat(n: Int): Rational = Rational(n)

  def vars(t: Term): Set[Variable] = CoreM.vars(t)
  def simplify(t: Term): Term = RealM.simplify(t)
  def isPolynomial(t: Term): Boolean = RealM.isPolynomial(t)
  def polynomialForm(t: Term, v: Variable): Term = RealM.polynomialForm(t, v)
  def expandedForm(t: Term): Term = RealM.expandedForm(t)
  def isRational(t: Term): Boolean = RealM.isRational(t)
  def rationalForm(t: Term, v: Variable): Term = RealM.rationalForm(t, v)
  def polynomialDivision(t: Term): (Term, Term) = RealM.polynomialDivision(t)
  def expandedRationalForm(t: Term): Term = RealM.expandedRationalForm(t)
  def eval(t: Term, m: Map[Variable, Rational] = Map()): Rational = real.Eval(t, m)
  def eval(t: Term, v: Variable, r: Rational): Rational = real.Eval(t, v, r)
  def prettyPrinter(t: Term): String = real.PrettyPrinter(t)
  def prettyPrinter(f: Formula): String = real.PrettyPrinter(f)
  def substitute(t: Term, v: Variable, nt: Term): Term = CoreM.substitute(t, v, nt)
  def substitute(t: Term, mapping: Map[Variable, Term]): Term = CoreM.substitute(t, mapping)
  def contains(t: Term, el: Term): Boolean = CoreM.contains(t, el)
  def solveSum(v: Variable, lb: Term, ub: Term, body: Term): Option[Term] = new Summation(v, lb, ub, body).closedFormula
  def solveEquations(eqs: List[PredicateApplication]): Map[Variable, Term] = LinearSystemSolver(eqs)
  def derive(term: Term, variable: Variable): Term = Derivative(new RealFunction(variable, term))
  def polynomialRoots(term: Term): Set[(Term, Int)] = PolynomialSolver.polynomialRoots(term) 
  def factorizePolynomial(term: Term): Term = PolynomialFactorizer.factorizePolynomial(term) 
  val e = RealT.E()
  val pi = RealT.PI()
  def exp(t: Term): Term = RealT.Exp(t)
  def ln(t: Term): Term = RealT.Ln(t)
  def log(b: Term, t: Term): Term = RealT.Log(b, t)
  def sqrt(t: Term): Term = RealT.Sqrt(t)
  def nthRoot(i: Int, t: Term): Term = RealT.NthRoot(i, t)

  //some usefull variables
  val a = Var("a")
  val b = Var("b")
  val c = Var("c")
  val i = Var("i")
  val j = Var("j")
  val k = Var("k")
  val l = Var("l")
  val n = Var("n")
  val m = Var("m")
  val x = Var("x")
  val y = Var("y")
  val z = Var("z")

}
