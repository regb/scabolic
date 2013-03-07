package regolic.asts.theories.number

import regolic.asts.theories.number.Trees._
import regolic.asts.theories.int.{Trees => IntT}
import regolic.asts.theories.real.{Trees => RealT}
import regolic.asts.core.Trees.{Formula, Term, Variable}
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees.{Equals => FOLEquals, _}
import regolic.asts.fol.Manip._
import regolic.algebra.Rational
import regolic.tools.Math.fix
import regolic.tools.SeqTools.mapUnique

/*
 * One of the design principle of the Manip object is to contain only basic "syntactic"
 * operation on the associated tree. Any "advanced" algorithm should be provide as a separate code
 * in a separate package. This Manip object tries to provide the most comonly used features.
 *
 * Note also that most of these methods do not do anything too smart, in particular a method like
 * isPolynomial will not give a "correct" answer (depending how you defined correct), in particular 
 * it will not attemp to simplify the formula to see whether some terms cancels out
 *
 * This object supports operation that can be applied to both formula over integer and real.
 *
 */

//maybe only do the safe modification (for example, not 0 * 1/a, because a 
//could be 0) here, and having a more aggressive system in calculus that could 
//return a list of assumption or take a list of assumption in addition

object Manip {

  def isSingleVarPolynomial(term: Term) = isPolynomial(term) && (vars(term).size == 1)

  //Is polynomial (accepting multiple variables)
  //do not require the polynomial to be in a standard form
  def isPolynomial(term: Term): Boolean = term match {
    case Var(_) | Num(_) => true
    case Add(ts) => ts.forall(isPolynomial(_))
    case Sub(t1, t2) => isPolynomial(t1) && isPolynomial(t2)
    case Mul(ts) => ts.forall(isPolynomial(_))
    case Neg(t) => isPolynomial(t)
    case Div(t1, Num(_)) => isPolynomial(t1)
    case Pow(t1, Num(r)) => isPolynomial(t1) && r.isInteger
   
    case _ => false
  }

  def polynomialDegree(polynomial: Term, variable: Variable): BigInt = {
    require(isPolynomialForm(polynomial, variable))
    val Add(ts) = polynomial
    val Mul(_ :: Pow(v, Num(degree)) :: ms) = ts.head
    require(v == variable)
    assert(degree.isInteger)
    degree.toBigInt
  }


  //checking that the term in in polynomial standard form
  //an*x^n + ... + a0*x^0, with an != 0
  def isPolynomialForm(term: Term, variable: Variable): Boolean = {
    def isCorrectPower(n: Rational, ts: List[Term]): Boolean = ts match {
      case Mul(List(coef, Pow(v, Num(r)))) :: Nil => variable == v && !contains(coef, variable) && r == n && n.isZero
      case Mul(List(coef, Pow(v, Num(r)))) :: ts => variable == v && !contains(coef, variable) && r == n && isCorrectPower(n-1, ts)
      case _ => false
    }
    term match {
      case Add(ts@(Mul(List(coef, Pow(v, Num(r))))::_ )) => isCorrectPower(r, ts)
      case _ => false
    }
  }

  /*
   * return an*x^n + ... + a0*x^0, with an != 0 and x being the head variable
   * note that all these terms appears explicitly in the returned tree, they are not simplified
   * note also that a_i could be a complex polynomial consisting of other variables, in that case, it will be
   * recursively put in polynomialForm according to the rest of the list of variables. If the list is empty no change
   * is done to the term.
   *
   * Note that there will be one level of nested Add and Mul for each variable in the list, even if the coefficient
   * do not contains any of the variables. This will be applied to each coefficient.
   */
  def polynomialForm(term: Term, variable: Variable): Term = polynomialForm(term, List(variable))
  def polynomialForm(term: Term, variables: List[Variable]): Term = {
    require(isPolynomial(term)) //this requires make sure that there won't be any n^x in the expanded form

    if(variables.isEmpty)
      term
    else {

      val variable = variables.head
  
      def containsNTimesVar(t: Term, degree: Int): Boolean = count(t, (_: Formula) => false, (t: Term) => t == variable) == degree
  
      def unify(ts: List[Term], degree: Int): List[Term] = if(ts.isEmpty) Nil else {
        val (thisDegree, otherDegree) = ts.partition(x => containsNTimesVar(x, degree))
        val coeff = 
          (thisDegree.map {
            case Mul(ts) => ts.filterNot(_ == variable) match {
              case Nil => One()
              case t :: Nil => t
              case ts@_ => Mul(ts)
            }
          }) match {
              case Nil => Zero()
              case t :: Nil => t
              case ts@_ => Add(ts)
          }
        val sCoeff = simplify(coeff)
        assert(!contains(sCoeff, variable))
        val mul = Mul(List(polynomialForm(sCoeff, variables.tail), Pow(variable, Num(Rational(degree)))))
        if(otherDegree.isEmpty) {
          if(sCoeff == Zero()) 
            Nil 
          else 
            List(mul)
        } else mul :: unify(otherDegree, degree+1)
      }
  
      val Add(ts) = expandedForm(term)
      val fTerm = Add(unify(ts, 0).reverse)
      fTerm
    }
  }

  def expandPower(term: Term): Term = {
    require(isRational(term))
    def inductionStep(t: Term): Term = t match {
      case Pow(t1, Num(r)) if r.isInteger => {
        if(r.isZero) One()
        else Mul((1 to r.toInt).map(_ => t1).toList)
      }
      case _ => t
    }
    mapPostorder(term, f => f, inductionStep)
  }

  /*
   * an atom is: a num, var, an Neg of an non-Neg atom
   * a Pow(n,x) with n a Num  and x a Var.
   * irrational numbers are atom as well, but the recognition of
   * irational numbers is limited to nthroots
   * this definition is not very perfect by any means, but we will work with that for now
   * there is no real reasons to define atoms as such, so they need more thinking
   *
   * The idea of the atoms is to have something containing all non-reductible node, in
   * particular some irreductible representation of all numbers (Rational and Irratinal) as well
   * as variables. I am not sure why Pow(n, x) should be considered as an atom, but it is definitely
   * useful for other algorithms to be considered as such, so we should find a good reason to keep it as
   * an atom
   */
  def isAtom(term: Term): Boolean = term match {
    case Num(_) => true
    case PI() => true
    case E() => true
    case Var(_) => true
    case Pow(Num(_), Var(_)) => true
    case NthRoot(n, Num(r)) => r.nthRoot(n) == None
    case Neg(t) => !isNeg(t) && isAtom(t)
    case _ => false
  }

  //expandedForm is kind of similar to a disjunctive normal form on logical formula
  def isExpandedForm(term: Term): Boolean = term match {
    case Add(ts) => ts.forall{
      case Mul(ts2) => ts2.forall(isAtom)
      case _ => false
    }
    case _ => false
  }

  //note here that everything is explicitely wrapped into the sum of prod, except for subterms of the atoms
  //(like Pow(n, x) both n and x are not wrapped around the Add and Mul)
  def expandedForm(term: Term): Term = {
    def sumProduct(t: Term) = Add(List(Mul(List(t))))

    def inductionSqrt(t: Term): Term = {
      val NthRoot(n, e) = t
      e match {
        case Add(List(Mul(List(Num(r))))) => 
          require(r.nthRoot(n) == None)
          NthRoot(n, Num(r))
        case _ => throw new IllegalArgumentException
      }
    }

    def inductionStep(t: Term): Term = t match {
      case Add(ts) => Add(ts.flatMap{ case Add(ts2) => ts2 })
      case Sub(Add(ts1), Add(ts2)) => Add(ts1 ::: (ts2.map{case Mul(ts3) => Mul(Num(Rational(-1)) :: ts3) }))
      case Mul(ts) => multiply(ts)
      case Div(Add(ts1), Add(ts2)) => {
        assert(ts2.size == 1)
        val Mul(ts3) = ts2.head
        assert(ts3.size == 1)
        val Num(r) = ts3.head
        Add(ts1.map{case Mul(ts2) => Mul(Num(r.inverse) :: ts2)})
      }
      case p@Pow(t1, Add(ts)) => ts match {
        case List(Mul(List(Num(r)))) =>
          require(r.isInteger)
          if(r.isZero) sumProduct(One()) else multiply((1 to r.toInt).map(_ => t1).toList)
        case List(Mul(List(v@Var(_)))) => t1 match {
          case Add(List(Mul(List(n@Num(_))))) => Pow(n, v)
          case _ => throw new IllegalArgumentException
        }
        case _ => throw new IllegalArgumentException
      }
      case Neg(Add(ts)) => Add(ts.map{ case Mul(ts2) => Mul(Num(-1) :: ts2) })
      case v@Var(_) => sumProduct(v)
      case n@Num(_) => sumProduct(n)
      case e@E() => sumProduct(e)
      case pi@PI() => sumProduct(pi)
      case NthRoot(_, e) => inductionSqrt(e)
      case _ => throw new IllegalArgumentException
    }

    def multiply(ts : List[Term]): Term = {
      require(!ts.isEmpty)
      def distribute(add1: Term, add2: Term): Term = (add1, add2) match {
        case (Add(ts1), Add(ts2)) => Add(ts1.flatMap{
          case Mul(tss1) => ts2.map{
            case Mul(tss2) => Mul(tss1 ::: tss2)
            case _ => sys.error("was expecting muls")
          }
          case _ => sys.error("was expecting muls")
        })
        case _ => sys.error("was expecting adds")
      }
      ts.reduceLeft(distribute)
    }

    mapPostorder(term, f => f, inductionStep)
  }


  /* Helpers */

  private def isNum(t: Term) = t match {
    case Num(_) => true
    case _ => false
  }
  private def isZero(t: Term) = t match {
    case Num(r) => r.isZero
    case _ => false
  }
  private def isOne(t: Term) = t match {
    case Num(r) => r.isOne
    case _ => false
  }
  private def isAdd(t: Term) = t match {
    case Add(_) => true
    case _ => false
  }
  private def isMul(t: Term) = t match {
    case Mul(_) => true
    case _ => false
  }
  private def isNeg(t: Term) = t match {
    case Neg(_) => true
    case _ => false
  }
  private def isNumOrProdWithNum(t: Term) = t match {
    case Num(_) => true
    case Mul(lExpr) => lExpr.exists(isNum)
    case _ => false
  }
  private def isDivWithNonZeroNumDenom(t: Term) = t match {
    case Div(_, Num(r)) if !r.isZero => true
    case _ => false
  }
  private def isSubOfNum(t: Term) = t match {
    case Sub(_, Num(r)) => true
    case _ => false
  }
}
