package regolic.asts.theories.realint

import regolic.asts.theories.real.{Trees => R}
import regolic.asts.theories.int.{Trees => I}
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
    case I.Var(_) | R.Var(_) | I.Num(_) | R.Num(_) => true
    case I.Add(ts) => ts.forall(isPolynomial(_))
    case R.Add(ts) => ts.forall(isPolynomial(_))
    case I.Sub(t1, t2) => isPolynomial(t1) && isPolynomial(t2)
    case R.Sub(t1, t2) => isPolynomial(t1) && isPolynomial(t2)
    case I.Mul(ts) => ts.forall(isPolynomial(_))
    case R.Mul(ts) => ts.forall(isPolynomial(_))
    case I.MulConst(_, t) => isPolynomial(t)
    case I.Neg(t) => isPolynomial(t)
    case R.Neg(t) => isPolynomial(t)
    case I.Div(t1, I.Num(_)) => isPolynomial(t1)
    case R.Div(t1, R.Num(_)) => isPolynomial(t1)
    case I.Pow(t1, I.Num(_)) => isPolynomial(t1)
    case R.Pow(t1, R.Num(r)) => isPolynomial(t1) && r.isInteger
    case R.Floor(Num(_)) => true
    case R.Abs(Num(_)) => true
   
    case _ => false
  }

  def polynomialDegree(polynomial: Term, variable: Variable): BigInt = {
    require(isPolynomialForm(polynomial, variable))
    val ts = polynomial match {
			case I.Add(ts) => ts
			case R.Add(ts) => ts
		}
		val (v, degree) = ts.head match {
			case I.Mul(_ :: I.Pow(v, Num(degree))) => (v, degree)
			case R.Mul(_ :: R.Pow(v, Num(degree)) :: ms) if degree.isInteger => (v, degree.toBigInt)
		}
    assert(v == variable)
    degree
  }

  //checking that the term in in polynomial standard form
  //an*x^n + ... + a0*x^0, with an != 0
  //def isPolynomialForm(term: Term, variable: Variable): Boolean = {
  //  def isCorrectPower(n: Rational, ts: List[Term]): Boolean = ts match {
  //    case Mul(List(coef, Pow(v, Num(r)))) :: Nil => variable == v && !contains(coef, variable) && r == n && n.isZero
  //    case Mul(List(coef, Pow(v, Num(r)))) :: ts => variable == v && !contains(coef, variable) && r == n && isCorrectPower(n-1, ts)
  //    case _ => false
  //  }
  //  term match {
  //    case R.Add(ts@( R.Mul(List(coef, R.Pow(v, R.Num(r))))::_ )) => isCorrectPower(r, ts)
  //    case I.Add(ts@( I.Mul(List(coef, I.Pow(v, I.Num(r))))::_ )) => isCorrectPower(r, ts)
  //    case _ => false
  //  }
  //}

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
    //require(isPolynomial(term)) //this requires make sure that there won't be any n^x in the expanded form

    if(variables.isEmpty)
      term
    else {

      val variable = variables.head
  
      def containsNTimesVar(t: Term, degree: Int): Boolean = count(t, (_: Formula) => false, (t: Term) => t == variable) == degree
  
      def unify(ts: List[Term], degree: Int, real: Boolean): List[Term] = if(ts.isEmpty) Nil else {
        val (thisDegree, otherDegree) = ts.partition(x => containsNTimesVar(x, degree))
        val coeff = 
          (thisDegree.map {
            case R.Mul(ts) => ts.filterNot(_ == variable) match {
              case Nil => R.One()
              case t :: Nil => t
              case ts@_ => R.Mul(ts)
            }
            case I.Mul(ts) => ts.filterNot(_ == variable) match {
              case Nil => I.One()
              case t :: Nil => t
              case ts@_ => I.Mul(ts)
            }
          }) match {
              case Nil => if(real) R.Zero() else I.Zero()
              case t :: Nil => t
              case ts@_ => if(real) R.Add(ts) else I.Add(ts)
          }
        val sCoeff = simplify(coeff)
        assert(!contains(sCoeff, variable))
        val mul = if(real)
						R.Mul(List(polynomialForm(sCoeff, variables.tail), R.Pow(variable, R.Num(Rational(degree)))))
					else
						I.Mul(List(polynomialForm(sCoeff, variables.tail), I.Pow(variable, I.Num(degree))))
        if(otherDegree.isEmpty) {
          if(sCoeff == R.Zero() || sCoeff == I.Zero())
            Nil 
          else 
            List(mul)
        } else mul :: unify(otherDegree, degree+1, real)
      }
  
      val ts = expandedForm(term) match {
				case R.Add(ts) => R.Add(unify(ts, 0, true).reverse)
				case I.Add(ts) => M.Add(unify(ts, 0, false).reverse)
			}
    }
  }

  def expandPower(term: Term): Term = {
    def inductionStep(t: Term): Term = t match {
      case R.Pow(t1, R.Num(r)) if r.isInteger =>
        if(r.isZero) R.One() else I.Mul((1 to r.toInt).map(_ => t1).toList)
      case I.Pow(t1, I.Num(i)) =>
        if(i == 0) I.One() else I.Mul((1 to i).map(_ => t1).toList)
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
    case R.Num(_) | I.Num(_) => true
    case R.PI() => true
    case R.E() => true
    case R.Var(_) | I.Var(_) => true
    case R.Pow(R.Num(_), R.Var(_)) | I.Pow(I.Num(_), I.Var(_)) => true
    case R.NthRoot(n, R.Num(r)) => r.nthRoot(n) == None
    case R.Neg(t) => !isNeg(t) && isAtom(t)
    case I.Neg(t) => !isNeg(t) && isAtom(t)
    case _ => false
  }


  //expandedForm is kind of similar to a disjunctive normal form on logical formula
  def isExpandedForm(term: Term): Boolean = term match {
    case R.Add(ts) => ts.forall{
      case R.Mul(ts2) => ts2.forall(isAtom)
      case _ => false
    }
    case I.Add(ts) => ts.forall{
      case I.Mul(ts2) => ts2.forall(isAtom)
      case _ => false
    }
    case _ => false
  }

  //note here that everything is explicitely wrapped into the sum of prod, except for subterms of the atoms
  //(like Pow(n, x) both n and x are not wrapped around the Add and Mul)
  def expandedForm(term: Term): Term = {
    def sumProduct(t: Term) = if(t.sort == IntSort) I.Add(List(I.Mul(List(t)))) else R.Add(List(R.Mul(List(t))))

    def inductionStep(t: Term): Term = t match {
      case R.Add(ts) => R.Add(ts.flatMap{ case R.Add(ts2) => ts2 })
      case I.Add(ts) => I.Add(ts.flatMap{ case I.Add(ts2) => ts2 })
      case R.Sub(R.Add(ts1), R.Add(ts2)) => R.Add(ts1 ::: (ts2.map{case R.Mul(ts3) => R.Mul(R.Num(Rational(-1)) :: ts3) }))
      case I.Sub(I.Add(ts1), I.Add(ts2)) => I.Add(ts1 ::: (ts2.map{case I.Mul(ts3) => I.Mul(I.Num(-1) :: ts3) }))
      case R.Mul(ts) => multiply(ts)
      case I.Mul(ts) => multiply(ts)
      case R.Div(R.Add(ts1), R.Add(ts2)) => {
        assert(ts2.size == 1)
        val R.Mul(ts3) = ts2.head
        assert(ts3.size == 1)
        val R.Num(r) = ts3.head
        R.Add(ts1.map{case R.Mul(ts2) => R.Mul(R.Num(r.inverse) :: ts2)})
      }
      case p@R.Pow(t1, R.Add(ts)) => ts match {
        case List(R.Mul(List(R.Num(r)))) =>
          require(r.isInteger)
          if(r.isZero) sumProduct(R.One()) else multiply((1 to r.toInt).map(_ => t1).toList)
        case List(R.Mul(List(v@R.Var(_)))) => t1 match {
          case R.Add(List(R.Mul(List(n@R.Num(_))))) => R.Pow(n, v)
          case _ => throw new IllegalArgumentException
        }
        case _ => throw new IllegalArgumentException
      }
      case p@I.Pow(t1, I.Add(ts)) => ts match {
        case List(I.Mul(List(I.Num(i)))) =>
          if(i == 0) sumProduct(I.One()) else multiply((1 to i).map(_ => t1).toList)
        case List(I.Mul(List(v@I.Var(_)))) => t1 match {
          case I.Add(List(I.Mul(List(n@I.Num(_))))) => I.Pow(n, v)
          case _ => throw new IllegalArgumentException
        }
        case _ => throw new IllegalArgumentException
      }
      case R.Neg(R.Add(ts)) => R.Add(ts.map{ case R.Mul(ts2) => R.Mul(R.Num(-1) :: ts2) })
      case I.Neg(I.Add(ts)) => I.Add(ts.map{ case I.Mul(ts2) => I.Mul(I.Num(-1) :: ts2) })
      case v@R.Var(_) => sumProduct(v)
      case v@I.Var(_) => sumProduct(v)
      case n@R.Num(_) => sumProduct(n)
      case n@I.Num(_) => sumProduct(n)
      case e@R.E() => sumProduct(e)
      case pi@R.PI() => sumProduct(pi)
      case _ => throw new IllegalArgumentException
    }

    def multiply(ts : List[Term]): Term = {
      require(!ts.isEmpty)
      def distribute(add1: Term, add2: Term): Term = (add1, add2) match {
        case (I.Add(ts1), I.Add(ts2)) => I.Add(ts1.flatMap{
          case I.Mul(tss1) => ts2.map{
            case I.Mul(tss2) => I.Mul(tss1 ::: tss2)
            case _ => sys.error("was expecting muls")
          }
          case _ => sys.error("was expecting muls")
        })
        case (R.Add(ts1), R.Add(ts2)) => R.Add(ts1.flatMap{
          case R.Mul(tss1) => ts2.map{
            case R.Mul(tss2) => R.Mul(tss1 ::: tss2)
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
