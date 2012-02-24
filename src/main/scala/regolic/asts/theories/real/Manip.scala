package regolic.asts.theories.real

import regolic.asts.theories.real.Trees._
import regolic.asts.core.Trees.{Formula, Term, Variable}
import regolic.asts.core.Manip._
import regolic.algebra.Rational
import regolic.tools.Math.fix
import regolic.tools.SeqTools.mapUnique

/*
 * One of the design principle of the Manip object is to contain only basic
 * operation on the associated tree. Any "advanced" algorithm should be provide as a separate code
 * in a separate package. This Manip object tries to provide the most comonly used features.
 *
 * Note also that most of these methods do not do anything too smart, in particular a method like
 * isPolynomial will not give a completely correct answer, in particular it will not attemp to simplify the formula to
 * see whether some terms cancels out
 */

//maybe only do the safe modification (for example, not 0 * 1/a, because a 
//could be 0) here, and having a more aggressive system in calculus that could 
//return a list of assumption or take a list of assumption in addition

object Manip {

  def isSingleVarPolynomial(term: Term) = isPolynomial(term) && (vars(term).size == 1)

  //Is polynomial (accepting multiple variables)
  //do not require the polynomial to be in a standard form
  def isPolynomial(term: Term): Boolean = term match {
    case Var(_) => true
    case Num(_) => true
    case Add(ts) => ts.forall(isPolynomial(_))
    case Sub(t1, t2) => isPolynomial(t1) && isPolynomial(t2)
    case Mul(ts) => ts.forall(isPolynomial(_))
    case Neg(t) => isPolynomial(t)
    case Div(t1, Num(_)) => isPolynomial(t1)
    case Pow(t1, Num(r)) => isPolynomial(t1) && r.isInteger
    case Floor(Num(_)) => true
    case Abs(Num(_)) => true
   
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
      case Add(ts@( Mul(List(coef, Pow(v, Num(r))))::_ )) => isCorrectPower(r, ts)
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

  def toLnAndExp(term: Term): Term = {
    def inductionStep(t: Term): Term = t match {
      case Log(b, t) if b != E() => Div(Ln(t), Ln(b))
      case Pow(b, t) if b != E() => Exp(Mul(List(t, Ln(b))))
      case _ => t
    }
    mapPostorder(term, f => f, inductionStep)
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

  def isRational(term: Term): Boolean = {
    def notRationalNode(t: Term): Boolean = t match {
      case Max(_) | Min(_) => true
      case Pow(t1, t2) => !isNum(t2)
      case Floor(t2) if !isNum(t2) => true
      case Abs(t2) => !isNum(t2)
      case _ => false
    }
    forall(term, (t: Term) => !notRationalNode(t))
  }

  def expandedRationalForm(term: Term): Term = {
    require(isRational(term))

    def wrap(t: Term) = 
      Div(
        Add(List(Mul(List(t)))),
        Add(List(Mul(List(Num(1))))))

    def inductionStep(t: Term): Term = t match {
      case Add(ts) => {
        val denominator: Term = multiply(ts.map{ case Div(_, d) => d })
        val numerators: List[Term] = ts.zipWithIndex.map{ case (Div(n, _), i) =>
          multiply(ts.zipWithIndex.flatMap{ case(Div(_, d), j) => 
            if(j != i) List(d) else List(n) //take numerator of the current one
          })
        }
        val numerator: Term = Add(numerators.flatMap{ case Add(xs) => xs })
        Div(numerator, denominator)
      }
      case Sub(Div(ts1n, ts1d), Div(ts2n, ts2d)) => {
        val denominator = multiply(List(ts1d, ts2d))
        val numerator = multiply(List(ts1n, ts2d)) match {
          case Add(ts3) => multiply(List(ts2n, ts1d)) match {
            case Add(ts4) => Add(ts3 ::: ts4.map{ 
              case Mul(ts) => Mul(Num(-1) :: ts)
            })
          }
        }
        Div(numerator, denominator)
      }
      case Mul(ts) => {
        val denominator = multiply(ts.map{ case Div(_, d) => d })
        val numerator = multiply(ts.map{ case Div(n, _) => n })
        Div(numerator, denominator)
      }
      case d@Div(Div(ts1n, ts1d), Div(ts2n, ts2d)) => {
        val denominator = multiply(List(ts1d, ts2n))
        val numerator = multiply(List(ts1n, ts2d))
        Div(numerator, denominator)
      }
      case v@Var(_) => wrap(v)
      case n@Num(_) => wrap(n)
      case n@Neg(Var(_)) => wrap(n)
      case n@Neg(Num(_)) => wrap(n)
      case _ => sys.error("Not expected")
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

    mapPostorder(expandPower(term), f => f, inductionStep)
  }

  def rationalForm(term: Term, variable: Variable): Term = {
    require(isRational(term))

    val Div(numerator, denominator) = expandedRationalForm(term)
    Div(polynomialForm(numerator, variable), polynomialForm(denominator, variable))
  }

  /* Apply local simplifications, only if the size of the tree is reduced */
  def simplify(term: Term): Term = {

    def simplifyOne(t: Term): Term = {
      def simplifyOneAdd(t: Term): Term = t match {
        case Add(Nil) => Zero()
        case Add(List(t)) => t
        case Add(ts) if ts.exists(isZero) => Add(ts.filterNot(isZero))
        case Add(ts) if ts.exists(isAdd) => flatten(t)
        case Add(ts) if ts.count(isNum) > 1 => {
          val (csts, rts) = ts.partition(isNum)
          val nr = csts.asInstanceOf[List[Term]].foldLeft(Rational(0))((a, c) => a + (c match { case Num(r) => r case _ => sys.error("unexpected") }))
          Add(Num(nr) :: rts)
        }
        case Add(ts) if ts.exists(isSubOfNum) && ts.exists(isNum) => {
          val (rts1, Num(r1)::rts2) = ts.span(t => !isNum(t))
          val (rrts1, Sub(t1, Num(r2))::rrts2) = (rts1:::rts2).span(t => !isSubOfNum(t))
          Add(Num(r1 - r2) :: t1 :: (rrts1 ::: rrts2))
        }
        case _ => t
      }
      def simplifyOneSub(t: Term): Term = t match {
        case Sub(t, Num(r)) if r.isZero => t
        case Sub(Num(r), t) if r.isZero => Neg(t)
        case Sub(Num(a), Num(b)) => Num(a - b)
        case Sub(t1, t2) if t1 == t2 => Num(0)
        case _ => t
      }
      def simplifyOneNeg(t: Term): Term = t match {
        case Neg(Neg(t2)) => t2
        case Neg(Sub(t1, t2)) => Sub(t2, t1)
        case _ => t
      }
      def simplifyOneMul(t: Term): Term = t match {
        case Mul(Nil) => One()
        case Mul(List(t)) => t
        case Mul(ts) if ts.exists(isZero) => Zero()
        case Mul(ts) if ts.exists(isOne) => Mul(ts.filterNot(isOne))
        case Mul(ts) if ts.exists(isMul) => flatten(t)
        case Mul(ts) if ts.count(isNum) > 1 => {
          val (csts, rts) = ts.partition(isNum)
          val nr = csts.foldLeft(Rational(1))((a, c) => a * (c match { case Num(r) => r case _ => sys.error("unexpected") }))
          Mul(Num(nr) :: rts)
        }
        case Mul(ts) if ts.exists(isNum) && ts.exists(isDivWithNonZeroNumDenom) => {
          val (rts1, Num(r1)::rts2) = ts.span(t => !isNum(t))
          val (rrts1, Div(t1, Num(r2))::rrts2) = (rts1:::rts2).span(t => !isDivWithNonZeroNumDenom(t))
          Mul(Num(r1/r2) :: t1 :: (rrts1 ::: rrts2))
        }
        case Mul(Num(r) :: Add(ts) :: Nil) if ts.forall(isNumOrProdWithNum) => {
          Add(ts.map((t: Term) => t match {
            case Num(r2) => Num(r*r2)
            case Mul(ts2) => Mul(mapUnique((t: Term) => t match { 
                case Num(r2) => Some(Num(r*r2)) 
                case _ => None 
              }, ts2))
            case _ => sys.error("unexpected")
          }))
        }
        case _ => t
      }
      def simplifyOneDiv(t: Term): Term = t match {
        case Div(t, Num(r)) if r.isOne => t
        case Div(Num(r), t) if r.isZero => Zero()
        case Div(Num(a), Num(b)) if !b.isZero => Num(a / b)
        case Div(Mul(ts), Num(r)) if ts.exists(isNum) && !r.isZero => Mul(mapUnique((t: Term) => t match { 
            case Num(r2) => Some(Num(r2/r))
            case _ => None 
          }, ts))
        case _ => t
      }
      def simplifyOnePow(t: Term): Term = t match {
        case Pow(t, Num(r)) if r.isOne => t
        case Pow(t, Num(r)) if r.isZero => One() //TODO: 0^0 might be a problem, could have some analysis that ensure non zero, similarly non even etc
        case Pow(Num(r), t) if r.isOne => One()
        case Pow(Num(r), t) if r.isZero => Zero()
        case Pow(Num(a), Num(b)) if b.isInteger => Num(a.toPower(b.toBigInt))
        case _ => t
      }
      def simplifyOneFloor(t: Term): Term = t match {
        case Floor(Num(r)) => Num(r.floor)
        case _ => t
      }
      def simplifyOneSqrt(t: Term): Term = t match {
        case Sqrt(Num(r)) => r.sqrt match {
          case Some(r2) => Num(r2)
          case None => t
        }
        case Sqrt(Pow(x, Num(r))) if r == Rational(2) => Abs(x)
        case Sqrt(Mul(List(t1, t2))) if t1 == t2 => Abs(t1)
        case _ => t
      }

      t match {
        case Add(_) => simplifyOneAdd(t)
        case Sub(_, _) => simplifyOneSub(t)
        case Neg(_) => simplifyOneNeg(t)
        case Mul(_) => simplifyOneMul(t)
        case Div(_,_) => simplifyOneDiv(t)
        case Pow(_,_) => simplifyOnePow(t)
        case Floor(_) => simplifyOneFloor(t)
        case Sqrt(_) => simplifyOneSqrt(t)
        case _ => t
      }
    }

    def mapSimplify(t: Term): Term = mapPostorder(t, x => x, simplifyOne)

    fix(mapSimplify,term)
  }

  /* Helpers */

  private def flatten(t: Term): Term = t match {
    case Add(ts) => Add(ts.flatMap{case Add(ts2) => ts2 case t2 => List(t2)})
    case Mul(ts) => Mul(ts.flatMap{case Mul(ts2) => ts2 case t2 => List(t2)})
    case _ => t
  }
  private def isDiv(t: Term) = t match {
    case Div(_,_) => true
    case _ => false
  }
  private def isVar(t: Term): Boolean = t match {
    case Var(_) => true
    case _ => false
  }
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
