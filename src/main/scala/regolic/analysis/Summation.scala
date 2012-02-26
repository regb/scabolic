package regolic.analysis

import Preamble._
import regolic.algebra.Rational

class Summation(
  val variable: Variable, 
  val from: Term,
  val to: Term,
  val body: Term) {

  require(!contains(from, variable) && !contains(to, variable))

  def closedFormula: Option[Term] = {

    val newVar = variable
    val newBody = body
    val newTo = to

    def sumExpr(t: Term): Option[Term] = t match {
      case mul@Mul(_) => {
        def isolateDiv(m: Term): Term =  m match {
          case Mul(ts) => {
            val (divs, rest) = ts.partition(isDiv)
            val (divisor, mult) = divs.foldLeft((Num(1),Num(1)))((a,div) => div match {
              case Div(t1, t2) => (a._1 * t1, a._2 * t2)
              case _ => sys.error("unexpected")
            })
            if(divisor == Num(1)) Mul(mult::rest) else
            Div(Mul(mult :: rest), divisor)
          }
          case _ => sys.error("unexpected")
        }

        val (ts, div) = isolateDiv(mul) match {
          case Mul(ts) => (ts, Num(1))
          //case d:IntDiv => (d :: Nil, Num(1))
          case Div(Mul(ts), e) => (ts, e)
          case n@Num(_) => (n :: Nil, Num(1))
          case _ => sys.error("unexpected")
        }

        if(contains(div, newVar)) 
          None
        else {

          val (csts, rest) = ts.partition(x => !contains(x, newVar))
          val (exps, rest2) = rest.partition(isPow)
          val expBase = exps match {
            case List(Pow(
              Add(List(Mul(List(n@Num(_))))),
              Add(List(Mul(List(x))))))
              if (x == newVar) => n
            case Nil => Num(1)
            case _ => sys.error("not solvable")
          }
          val power = 
          if (rest2.forall{case v@Var(_) if (v == newVar) => true; case _ => false})
            rest2.length
          else
            sys.error("too complex div: " + rest2)

          val upperBound = freshVar("to")
          val clForm = (
            if(expBase == Num(1) && power == 0) 
              Add(List(upperBound, Num(1)))
            else if(expBase == Num(1) && power == 1)	
              Div(
                Mul(List(
                  upperBound,
                  Add(List(upperBound, Num(1))))),
                Num(Rational(2)))
            //else if(expBase == Num(1) && power == 2) (upperBound * (upperBound+1)* ((upperBound*2)+1)) / 6
            //else if(expBase == Num(1) && power == 3) (upperBound*upperBound*(upperBound+1)*(upperBound+1))/4
            //else if(power == 0) (Pow(expBase, upperBound+1) - 1)/(expBase-1) //geometric serie
            //else if(expBase == Num(1) && power == -1) H(upperBound) //harmonic serie
            else 
              SimpleGosper(newVar, Num(Rational(power)), expBase, upperBound)
          )
        
          val fclf = substitute(clForm, upperBound, newTo)

          Some(simplify(csts match {
              case Nil => Div(fclf, div)
              case list => Div(Mul(fclf :: list), div)
            }))
        }
      }
      case Div(t1,t2) if(!contains(t2, newVar)) => sumExpr(t1) match {
        case Some(res) => Some(Div(res,t2))
        case None => None
      }
      case n@Num(_) => sumExpr(Mul(List(n)))
      case v@Var(_) => sumExpr(Mul(List(v)))
      case e@Pow(_,_) => sumExpr(Mul(List(e)))
      case x@_ => sys.error("unexpected " + x)
    }

    val secondSum = new Summation(variable, 0, Sub(from, 1), body)
    val toSubtract = if(from == Num(0)) Num(0) else secondSum.closedFormula.get
    val expForm = expandedForm(newBody)
    val res = expForm match {
      case Add(ts) => {
        val res = ts.map(sumExpr) 
        if(res.forall({case None => false; case Some(_) => true})) 
          Some(simplify(Sub(Add(res.map({case Some(ex) => ex; case None => sys.error("strange...")})), toSubtract)))
        else None
      }
      case _ => sys.error("unexpected")
    }
    res
  }

  def isDiv(t: Term): Boolean = t match { 
    case Div(_,_) => true
    case _ => false
  }

  def isPow(t: Term): Boolean = t match {
    case Pow(_,_) => true
    case _ => false
  }
}

//class Summation(i: Variable, from: Expression, to: Expression, e: Expression) {
//  if(from.contains(i) || to.contains(i)) 
//    throw new IncoherentSummationException("summation start" + 
//    "and end cannot be described by an expression containing the iterated variable")
//
//  private def liftForm(e: Expression) : Expression = e match {
//    case v:Variable if (v == i) => Exp(v, 1)
//    case Prod(le) if le.forall(e => e == i) => Exp(i, le.length) 
//    case _ => e
//  }
//
//  private def simpleClosedForm(e: Expression, to: Expression) = { 
//    val t = freshVar
//    (e match {
//        case Number(n) => n*(t + 1)
//        case v:Variable if (v != i) => v*(t + 1)
//        case IntDiv(Number(n), v:Variable) if (n == 1 && v == i) => H(t)
//        case Exp(v:Variable, Number(n)) if (v == i && n == 1) => (t*(t + 1))/2
//        case Exp(v:Variable, Number(n)) if (v == i && n == 2) => (t*(t + 1)*(2*t + 1))/6
//        case Exp(v:Variable, Number(n)) if (v == i) => SimpleGosper(i, n, 1, t)
//        case Exp(Number(n), v:Variable) if (v == i) => SimpleGosper(i, 0, n, t)
//        case Prod(Exp(v1:Variable, Number(n)) :: Exp(Number(b), v2:Variable) :: Nil)
//        if (v1 == v2 && v2 == i) => SimpleGosper(i, n, b, t)
//          case x@_ => throw new SummationFailure(x)
//      }).substitute(t, to)
//  }
//
//  private def closedForm(from: Expression, to: Expression)(e: Expression) : Expression = {
//    def isCst(e: Expression) = !e.contains(i)
//
//      println("Summing " + expand(e) + " over " + i)
//
//    expand(e) match {
//      case Sum(lExpr) => Sum(lExpr.map(closedForm(from, to)_))
//      case Prod(lExpr) if (lExpr.exists(isCst)) => {
//        val (csts: List[Number], exps) = lExpr.partition(isCst)
//          val exps2 = if (exps.isEmpty) Number(1) :: Nil else exps
//        Prod(closedForm(from, to)(Prod(exps2)) :: csts)
//      }
//      /*case Prod(lExpr) => {
//        val (svars, rest) = lExpr.partition(_ == i)
//          val (exps, bad) =    
//        }*/
//      case IntDiv(e1, e2) if (!isCst(e1) && isCst(e2)) =>
//      IntDiv(closedForm(from, to)(e1), e2)
//      case IntDiv(e1, e2) if (isCst(e1) && !isCst(e2) && e1 != Number(1)) =>
//      Prod(e1 :: closedForm(from, to)(IntDiv(1, e2)) :: Nil)
//      case x@IntDiv(e1, e2) if (isCst(e1) && isCst(e2)) =>
//      Prod(x :: closedForm(from, to)(1) :: Nil)
//      case Div(e1, e2) if (!isCst(e1) && isCst(e2)) => 
//      Div(closedForm(from, to)(e1), e2)
//      case x@Div(e1, e2) if (isCst(e1) && isCst(e2)) =>
//      Prod(closedForm(from, to)(1) :: x :: Nil)
//      //case v:Variable if (v == i) => closedForm(from, to)(Exp(v, 1))
//      case x@_ => {
//        val f = liftForm(x)
//          simpleClosedForm(f, to) - simpleClosedForm(f, from - 1)
//      }
//    }
//  }
//
//  def closedFormula: Option[Expression] = {
//    try {
//      Some(flatten(closedForm(from, to)(e)))
//    } catch {
//      case SummationFailure(e) => println("Cannot Sum: " + e); None
//    }
//}
//}
//
