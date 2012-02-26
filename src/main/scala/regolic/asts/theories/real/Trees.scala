package regolic.asts.theories.real

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees.Constant
import regolic.asts.fol.{Trees => FolT}
import regolic.algebra.Rational

object Trees {

  object RealSort {
    def apply() = Sort("Real")
    def unapply(sort: Sort): Boolean = sort match {
      case Sort("Real") => true
      case _ => false
    }
  }

  object EqualsSymbol {
    def apply(): PredicateSymbol = FolT.EqualsSymbol(RealSort())
    def unapply(s: PredicateSymbol): Boolean = s match {
      case FolT.EqualsSymbol(RealSort()) => true
      case _ => false
    }
  }
  object Equals {
    def apply(t1: Term, t2: Term): PredicateApplication = PredicateApplication(EqualsSymbol(), List(t1, t2))
    def unapply(pApply: PredicateApplication): Option[(Term, Term)] = pApply match {
      case PredicateApplication(EqualsSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object LessThanSymbol {
    def apply() = PredicateSymbol("<", List(RealSort(), RealSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol("<", List(RealSort(), RealSort())) => true
      case _ => false
    }
  }
  object LessThan {
    def apply(t1: Term, t2: Term) = PredicateApplication(LessThanSymbol(), List(t1, t2))
    def unapply(appli: PredicateApplication): Option[(Term, Term)] = appli match {
      case PredicateApplication(LessThanSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object LessEqualSymbol {
    def apply() = PredicateSymbol("<=", List(RealSort(), RealSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol("<=", List(RealSort(), RealSort())) => true
      case _ => false
    }
  }
  object LessEqual {
    def apply(t1: Term, t2: Term) = PredicateApplication(LessEqualSymbol(), List(t1, t2))
    def unapply(appli: PredicateApplication): Option[(Term, Term)] = appli match {
      case PredicateApplication(LessEqualSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object GreaterThanSymbol {
    def apply() = PredicateSymbol(">", List(RealSort(), RealSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol(">", List(RealSort(), RealSort())) => true
      case _ => false
    }
  }
  object GreaterThan {
    def apply(t1: Term, t2: Term) = PredicateApplication(GreaterThanSymbol(), List(t1, t2))
    def unapply(appli: PredicateApplication): Option[(Term, Term)] = appli match {
      case PredicateApplication(GreaterThanSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object GreaterEqualSymbol {
    def apply() = PredicateSymbol(">=", List(RealSort(), RealSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol(">=", List(RealSort(), RealSort())) => true
      case _ => false
    }
  }
  object GreaterEqual {
    def apply(t1: Term, t2: Term) = PredicateApplication(GreaterEqualSymbol(), List(t1, t2))
    def unapply(appli: PredicateApplication): Option[(Term, Term)] = appli match {
      case PredicateApplication(GreaterEqualSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object Var {
    def apply(name: String): Variable = Variable(name, RealSort())
    def unapply(v: Variable): Option[String] = v match {
      case Variable(name, RealSort()) => Some(name)
      case _ => None
    }
  }

  object Num {
    def apply(r: Rational) = Constant(r.toString, RealSort())
    def unapply(appli: FunctionApplication): Option[Rational] = appli match {
      case Constant(str, RealSort()) => try {
        Some(Rational(str))
      } catch {
        case _ => None
      }
      case _ => None
    }
  }

  object Zero {
    def apply() = Num(Rational(0))
    def unapply(appli: FunctionApplication): Boolean = appli match {
      case Constant(str, RealSort()) => try {
        Rational(str).isZero
      } catch {
        case _ => false
      }
      case _ => false
    }
  }
  object One {
    def apply() = Num(Rational(1))
    def unapply(appli: FunctionApplication): Boolean = appli match {
      case Constant(str, RealSort()) => try {
        Rational(str).isOne
      } catch {
        case _ => false
      }
      case _ => false
    }
  }

  object E {
    def apply() = Constant("e", RealSort())
    def unapply(appli: FunctionApplication): Boolean = appli match {
      case Constant("e", RealSort()) => true
      case _ => false
    }
  }
  object PI {
    def apply() = Constant("pi", RealSort())
    def unapply(appli: FunctionApplication): Boolean = appli match {
      case Constant("pi", RealSort()) => true
      case _ => false
    }
  }

  object NthRootSymbol {
    def apply(index: Int) = FunctionSymbol(index + "-th-root", List(RealSort()), RealSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
        case FunctionSymbol(str, List(RealSort()), RealSort()) => {
          val parts = str.split('-')
          try {
            if(parts.size == 3 && parts(1) == "th" && parts(2) == "root")
              Some(parts(0).toInt)
            else
              None
          } catch {
            case _ => None
          }
        }
        case _ => None
    }
  }
  object NthRoot {
    def apply(index: Int, t: Term) = FunctionApplication(NthRootSymbol(index), List(t))
    def unapply(appli: FunctionApplication): Option[(Int, Term)] = appli match {
      case FunctionApplication(NthRootSymbol(index), List(t)) => Some((index, t))
      case _ => None
    }
  }

  object Sqrt {
    def apply(t: Term) = FunctionApplication(NthRootSymbol(2), List(t))
    def unapply(appli: FunctionApplication): Option[Term] = appli match {
      case FunctionApplication(NthRootSymbol(2), List(t)) => Some(t)
      case _ => None
    }
  }
  object CubeRoot {
    def apply(t: Term) = FunctionApplication(NthRootSymbol(3), List(t))
    def unapply(appli: FunctionApplication): Option[Term] = appli match {
      case FunctionApplication(NthRootSymbol(3), List(t)) => Some(t)
      case _ => None
    }
  }

  object AddSymbol {
    def apply(n: Int) = FunctionSymbol("+", (1 to n).map(_ => RealSort()).toList, RealSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("+", argsSort, RealSort()) if argsSort.forall(s => s == RealSort()) => Some(argsSort.size)
      case _ => None
    }
  }
  object Add {
    def apply(ts: List[Term]) = FunctionApplication(AddSymbol(ts.size), ts)
    def apply(ts: Term*) = FunctionApplication(AddSymbol(ts.size), ts.toList)
    def unapply(appli: FunctionApplication): Option[List[Term]] = appli match {
      case FunctionApplication(AddSymbol(_), ts) => Some(ts)
      case _ => None
    }
  }

  object SubSymbol {
    def apply() = FunctionSymbol("-", List(RealSort(), RealSort()), RealSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
      case FunctionSymbol("-", List(RealSort(), RealSort()), RealSort()) => true
      case _ => false
    }
  }
  object Sub {
    def apply(t1: Term, t2: Term) = FunctionApplication(SubSymbol(), List(t1, t2))
    def unapply(appli: FunctionApplication): Option[(Term, Term)] = appli match {
      case FunctionApplication(SubSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object MulSymbol {
    def apply(n: Int) = FunctionSymbol("*", (1 to n).map(_ => RealSort()).toList, RealSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("*", argsSort, RealSort()) if argsSort.forall(s => s == RealSort()) => Some(argsSort.size)
      case _ => None
    }
  }
  object Mul {
    def apply(ts: List[Term]) = FunctionApplication(MulSymbol(ts.size), ts)
    def unapply(appli: FunctionApplication): Option[List[Term]] = appli match {
      case FunctionApplication(MulSymbol(_), ts) => Some(ts)
      case _ => None
    }
  }

  object DivSymbol {
    def apply() = FunctionSymbol("/", List(RealSort(), RealSort()), RealSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
      case FunctionSymbol("/", List(RealSort(), RealSort()), RealSort()) => true
      case _ => false
    }
  }
  object Div {
    def apply(t1: Term, t2: Term) = FunctionApplication(DivSymbol(), List(t1, t2))
    def unapply(appli: FunctionApplication): Option[(Term, Term)] = appli match {
      case FunctionApplication(DivSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object PowSymbol {
    def apply() = FunctionSymbol("^", List(RealSort(), RealSort()), RealSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
      case FunctionSymbol("^", List(RealSort(), RealSort()), RealSort()) => true
      case _ => false
    }
  }
  object Pow {
    def apply(t1: Term, t2: Term) = FunctionApplication(PowSymbol(), List(t1, t2))
    def unapply(appli: FunctionApplication): Option[(Term, Term)] = appli match {
      case FunctionApplication(PowSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object Exp {
    def apply(t: Term) = FunctionApplication(PowSymbol(), List(E(), t))
    def unapply(appli: FunctionApplication): Option[Term] = appli match {
      case FunctionApplication(PowSymbol(), List(E(), t)) => Some(t)
      case _ => None
    }
  }

  object LogSymbol {
    def apply() = FunctionSymbol("log", List(RealSort(), RealSort()), RealSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
      case FunctionSymbol("log", List(RealSort(), RealSort()), RealSort()) => true
      case _ => false
    }
  }
  object Log {
    def apply(base: Term, t: Term) = FunctionApplication(LogSymbol(), List(base, t))
    def unapply(appli: FunctionApplication): Option[(Term, Term)] = appli match {
      case FunctionApplication(LogSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object Ln {
    def apply(t: Term) = FunctionApplication(LogSymbol(), List(E(), t))
    def unapply(appli: FunctionApplication): Option[Term] = appli match {
      case FunctionApplication(LogSymbol(), List(E(), t)) => Some(t)
      case _ => None
    }
  }

  object NegSymbol {
    def apply() = FunctionSymbol("-", List(RealSort()), RealSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
        case FunctionSymbol("-", List(RealSort()), RealSort()) => true
        case _ => false
    }
  }
  object Neg {
    def apply(t: Term) = FunctionApplication(NegSymbol(), List(t))
    def unapply(appli: FunctionApplication): Option[Term] = appli match {
      case FunctionApplication(NegSymbol(), List(t)) => Some(t)
      case _ => None
    }
  }

  object AbsSymbol {
    def apply() = FunctionSymbol("abs", List(RealSort()), RealSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
        case FunctionSymbol("abs", List(RealSort()), RealSort()) => true
        case _ => false
    }
  }
  object Abs {
    def apply(t: Term) = FunctionApplication(AbsSymbol(), List(t))
    def unapply(appli: FunctionApplication): Option[Term] = appli match {
      case FunctionApplication(AbsSymbol(), List(t)) => Some(t)
      case _ => None
    }
  }

  object FloorSymbol {
    def apply() = FunctionSymbol("floor", List(RealSort()), RealSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
        case FunctionSymbol("intpart", List(RealSort()), RealSort()) => true
        case _ => false
    }
  }
  object Floor {
    def apply(t: Term) = FunctionApplication(FloorSymbol(), List(t))
    def unapply(appli: FunctionApplication): Option[Term] = appli match {
      case FunctionApplication(FloorSymbol(), List(t)) => Some(t)
      case _ => None
    }
  }

  object MaxSymbol {
    def apply(n: Int) = FunctionSymbol("max", (1 to n).map(_ => RealSort()).toList, RealSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("max", argsSort, RealSort()) if argsSort.forall(s => s == RealSort()) => Some(argsSort.size)
      case _ => None
    }
  }
  object Max {
    def apply(ts: List[Term]) = FunctionApplication(MaxSymbol(ts.size), ts)
    def unapply(appli: FunctionApplication): Option[List[Term]] = appli match {
      case FunctionApplication(MaxSymbol(_), ts) => Some(ts)
      case _ => None
    }
  }

  object MinSymbol {
    def apply(n: Int) = FunctionSymbol("min", (1 to n).map(_ => RealSort()).toList, RealSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("min", argsSort, RealSort()) if argsSort.forall(s => s == RealSort()) => Some(argsSort.size)
      case _ => None
    }
  }
  object Min {
    def apply(ts: List[Term]) = FunctionApplication(MinSymbol(ts.size), ts)
    def unapply(appli: FunctionApplication): Option[List[Term]] = appli match {
      case FunctionApplication(MinSymbol(_), ts) => Some(ts)
      case _ => None
    }
  }

  def freshVar(prefix: String = "x"): Variable = freshVariable(prefix, RealSort())
}
