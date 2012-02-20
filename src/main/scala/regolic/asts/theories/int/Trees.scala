package regolic.asts.theories.int

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees.Constant
import regolic.asts.fol.{Trees => FolT}

object Trees {

  object IntSort {
    def apply() = Sort("Int")
    def unapply(sort: Sort): Boolean = sort match {
      case Sort("Int") => true
      case _ => false
    }
  }

  object EqualsSymbol {
    def apply(): PredicateSymbol = FolT.EqualsSymbol(IntSort())
    def unapply(s: PredicateSymbol): Boolean = s match {
      case FolT.EqualsSymbol(IntSort()) => true
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
    def apply() = PredicateSymbol("<", List(IntSort(), IntSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol("<", List(IntSort(), IntSort())) => true
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
    def apply() = PredicateSymbol("<=", List(IntSort(), IntSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol("<=", List(IntSort(), IntSort())) => true
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
    def apply() = PredicateSymbol(">", List(IntSort(), IntSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol(">", List(IntSort(), IntSort())) => true
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
    def apply() = PredicateSymbol(">=", List(IntSort(), IntSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol(">=", List(IntSort(), IntSort())) => true
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
    def apply(name: String): Variable = Variable(name, IntSort())
    def unapply(v: Variable): Option[String] = v match {
      case Variable(name, IntSort()) => Some(name)
      case _ => None
    }
  }

  object Num {
    def apply(n: BigInt) = Constant(n.toString, IntSort())
    def unapply(appli: FunctionApplication): Option[BigInt] = appli match {
      case Constant(n, IntSort()) => try {
        Some(BigInt(n))
      } catch {
        case _ => None
      }
      case _ => None
    }
  }

  object AddSymbol {
    def apply(n: Int) = FunctionSymbol("+", (1 to n).map(_ => IntSort()).toList, IntSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("+", argsSort, IntSort()) if argsSort.forall(s => s == IntSort()) => Some(argsSort.size)
      case _ => None
    }
  }
  object Add {
    def apply(ts: List[Term]) = FunctionApplication(AddSymbol(ts.size), ts)
    def unapply(appli: FunctionApplication): Option[List[Term]] = appli match {
      case FunctionApplication(AddSymbol(_), ts) => Some(ts)
      case _ => None
    }
  }

  object SubSymbol {
    def apply() = FunctionSymbol("-", List(IntSort(), IntSort()), IntSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
      case FunctionSymbol("-", List(IntSort(), IntSort()), IntSort()) => true
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
    def apply(n: Int) = FunctionSymbol("*", (1 to n).map(_ => IntSort()).toList, IntSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("*", argsSort, IntSort()) if argsSort.forall(s => s == IntSort()) => Some(argsSort.size)
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

  object MulConstSymbol {
    def apply(n: BigInt) = FunctionSymbol("*" + n.toString, List(IntSort()), IntSort())
    def unapply(symb: FunctionSymbol): Option[BigInt] = symb match {
      case FunctionSymbol(name, List(IntSort()), IntSort()) => {
        val str: Seq[Char] = name
        str match {
          case Seq('*', n @ _*) => Some(BigInt(n.toString))
          case _ => None
        }
      }
      case _ => None
    }
  }
  object MulConst {
    def apply(t: Term, n: BigInt) = FunctionApplication(MulConstSymbol(n), List(t))
    def unapply(appli: FunctionApplication): Option[(Term, BigInt)] = appli match {
      case FunctionApplication(MulConstSymbol(n), List(t)) => Some((t, n))
      case _ => None
    }
  }

  object DivSymbol {
    def apply() = FunctionSymbol("/", List(IntSort(), IntSort()), IntSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
      case FunctionSymbol("/", List(IntSort(), IntSort()), IntSort()) => true
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

  object ModSymbol {
    def apply() = FunctionSymbol("%", List(IntSort(), IntSort()), IntSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
      case FunctionSymbol("%", List(IntSort(), IntSort()), IntSort()) => true
      case _ => false
    }
  }
  object Mod {
    def apply(t1: Term, t2: Term) = FunctionApplication(ModSymbol(), List(t1, t2))
    def unapply(appli: FunctionApplication): Option[(Term, Term)] = appli match {
      case FunctionApplication(ModSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object NegSymbol {
    def apply() = FunctionSymbol("-", List(IntSort()), IntSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
        case FunctionSymbol("-", List(IntSort()), IntSort()) => true
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
    def apply() = FunctionSymbol("abs", List(IntSort()), IntSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
        case FunctionSymbol("abs", List(IntSort()), IntSort()) => true
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

  object MaxSymbol {
    def apply(n: Int) = FunctionSymbol("max", (1 to n).map(_ => IntSort()).toList, IntSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("max", argsSort, IntSort()) if argsSort.forall(s => s == IntSort()) => Some(argsSort.size)
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
    def apply(n: Int) = FunctionSymbol("min", (1 to n).map(_ => IntSort()).toList, IntSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("min", argsSort, IntSort()) if argsSort.forall(s => s == IntSort()) => Some(argsSort.size)
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
}
