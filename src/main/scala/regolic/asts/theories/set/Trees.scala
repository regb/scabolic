package regolic.asts.theories.set

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees.Constant
import regolic.asts.fol.{Trees => FolT}

object Trees {

  object SetSort {
    def apply() = Sort("Set")
    def unapply(sort: Sort): Boolean = sort match {
      case Sort("Set") => true
      case _ => false
    }
  }

  object EqualsSymbol {
    def apply(): PredicateSymbol = FolT.EqualsSymbol(SetSort())
    def unapply(s: PredicateSymbol): Boolean = s match {
      case FolT.EqualsSymbol(SetSort()) => true
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

  object IncludeSymbol {
    def apply() = PredicateSymbol("include", List(SetSort(), SetSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol("include", List(SetSort(), SetSort())) => true
      case _ => false
    }
  }
  object Include {
    def apply(t1: Term, t2: Term) = PredicateApplication(IncludeSymbol(), List(t1, t2))
    def unapply(appli: PredicateApplication): Option[(Term, Term)] = appli match {
      case PredicateApplication(IncludeSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object IncludeEqSymbol {
    def apply() = PredicateSymbol("includeeq", List(SetSort(), SetSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol("includeeq", List(SetSort(), SetSort())) => true
      case _ => false
    }
  }
  object IncludeEq {
    def apply(t1: Term, t2: Term) = PredicateApplication(IncludeEqSymbol(), List(t1, t2))
    def unapply(appli: PredicateApplication): Option[(Term, Term)] = appli match {
      case PredicateApplication(IncludeEqSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object Var {
    def apply(name: String): Variable = Variable(name, SetSort())
    def unapply(v: Variable): Option[String] = v match {
      case Variable(name, SetSort()) => Some(name)
      case _ => None
    }
  }

  object Empty {
    def apply() = Constant("empty", SetSort())
    def unapply(appli: FunctionApplication): Boolean = appli match {
      case Constant("empty", SetSort()) => true
      case _ => false
    }
  }

  object Universe {
    def apply() = Constant("universe", SetSort())
    def unapply(appli: FunctionApplication): Boolean = appli match {
      case Constant("universe", SetSort()) => true
      case _ => false
    }
  }

  object ConstructorSymbol {
    def apply(name: String, arity: Int): FunctionSymbol = FunctionSymbol(name, (1 to arity).map(_ => SetSort()).toList, SetSort())
    def unapply(symb: FunctionSymbol): Option[(String, Int)] = symb match {
      case FunctionSymbol(name, argsSort, SetSort()) if argsSort.forall(s => s == SetSort()) => Some(name, argsSort.size)
      case _ => None
    }
  }
  object Constructor {
    def apply(name: String, ts: List[Term]) = FunctionApplication(ConstructorSymbol(name, ts.size), ts)
    def unapply(appli: FunctionApplication): Option[(String, List[Term])] = appli match {
      case FunctionApplication(ConstructorSymbol(name, _), ts) => Some((name, ts))
      case _ => None
    }
  }

  object UnionSymbol {
    def apply(n: Int) = FunctionSymbol("union", (1 to n).map(_ => SetSort()).toList, SetSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("union", argsSort, SetSort()) if argsSort.forall(s => s == SetSort()) => Some(argsSort.size)
      case _ => None
    }
  }
  object Union {
    def apply(ts: List[Term]) = FunctionApplication(UnionSymbol(ts.size), ts)
    def unapply(appli: FunctionApplication): Option[List[Term]] = appli match {
      case FunctionApplication(UnionSymbol(_), ts) => Some(ts)
      case _ => None
    }
  }

  object IntersectionSymbol {
    def apply(n: Int) = FunctionSymbol("intersection", (1 to n).map(_ => SetSort()).toList, SetSort())
    def unapply(symb: FunctionSymbol): Option[Int] = symb match {
      case FunctionSymbol("intersection", argsSort, SetSort()) if argsSort.forall(s => s == SetSort()) => Some(argsSort.size)
      case _ => None
    }
  }
  object Intersection {
    def apply(ts: List[Term]) = FunctionApplication(IntersectionSymbol(ts.size), ts)
    def unapply(appli: FunctionApplication): Option[List[Term]] = appli match {
      case FunctionApplication(IntersectionSymbol(_), ts) => Some(ts)
      case _ => None
    }
  }

  object ComplementSymbol {
    def apply() = FunctionSymbol("complement", List(SetSort()), SetSort())
    def unapply(symb: FunctionSymbol): Boolean = symb match {
        case FunctionSymbol("complement", List(SetSort()), SetSort()) => true
        case _ => false
    }
  }
  object Complement {
    def apply(t: Term) = FunctionApplication(ComplementSymbol(), List(t))
    def unapply(appli: FunctionApplication): Option[Term] = appli match {
      case FunctionApplication(ComplementSymbol(), List(t)) => Some(t)
      case _ => None
    }
  }
}
/*
  object InSymbol {
    def apply() = PredicateSymbol("in", List(SetSort(), SetSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol("in", List(SetSort(), SetSort())) => true
      case _ => false
    }
  }
  object In {
    def apply(t1: Term, t2: Term) = PredicateApplication(InSymbol(), List(t1, t2))
    def unapply(appli: PredicateApplication): Option[(Term, Term)] = appli match {
      case PredicateApplication(InSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object ContainsSymbol {
    def apply() = PredicateSymbol("contains", List(SetSort(), SetSort()))
    def unapply(symb: PredicateSymbol): Boolean = symb match {
      case PredicateSymbol("contains", List(SetSort(), SetSort())) => true
      case _ => false
    }
  }
  object Contains {
    def apply(t1: Term, t2: Term) = PredicateApplication(ContainsSymbol(), List(t1, t2))
    def unapply(appli: PredicateApplication): Option[(Term, Term)] = appli match {
      case PredicateApplication(ContainsSymbol(), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }
*/
