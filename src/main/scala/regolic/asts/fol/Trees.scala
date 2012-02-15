package regolic.asts.fol

import regolic.asts.core.Trees._

object Trees {

  object ConstantSymbol {
    def apply(name: String, sort: Sort) = FunctionSymbol(name, Nil, sort)
    def unapply(symbol: FunctionSymbol): Option[(String, Sort)] = symbol match {
      case FunctionSymbol(n, Nil, s) => Some((n, s))
      case _ => None
    }
  }
  object Constant {
    def apply(name: String, sort: Sort) = FunctionApplication(ConstantSymbol(name, sort), Nil)
    def unapply(apply: FunctionApplication): Option[(String, Sort)] = apply match {
      case FunctionApplication(ConstantSymbol(n, s), Nil) => Some((n, s))
      case _ => None
    }
  }

  object EqualsSymbol {
    def apply(sort: Sort): PredicateSymbol = PredicateSymbol("=", List(sort, sort))
    def unapply(s: PredicateSymbol): Option[Sort] = s match {
      case PredicateSymbol("=", List(s1, s2)) if s1 == s2 => Some(s1)
      case _ => None
    }
  }
  object Equals {
    def apply(t1: Term, t2: Term): PredicateApplication = PredicateApplication(EqualsSymbol(t1.sort), List(t1, t2))
    def unapply(pApply: PredicateApplication): Option[(Term, Term)] = pApply match {
      case PredicateApplication(EqualsSymbol(_), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object TrueSymbol {
    def apply() = PredicateSymbol("true", List())
    def unapply(symbol: PredicateSymbol): Boolean = symbol match {
      case PredicateSymbol("true", List()) => true 
      case _ => false
    }
  }
  object True {
    def apply() = PredicateApplication(TrueSymbol(), Nil)
    def unapply(appli: PredicateApplication): Boolean = appli match {
      case PredicateApplication(TrueSymbol(), Nil) => true
      case _ => false
    }
  }

  object FalseSymbol {
    def apply() = PredicateSymbol("false", List())
    def unapply(symbol: PredicateSymbol): Boolean = symbol match {
      case PredicateSymbol("false", List()) => true 
      case _ => false
    }
  }
  object False {
    def apply() = PredicateApplication(FalseSymbol(), Nil)
    def unapply(appli: PredicateApplication): Boolean = appli match {
      case PredicateApplication(FalseSymbol(), Nil) => true
      case _ => false
    }
  }

  object NotSymbol {
    def apply() = ConnectiveSymbol("not", 1)
    def unapply(symbol: ConnectiveSymbol): Boolean = symbol match {
      case ConnectiveSymbol("not", 1) => true
      case _ => false
    }
  }
  object Not {
    def apply(formula: Formula) = ConnectiveApplication(NotSymbol(), List(formula))
    def unapply(appli: ConnectiveApplication): Option[Formula] = appli match {
      case ConnectiveApplication(NotSymbol(), formula :: Nil) => Some(formula)
      case _ => None
    }
  }

  object AndSymbol {
    def apply(arity: Int) = ConnectiveSymbol("and", arity)
    def unapply(symbol: ConnectiveSymbol): Option[Int] = symbol match {
      case ConnectiveSymbol("and", n) => Some(n)
      case _ => None
    }
  }
  object And {
    def apply(formulas: List[Formula]) = ConnectiveApplication(AndSymbol(formulas.size), formulas)
    def unapply(appli: ConnectiveApplication): Option[List[Formula]] = appli match {
      case ConnectiveApplication(AndSymbol(_), formulas) => Some(formulas)
      case _ => None
    }
  }

  object OrSymbol {
    def apply(arity: Int) = ConnectiveSymbol("or", arity)
    def unapply(symbol: ConnectiveSymbol): Option[Int] = symbol match {
      case ConnectiveSymbol("or", n) => Some(n)
      case _ => None
    }
  }
  object Or {
    def apply(formulas: List[Formula]) = ConnectiveApplication(OrSymbol(formulas.size), formulas)
    def unapply(appli: ConnectiveApplication): Option[List[Formula]] = appli match {
      case ConnectiveApplication(OrSymbol(_), formulas) => Some(formulas)
      case _ => None
    }
  }

  object IffSymbol {
    def apply() = ConnectiveSymbol("iff", 2)
    def unapply(symbol: ConnectiveSymbol): Boolean = symbol match {
      case ConnectiveSymbol("iff", 2) => true
      case _ => false
    }
  }
  object Iff {
    def apply(f1: Formula, f2: Formula) = ConnectiveApplication(IffSymbol(), List(f1, f2))
    def unapply(appli: ConnectiveApplication): Option[(Formula, Formula)] = appli match {
      case ConnectiveApplication(IffSymbol(), List(f1, f2)) => Some((f1, f2))
      case _ => None
    }
  }

  object ImpliesSymbol {
    def apply() = ConnectiveSymbol("implies", 2)
    def unapply(symbol: ConnectiveSymbol): Boolean = symbol match {
      case ConnectiveSymbol("implies", 2) => true
      case _ => false
    }
  }
  object Implies {
    def apply(f1: Formula, f2: Formula) = ConnectiveApplication(ImpliesSymbol(), List(f1, f2))
    def unapply(appli: ConnectiveApplication): Option[(Formula, Formula)] = appli match {
      case ConnectiveApplication(ImpliesSymbol(), List(f1, f2)) => Some((f1, f2))
      case _ => None
    }
  }

  object IfThenElseSymbol {
    def apply() = ConnectiveSymbol("if_then_else", 3)
    def unapply(symbol: ConnectiveSymbol): Boolean = symbol match {
      case ConnectiveSymbol("if_then_else", 3) => true
      case _ => false
    }
  }
  object IfThenElse {
    def apply(f1: Formula, f2: Formula, f3: Formula) = ConnectiveApplication(IfThenElseSymbol(), List(f1, f2, f3))
    def unapply(appli: ConnectiveApplication): Option[(Formula, Formula, Formula)] = appli match {
      case ConnectiveApplication(IfThenElseSymbol(), List(f1, f2, f3)) => Some((f1, f2, f3))
      case _ => None
    }
  }

  object ForallSymbol {
    def apply() = QuantifierSymbol("forall")
    def unapply(symbol: QuantifierSymbol): Boolean = symbol match {
      case QuantifierSymbol("forall") => true
      case _ => false
    }
  }
  object Forall {
    def apply(v: Variable, f: Formula) = QuantifierApplication(ForallSymbol(), v, f)
    def unapply(appli: QuantifierApplication): Option[(Variable, Formula)] = appli match {
      case QuantifierApplication(ForallSymbol(), v, f) => Some((v, f))
      case _ => None
    }
  }

  object ExistsSymbol {
    def apply() = QuantifierSymbol("exists")
    def unapply(symbol: QuantifierSymbol): Boolean = symbol match {
      case QuantifierSymbol("exists") => true
      case _ => false
    }
  }
  object Exists {
    def apply(v: Variable, f: Formula) = QuantifierApplication(ExistsSymbol(), v, f)
    def unapply(appli: QuantifierApplication): Option[(Variable, Formula)] = appli match {
      case QuantifierApplication(ExistsSymbol(), v, f) => Some((v, f))
      case _ => None
    }
  }
}
