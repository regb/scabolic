package regolic.asts.theories.array

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees.Constant
import regolic.asts.fol.{Trees => FolT}

object Trees {

  object ArraySort {
    def apply(from: Sort, to: Sort) = Sort("Array", List(from, to))
    def unapply(sort: Sort): Option[(Sort, Sort)] = sort match {
      case Sort("Array", List(from, to)) => Some((from, to))
      case _ => None
    }
  }

  object EqualsSymbol {
    def apply(from: Sort, to: Sort): PredicateSymbol = FolT.EqualsSymbol(ArraySort(from, to))
    def unapply(s: PredicateSymbol): Option[(Sort, Sort)] = s match {
      case FolT.EqualsSymbol(ArraySort(from, to)) => Some((from, to))
      case _ => None
    }
  }
  object Equals {
    def apply(t1: Term, t2: Term): PredicateApplication = {
      val ArraySort(from, to) = t1.sort
      PredicateApplication(EqualsSymbol(from, to), List(t1, t2))
    }
    def unapply(pApply: PredicateApplication): Option[(Term, Term)] = pApply match {
      case PredicateApplication(EqualsSymbol(_, _), List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  object SelectSymbol {
    def apply(from: Sort, to: Sort): FunctionSymbol = FunctionSymbol("select", List(ArraySort(from, to), from), to)
    def unapply(s: FunctionSymbol): Option[(Sort, Sort)] = s match {
      case FunctionSymbol("select", List(ArraySort(from, to), from2), to2) if from == from2 && to == to2 => Some((from, to))
      case _ => None
    }
  }
  object Select {
    def apply(a: Term, i: Term) = {
      val ArraySort(from, to) = a.sort
      FunctionApplication(SelectSymbol(from, to), List(a, i))
    }
    def unapply(appli: FunctionApplication): Option[(Term, Term)] = appli match {
      case FunctionApplication(SelectSymbol(_, _), List(a, i)) => Some((a, i))
      case _ => None
    }
  }

  object StoreSymbol {
    def apply(from: Sort, to: Sort): FunctionSymbol = FunctionSymbol("store", List(ArraySort(from, to), from, to), ArraySort(from, to))
    def unapply(s: FunctionSymbol): Option[(Sort, Sort)] = s match {
      case FunctionSymbol("store", List(ArraySort(from, to), from2, to2), to3) if to == to2 && to2 == to3 && from == from2 => Some((from, to))
      case _ => None
    }
  }
  object Store {
    def apply(a: Term, i: Term, v: Term) = FunctionApplication(StoreSymbol(i.sort, v.sort), List(a, i, v))
    def unapply(appli: FunctionApplication): Option[(Term, Term, Term)] = appli match {
      case FunctionApplication(StoreSymbol(_, _), List(a, i, v)) => Some((a, i, v))
      case _ => None
    }
  }

}
