package regolic.asts.core

object Trees {

  final case class PredicateSymbol(name: String, argSorts: List[Sort])
  final case class FunctionSymbol(name: String, argSorts: List[Sort], returnSort: Sort)
  final case class ConnectiveSymbol(name: String, arity: Int)
  final case class QuantifierSymbol(name: String)
  final case class TermQuantifierSymbol(name: String, argSorts: List[Sort], returnSort: Sort)

  final case class Sort(name: String)

  sealed abstract class Term {
    val sort: Sort 

    override def toString = PrettyPrinter(this)
  }
  final case class FunctionApplication(fSymbol: FunctionSymbol, terms: List[Term]) extends Term {
    require(terms.size == fSymbol.argSorts.size)
    terms.zip(fSymbol.argSorts).foreach(c => c match {
      case (t,s) => require(t.sort == s)
    })

    val sort = fSymbol.returnSort

  }
  final case class Variable(name: String, sort: Sort) extends Term
  final case class ITE(condition: Formula, thenTerm: Term, elseTerm: Term) extends Term {
    require(thenTerm.sort == elseTerm.sort)
    val sort = thenTerm.sort
  }
  final case class TermQuantifierApplication(symbol: TermQuantifierSymbol, variable: Variable, terms: List[Term]) extends Term {
    require(terms.size == symbol.argSorts.size)
    terms.zip(symbol.argSorts).foreach(c => c match {
      case (t,s) => require(t.sort == s)
    })
    val sort = symbol.returnSort
  }

  sealed abstract class Formula {
    override def toString = PrettyPrinter(this)
  }

  final case class PredicateApplication(symbol: PredicateSymbol, terms: List[Term]) extends Formula 
  final case class ConnectiveApplication(symbol: ConnectiveSymbol, formulas: List[Formula]) extends Formula {
    require(symbol.arity >= 0 && symbol.arity == formulas.size)
  }
  final case class QuantifierApplication(symbol: QuantifierSymbol, variable: Variable, formula: Formula) extends Formula

  private var varCnt = -1

  def freshVariable(prefix: String, sort: Sort): Variable = { varCnt += 1; Variable(prefix + "_fresh_" + varCnt, sort) }
  def freshVariable(prefix: Variable): Variable = freshVariable(prefix.name, prefix.sort)

}
