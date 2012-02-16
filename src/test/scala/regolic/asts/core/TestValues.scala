package regolic.asts.core

import Trees._

object TestValues {

  val sort = Sort("sort")

  val nSymbol = FunctionSymbol("n", List(), sort)
  val mSymbol = FunctionSymbol("m", List(), sort)
  val fSymbol = FunctionSymbol("f", List(sort), sort)
  val FSymbol = FunctionSymbol("F", List(sort), sort)
  val gSymbol = FunctionSymbol("g", List(sort, sort), sort)
  val GSymbol = FunctionSymbol("G", List(sort, sort), sort)
  val hSymbol = FunctionSymbol("h", List(sort, sort, sort), sort)
  val HSymbol = FunctionSymbol("H", List(sort, sort, sort), sort)

  val pSymbol = PredicateSymbol("p", List(sort))
  val PSymbol = PredicateSymbol("P", List(sort))
  val qSymbol = PredicateSymbol("q", List(sort, sort))
  val QSymbol = PredicateSymbol("Q", List(sort, sort))

  val cSymbol = ConnectiveSymbol("c", 1)
  val CSymbol = ConnectiveSymbol("C", 1)
  val dSymbol = ConnectiveSymbol("d", 2)
  val DSymbol = ConnectiveSymbol("D", 2)

  val x = Variable("x", sort)
  val y = Variable("y", sort)
  val z = Variable("z", sort)

  val n = FunctionApplication(nSymbol, List())
  val m = FunctionApplication(mSymbol, List())

  private def parseTerm(cs: List[Char]): (Term, List[Char]) = cs match {
    case Nil => sys.error("while parsing, received Nil")
    case c::cs => c match {
      case 'x' => (x, cs)
      case 'y' => (y, cs)
      case 'z' => (z, cs)
      case 'n' => (n, cs)
      case 'm' => (m, cs)
      case 'f' => {
        val (t, rest) = parseTerm(cs)
        (FunctionApplication(fSymbol, List(t)), rest)
      }
      case 'F' => {
        val (t, rest) = parseTerm(cs)
        (FunctionApplication(FSymbol, List(t)), rest)
      }
      case 'g' => {
        val (t1, rest1) = parseTerm(cs)
        val (t2, rest2) = parseTerm(rest1)
        (FunctionApplication(gSymbol, List(t1, t2)), rest2)
      }
      case 'G' => {
        val (t1, rest1) = parseTerm(cs)
        val (t2, rest2) = parseTerm(rest1)
        (FunctionApplication(GSymbol, List(t1, t2)), rest2)
      }
      case 'h' => {
        val (t1, rest1) = parseTerm(cs)
        val (t2, rest2) = parseTerm(rest1)
        val (t3, rest3) = parseTerm(rest2)
        (FunctionApplication(hSymbol, List(t1, t2, t3)), rest3)
      }
      case 'H' => {
        val (t1, rest1) = parseTerm(cs)
        val (t2, rest2) = parseTerm(rest1)
        val (t3, rest3) = parseTerm(rest2)
        (FunctionApplication(HSymbol, List(t1, t2, t3)), rest3)
      }
      case 'i' => {
        val (f, rest1) = parseFormula(cs)
        val (t1, rest2) = parseTerm(rest1)
        val (t2, rest3) = parseTerm(rest2)
        (ITE(f, t1, t2), rest3)
      }
    }
  }
  def parseFormula(cs: List[Char]): (Formula, List[Char]) = cs match {
    case Nil => sys.error("while parsing, received Nil")
    case c::cs => c match {
      case 'p' => {
        val (t, rest) = parseTerm(cs)
        (PredicateApplication(pSymbol, List(t)), rest)
      }
      case 'q' => {
        val (t1, rest1) = parseTerm(cs)
        val (t2, rest2) = parseTerm(rest1)
        (PredicateApplication(qSymbol, List(t1, t2)), rest2)
      }
      case 'P' => {
        val (t, rest) = parseTerm(cs)
        (PredicateApplication(PSymbol, List(t)), rest)
      }
      case 'Q' => {
        val (t1, rest1) = parseTerm(cs)
        val (t2, rest2) = parseTerm(rest1)
        (PredicateApplication(QSymbol, List(t1, t2)), rest2)
      }
      case 'c' => {
        val (f, rest) = parseFormula(cs)
        (ConnectiveApplication(cSymbol, List(f)), rest)
      }
      case 'C' => {
        val (f, rest) = parseFormula(cs)
        (ConnectiveApplication(CSymbol, List(f)), rest)
      }
      case 'd' => {
        val (f1, rest1) = parseFormula(cs)
        val (f2, rest2) = parseFormula(rest1)
        (ConnectiveApplication(dSymbol, List(f1, f2)), rest2)
      }
      case 'D' => {
        val (f1, rest1) = parseFormula(cs)
        val (f2, rest2) = parseFormula(rest1)
        (ConnectiveApplication(DSymbol, List(f1, f2)), rest2)
      }
    }
  }

  def s2t(s: String): Term = {
    val (t, cs) = parseTerm(s.toList)
    if(cs != Nil) sys.error("parsing finished but " + cs + " left")
    else t
  }
  def s2f(s: String): Formula = {
    val (f, cs) = parseFormula(s.toList)
    if(cs != Nil) sys.error("parsing finished but " + cs + " left")
    else f
  }

  def fid(f: Formula): Formula = f
  def tid(t: Term): Term = t
}
