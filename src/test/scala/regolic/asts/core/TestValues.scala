package regolic.asts.core

import Trees._

object TestValues {

  val sort = Sort("sort")

  val nSymbol = FunctionSymbol("n", List(), sort)
  val mSymbol = FunctionSymbol("m", List(), sort)
  val fSymbol = FunctionSymbol("f", List(sort), sort)
  val gSymbol = FunctionSymbol("g", List(sort, sort), sort)
  val hSymbol = FunctionSymbol("h", List(sort, sort, sort), sort)

  val pSymbol = PredicateSymbol("p", List(sort))
  val qSymbol = PredicateSymbol("q", List(sort, sort))

  val cSymbol = ConnectiveSymbol("c", 1)
  val dSymbol = ConnectiveSymbol("d", 2)

  val x = Variable("x", sort)
  val y = Variable("y", sort)
  val z = Variable("z", sort)

  val c = FunctionApplication(FunctionSymbol("c", List(), sort), List())
  val n = FunctionApplication(nSymbol, List())
  val m = FunctionApplication(mSymbol, List())

  val fx = FunctionApplication(fSymbol, List(x))
  val fy = FunctionApplication(fSymbol, List(y))
  val fz = FunctionApplication(fSymbol, List(z))
  val fn = FunctionApplication(fSymbol, List(n))
  val fm = FunctionApplication(fSymbol, List(m))
  
  val gxx = FunctionApplication(gSymbol, List(x, x))
  val gxy = FunctionApplication(gSymbol, List(x, y))
  val gxz = FunctionApplication(gSymbol, List(x, z))
  val gxn = FunctionApplication(gSymbol, List(x, n))
  val gxm = FunctionApplication(gSymbol, List(x, m))
  val gyx = FunctionApplication(gSymbol, List(y, x))
  val gyy = FunctionApplication(gSymbol, List(y, y))
  val gyz = FunctionApplication(gSymbol, List(y, z))
  val gyn = FunctionApplication(gSymbol, List(y, n))
  val gym = FunctionApplication(gSymbol, List(y, m))
  val gzx = FunctionApplication(gSymbol, List(z, x))
  val gzy = FunctionApplication(gSymbol, List(z, y))
  val gzz = FunctionApplication(gSymbol, List(z, z))
  val gzn = FunctionApplication(gSymbol, List(z, n))
  val gzm = FunctionApplication(gSymbol, List(z, m))
  val gnx = FunctionApplication(gSymbol, List(n, x))
  val gny = FunctionApplication(gSymbol, List(n, y))
  val gnz = FunctionApplication(gSymbol, List(n, z))
  val gnn = FunctionApplication(gSymbol, List(n, n))
  val gnm = FunctionApplication(gSymbol, List(n, m))
  val gmx = FunctionApplication(gSymbol, List(m, x))
  val gmy = FunctionApplication(gSymbol, List(m, y))
  val gmz = FunctionApplication(gSymbol, List(m, z))
  val gmn = FunctionApplication(gSymbol, List(m, n))
  val gmm = FunctionApplication(gSymbol, List(m, m))

  val hxxx = FunctionApplication(hSymbol, List(x, x, x))
  val hxyz = FunctionApplication(hSymbol, List(x, y, z))
  val hyyy = FunctionApplication(hSymbol, List(y, y, y))
  val hynz = FunctionApplication(hSymbol, List(y, n, z))
  val hzzz = FunctionApplication(hSymbol, List(z, z, z))
  val hnnn = FunctionApplication(hSymbol, List(n, n, n))
  val hmmm = FunctionApplication(hSymbol, List(m, m, m))

  val px = PredicateApplication(pSymbol, List(x))
  val py = PredicateApplication(pSymbol, List(y))
  val pz = PredicateApplication(pSymbol, List(z))
  val pn = PredicateApplication(pSymbol, List(n))
  val pm = PredicateApplication(pSymbol, List(m))

  val qxx = PredicateApplication(qSymbol, List(x, x))
  val qxy = PredicateApplication(qSymbol, List(x, y))
  val qxz = PredicateApplication(qSymbol, List(x, z))
  val qxn = PredicateApplication(qSymbol, List(x, n))
  val qxm = PredicateApplication(qSymbol, List(x, m))
  val qyx = PredicateApplication(qSymbol, List(y, x))
  val qyy = PredicateApplication(qSymbol, List(y, y))
  val qyz = PredicateApplication(qSymbol, List(y, z))
  val qyn = PredicateApplication(qSymbol, List(y, n))
  val qym = PredicateApplication(qSymbol, List(y, m))
  val qzx = PredicateApplication(qSymbol, List(z, x))
  val qzy = PredicateApplication(qSymbol, List(z, y))
  val qzz = PredicateApplication(qSymbol, List(z, z))
  val qzn = PredicateApplication(qSymbol, List(z, n))
  val qzm = PredicateApplication(qSymbol, List(z, m))
  val qnx = PredicateApplication(qSymbol, List(n, x))
  val qny = PredicateApplication(qSymbol, List(n, y))
  val qnz = PredicateApplication(qSymbol, List(n, z))
  val qnn = PredicateApplication(qSymbol, List(n, n))
  val qnm = PredicateApplication(qSymbol, List(n, m))
  val qmx = PredicateApplication(qSymbol, List(m, x))
  val qmy = PredicateApplication(qSymbol, List(m, y))
  val qmz = PredicateApplication(qSymbol, List(m, z))
  val qmn = PredicateApplication(qSymbol, List(m, n))
  val qmm = PredicateApplication(qSymbol, List(m, m))

  private def parseTerm(cs: List[Char]): (Term, List[Char]) = cs match {
    case Nil => sys.error("while parsing, received Nil")
    case c::cs => c match {
      case 'x' => (x, cs)
      case 'y' => (y, cs)
      case 'z' => (z, cs)
      case 'n' => (n, cs)
      case 'm' => (m, cs)
      case 'c' => (this.c, cs) //not sure it's a good idea to "overload" the c of connectives
      case 'f' => {
        val (t, rest) = parseTerm(cs)
        (FunctionApplication(fSymbol, List(t)), rest)
      }
      case 'g' => {
        val (t1, rest1) = parseTerm(cs)
        val (t2, rest2) = parseTerm(rest1)
        (FunctionApplication(gSymbol, List(t1, t2)), rest2)
      }
      case 'h' => {
        val (t1, rest1) = parseTerm(cs)
        val (t2, rest2) = parseTerm(rest1)
        val (t3, rest3) = parseTerm(rest2)
        (FunctionApplication(hSymbol, List(t1, t2, t3)), rest3)
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
      case 'c' => {
        val (f, rest) = parseFormula(cs)
        (ConnectiveApplication(cSymbol, List(f)), rest)
      }
      case 'd' => {
        val (f1, rest1) = parseFormula(cs)
        val (f2, rest2) = parseFormula(rest1)
        (ConnectiveApplication(dSymbol, List(f1, f2)), rest2)
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
