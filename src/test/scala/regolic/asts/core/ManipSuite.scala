package regolic.asts.core

import Trees._
import Manip._
import org.scalatest.FunSuite

class ManipSuite extends FunSuite {

  /*
   * Short hand definition to build trees for the tests
   * Search for 'TESTCASES' to find the beginning of the tests
   */
  val sort = Sort("sort", List())

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

  val aSymbol = QuantifierSymbol("a")
  val ASymbol = QuantifierSymbol("A")
  val bSymbol = QuantifierSymbol("b")
  val BSymbol = QuantifierSymbol("B")

  val x = Variable("x", sort)
  val y = Variable("y", sort)
  val z = Variable("z", sort)

  val n = FunctionApplication(nSymbol, List())
  val m = FunctionApplication(mSymbol, List())
  
  def f(t: Term): Term = FunctionApplication(fSymbol, List(t))
  def F(t: Term): Term = FunctionApplication(FSymbol, List(t))
  def g(t1: Term, t2: Term): Term = FunctionApplication(gSymbol, List(t1, t2))
  def G(t1: Term, t2: Term): Term = FunctionApplication(GSymbol, List(t1, t2))
  def h(t1: Term, t2: Term, t3: Term): Term = FunctionApplication(hSymbol, List(t1, t2, t3))
  def H(t1: Term, t2: Term, t3: Term): Term = FunctionApplication(HSymbol, List(t1, t2, t3))

  def p(t: Term): Formula = PredicateApplication(pSymbol, List(t))
  def P(t: Term): Formula = PredicateApplication(PSymbol, List(t))
  def q(t1: Term, t2: Term): Formula = PredicateApplication(qSymbol, List(t1, t2))
  def Q(t1: Term, t2: Term): Formula = PredicateApplication(QSymbol, List(t1, t2))

  def c(f: Formula): Formula = ConnectiveApplication(cSymbol, List(f))
  def C(f: Formula): Formula = ConnectiveApplication(CSymbol, List(f))
  def d(f1: Formula, f2: Formula): Formula = ConnectiveApplication(dSymbol, List(f1, f2))
  def D(f1: Formula, f2: Formula): Formula = ConnectiveApplication(DSymbol, List(f1, f2))

  def a(v: Variable, b: Formula): Formula = QuantifierApplication(aSymbol, v, b)
  def A(v: Variable, b: Formula): Formula = QuantifierApplication(ASymbol, v, b)
  def b(v: Variable, b: Formula): Formula = QuantifierApplication(bSymbol, v, b)
  def B(v: Variable, b: Formula): Formula = QuantifierApplication(BSymbol, v, b)

  def ite(c: Formula, t1: Term, t2: Term): Term = ITE(c, t1, t2)

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


  //basic predicates
  def fFalse(f: Formula) = false
  def tFalse(t: Term) = false
  def fTrue(f: Formula) = true
  def tTrue(t: Term) = true
  def isVar(t: Term) = t match {
    case Variable(_, _) => true
    case _ => false
  }
  def isConst(t: Term) = t match {
    case FunctionApplication(_, List()) => true
    case _ => false
  }
  def isx(t: Term) = t == x
  def isy(t: Term) = t == y
  def isn(t: Term) = t == n
  def isfn(t: Term) = t == f(n)

  //some useful mapping functions
  def fid(f: Formula): Formula = f
  def tid(t: Term): Term = t
  private def xtoy(t: Term): Term = t match {
    case v@Variable(_,_) if v == x => y
    case t@_ => t }
  private def ytox(t: Term): Term = t match {
    case v@Variable(_,_) if v == y => x
    case t@_ => t
  }
  private def swapxy(t: Term): Term = t match {
    case v@Variable(_,_) if v == y => x
    case v@Variable(_,_) if v == x => y
    case t@_ => t
  }
  private def xton(t: Term): Term = t match {
    case v@Variable(_,_) if v == x => n
    case t@_ => t
  }
  private def yton(t: Term): Term = t match {
    case v@Variable(_,_) if v == y => n
    case t@_ => t
  }
  private def xtognm(t: Term): Term = t match {
    case v@Variable(_, _) if v == x => g(n,m)
    case t@_ => t
  }
  private def pxtoqnm(f: Formula): Formula = f match {
    case pa@PredicateApplication(_, _) if pa == p(x) => q(n,m)
    case t@_ => t
  }

  private def fwrapper(t: Term): Term = FunctionApplication(fSymbol, List(t))
  private def cwrapper(f: Formula): Formula = ConnectiveApplication(cSymbol, List(f))
  def incifx(acc: Int, t: Term): Int = if(x == t) acc+1 else acc
  def fvoid[A](acc: A, f: Formula): A = acc
  def tvoid[A](acc: A, t: Term): A = acc


  /**************************************************************************
   *                            TESTCASES                                   *
   **************************************************************************/

  test("findAndMap: identity of trivial terms") {
    assert((x, true) === findAndMap(x, fFalse _, isVar _, fid _, tid _))
    assert((n, true) === findAndMap(n, fFalse _, isConst _, fid _, tid _))
    assert((f(x), true) === findAndMap(f(x), fFalse _, isVar _, fid _, tid _))
    assert((h(y,n,z), true) === findAndMap(h(y,n,z), fFalse _, isVar _, fid _, tid _))
    assert((g(y,n), true) != findAndMap(g(x,n), fFalse _, isVar _, fid _, tid _))
    assert((G(x,m), true) != findAndMap(g(x,m), fFalse _, isConst _, fid _, tid _))
  }

  test("findAndMap: identity of trivial formulas") {
    assert((q(x,y), true) === findAndMap(q(x,y), fFalse _, isVar _, fid _, tid _))
    assert((p(n), true) === findAndMap(p(n), fFalse _, isConst _, fid _, tid _))
  }

  test("findAndMap: identity of composed terms") {
    assert((f(f(x)), true) === findAndMap(f(f(x)), fFalse _, isVar _, fid _, tid _))
    assert((h(f(x), g(n, y), m), true) === findAndMap(h(f(x), g(n, y), m), fFalse _, isVar _, fid _, tid _))
  }

  test("findAndMap: identity of composed formulas") {
    assert((c(p(f(f(x)))), true) === findAndMap(c(p(f(f(x)))), fFalse _, isVar _, fid _, tid _))
    assert((d(c(p(f(x))), q(g(n, y), m)), true) === findAndMap(d(c(p(f(x))), q(g(n, y), m)), fFalse _, isVar _, fid _, tid _))
  }

  test("findAndMap: finding terms") {
    assert((f(x), false) == findAndMap(f(x), fFalse _, isConst _, fid _, tid _))
    assert((h(y,n,z), false) === findAndMap(h(y,n,z), fFalse _, isx _, fid _, tid _))
    assert((h(f(x), g(n, y), m), true) === findAndMap(h(f(x), g(n, y), m), fFalse _, isn _, fid _, tid _))
    assert((h(f(x), g(f(n), y), m), true) === findAndMap(h(f(x), g(f(n), y), m), fFalse _, isfn _, fid _, tid _))
    assert((d(c(p(f(x))), q(g(n, y), m)), false) === findAndMap(d(c(p(f(x))), q(g(n, y), m)), fFalse _, isfn _, fid _, tid _))

    assert((h(y,n,z), false) === findAndMap(h(y,n,z), fFalse _, isx _, fid _, ytox _))
    assert((f(x), false) == findAndMap(f(x), fFalse _, isy _, fid _, xtoy _))
  }

  test("findAndMap: simple substitution") {
    assert((f(y), true) == findAndMap(f(x), fFalse _, isx _, fid _, xtoy _))
    assert((f(f(n)), true) === findAndMap(f(f(x)), fFalse _, isVar _, fid _, xton _))
    assert((h(f(x), g(n, x), m), true) === findAndMap(h(f(x), g(n, y), m), fFalse _, isy _, fid _, ytox _))
    assert((d(c(p(f(x))), q(g(n, n), m)), true) === findAndMap(d(c(p(f(x))), q(g(n, y), m)), fFalse _, isy _, fid _, yton _))
    assert((ite(q(f(x), g(x, n)), f(n), h(n,m,n)), true) === findAndMap(ite(q(f(x), g(x, y)), f(n), h(n,m,n)), fFalse _, isy _, fid _, yton _))
  }

  test("findAndMap: only applied once") {
    val f1 = ite(q(f(x), g(y, n)), f(n), h(n,x,y))
    val (f2, found1) = findAndMap(f1, fFalse _, isx _, fid _, xton _)
    assert(found1 === true)
    assert(f2 == ite(q(f(n), g(y, n)), f(n), h(n,x,y)) || f2 == ite(q(f(x), g(y, n)), f(n), h(n,n,y)))
    val (f3, found2) = findAndMap(f2, fFalse _, isx _, fid _, xton _)
    assert(found2 === true)
    assert(f3 === ite(q(f(n), g(y, n)), f(n), h(n,n,y)))
    val (f4, found3) = findAndMap(f3, fFalse _, isx _, fid _, xton _)
    assert(found3 === false)
    assert(f4 === ite(q(f(n), g(y, n)), f(n), h(n,n,y)))
  }

  test("mapPreorder: identity of trivial terms") {
    assert(x === mapPreorder(x, fid _, tid _))
    assert(n === mapPreorder(n, fid _, tid _))
    assert(s2t("fx") === mapPreorder(s2t("fx"), fid _, tid _))
    assert(s2t("hynz") === mapPreorder(s2t("hynz"), fid _, tid _))
    assert(s2t("gyn") != mapPreorder(s2t("gxn"), fid _, tid _))
    assert(s2t("Gxm") != mapPreorder(s2t("gxm"), fid _, tid _))
  }
  test("mapPreorder: identity of trivial formulas") {
    assert(s2f("qxy") === mapPreorder(s2f("qxy"), fid _, tid _))
    assert(s2f("pn") === mapPreorder(s2f("pn"), fid _, tid _))
  }
  test("mapPostorder: identity of trivial terms") {
    assert(x === mapPostorder(x, fid _, tid _))
    assert(n === mapPostorder(n, fid _, tid _))
    assert(s2t("hynz") === mapPostorder(s2t("hynz"), fid _, tid _))
    assert(s2t("gyn") != mapPostorder(s2t("gxn"), fid _, tid _))
    assert(s2t("Gxm") != mapPostorder(s2t("gxm"), fid _, tid _))
  }
  test("mapPostorder: identity of trivial formulas") {
    assert(s2f("qxy") === mapPostorder(s2f("qxy"), fid _, tid _))
    assert(s2f("pn") === mapPostorder(s2f("pn"), fid _, tid _))
  }

  test("mapPreorder: identity of complex terms") {
    assert(s2t("iqxygxnfy") === mapPreorder(s2t("iqxygxnfy"), fid _, tid _))
    assert(s2t("fgxm") === mapPreorder(s2t("fgxm"), fid _, tid _))
  }
  test("mapPreorder: identity of complex formulas") {
    assert(s2f("cpz") === mapPreorder(s2f("cpz"), fid _, tid _))
    assert(s2f("dpxqxy") === mapPreorder(s2f("dpxqxy"), fid _, tid _))
  }
  test("mapPostorder: identity of complex terms") {
    assert(s2t("iqxygxnfy") === mapPostorder(s2t("iqxygxnfy"), fid _, tid _))
    assert(s2t("fgxm") === mapPostorder(s2t("fgxm"), fid _, tid _))
  }
  test("mapPostorder: identity of complex formulas") {
    assert(s2f("cpz") === mapPostorder(s2f("cpz"), fid _, tid _))
    assert(s2f("dpxqxy") === mapPostorder(s2f("dpxqxy"), fid _, tid _))
  }
  
  test("mapPreorder: basic functions over terms") {
    assert(y === mapPreorder(x, fid _, xtoy _))
    assert(n === mapPreorder(x, fid _, xton _))
    assert(x != mapPreorder(x, fid _, xton _))
    assert(s2t("gyn") === mapPreorder(s2t("gxn"), fid _, xtoy _))
    assert(s2t("gxy") === mapPreorder(s2t("gyx"), fid _, swapxy _))
    assert(s2t("ipnhynyfy") === mapPreorder(s2t("ipnhxnxfx"), fid _, xtoy _))
    assert(s2t("gygnm") === mapPreorder(s2t("gyx"), fid _, xtognm _))
  }
  test("mapPreorder: basic functions over formulas") {
    assert(s2f("qxx") === mapPreorder(s2f("qxy"), fid _, ytox _))
    assert(s2f("pgnm") === mapPreorder(s2f("px"), fid _, xtognm _))
    assert(s2f("qnm") === mapPreorder(s2f("px"), pxtoqnm _, tid _))
  }
  test("mapPostorder: basic functions over terms") {
    assert(y === mapPostorder(x, fid _, xtoy _))
    assert(n === mapPostorder(x, fid _, xton _))
    assert(x != mapPostorder(x, fid _, xton _))
    assert(s2t("gyn") === mapPostorder(s2t("gxn"), fid _, xtoy _))
    assert(s2t("gxy") === mapPostorder(s2t("gyx"), fid _, swapxy _))
    assert(s2t("ipnhynyfy") === mapPostorder(s2t("ipnhxnxfx"), fid _, xtoy _))
    assert(s2t("gygnm") === mapPostorder(s2t("gyx"), fid _, xtognm _))
    assert(s2t("fgfxfy") === mapPostorder(s2t("gxy"), fid _, fwrapper _))
  }
  test("mapPostorder: basic functions over formulas") {
    assert(s2f("qxx") === mapPostorder(s2f("qxy"), fid _, ytox _))
    assert(s2f("pgnm") === mapPostorder(s2f("px"), fid _, xtognm _))
    assert(s2f("qnm") === mapPostorder(s2f("px"), pxtoqnm _, tid _))
    assert(s2f("cdcpxcpgnm") === mapPostorder(s2f("dpxpgnm"), cwrapper _, tid _))
  }

  test("mapPreorder: complex functions over terms") {
    var nbn = 0
    mapPreorder(s2t("iqfngmnhnnfgnmgfnhfmfngxm"), (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == n) {
          nbn += 1
          t
        } else t
        case _ => t})
    assert(nbn === 7)
  }
  test("mapPreorder: complex functions over formulas") {
    var nbn = 0
    mapPreorder(s2f("qiqfngmnhnnfgnmgfnhfmfngxmhnfngnm"), (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == n) {
          nbn += 1
          t
        } else t
        case _ => t})

    assert(nbn === 10)
  }
  test("mapPostorder: complex functions over terms") {
    var nbn = 0
    mapPostorder(s2t("iqfngmnhnnfgnmgfnhfmfngxm"), (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == n) {
          nbn += 1
          t
        } else t
        case _ => t})
    assert(nbn === 7)
  }
  test("mapPostorder: complex functions over formulas") {
    var nbn = 0
    mapPostorder(s2f("qiqfngmnhnnfgnmgfnhfmfngxmhnfngnm"), (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == n) {
          nbn += 1
          t
        } else t
        case _ => t})

    assert(nbn === 10)
  }

  test("mapPreorder: correct order") {

  }
  test("mapPostorder: correct order") {

  }

  test("foldPreorder: basic over terms") {
    assert(foldPreorder(x, 0)(fvoid, incifx) === 1)
    assert(foldPreorder(y, 0)(fvoid, incifx) === 0)
    assert(foldPreorder(n, 0)(fvoid, incifx) === 0)
    assert(foldPreorder(s2t("fx"), 0)(fvoid, incifx) === 1)
    assert(foldPreorder(s2t("fy"), 0)(fvoid, incifx) === 0)
    assert(foldPreorder(s2t("fn"), 0)(fvoid, incifx) === 0)
    assert(foldPreorder(s2t("gxn"), 0)(fvoid, incifx) === 1)
    assert(foldPreorder(s2t("gxx"), 0)(fvoid, incifx) === 2)
    assert(foldPreorder(s2t("gym"), 0)(fvoid, incifx) === 0)
  }
  test("foldPreorder: basic over formulas") {
    assert(foldPreorder(s2f("px"), 0)(fvoid, incifx) === 1)
    assert(foldPreorder(s2f("qxn"), 0)(fvoid, incifx) === 1)
    assert(foldPreorder(s2f("qnx"), 0)(fvoid, incifx) === 1)
    assert(foldPreorder(s2f("py"), 0)(fvoid, incifx) === 0)
    assert(foldPreorder(s2f("pn"), 0)(fvoid, incifx) === 0)
    assert(foldPreorder(s2f("qyy"), 0)(fvoid, incifx) === 0)
    assert(foldPreorder(s2f("qnm"), 0)(fvoid, incifx) === 0)
  }
  test("foldPostorder: basic over terms") {
    assert(foldPostorder(x, 0)(fvoid, incifx) === 1)
    assert(foldPostorder(y, 0)(fvoid, incifx) === 0)
    assert(foldPostorder(n, 0)(fvoid, incifx) === 0)
    assert(foldPostorder(s2t("fx"), 0)(fvoid, incifx) === 1)
    assert(foldPostorder(s2t("fy"), 0)(fvoid, incifx) === 0)
    assert(foldPostorder(s2t("fn"), 0)(fvoid, incifx) === 0)
    assert(foldPostorder(s2t("gxn"), 0)(fvoid, incifx) === 1)
    assert(foldPostorder(s2t("gxx"), 0)(fvoid, incifx) === 2)
    assert(foldPostorder(s2t("gym"), 0)(fvoid, incifx) === 0)
  }
  test("foldPostorder: basic over formulas") {
    assert(foldPostorder(s2f("px"), 0)(fvoid, incifx) === 1)
    assert(foldPostorder(s2f("qxn"), 0)(fvoid, incifx) === 1)
    assert(foldPostorder(s2f("qnx"), 0)(fvoid, incifx) === 1)
    assert(foldPostorder(s2f("py"), 0)(fvoid, incifx) === 0)
    assert(foldPostorder(s2f("pn"), 0)(fvoid, incifx) === 0)
    assert(foldPostorder(s2f("qyy"), 0)(fvoid, incifx) === 0)
    assert(foldPostorder(s2f("qnm"), 0)(fvoid, incifx) === 0)
  }

  test("foldPreorder: complex over terms") {
    assert(foldPreorder(s2t("ipxiqxynxhxxgnx"), 0)(fvoid, incifx) === 6)
  }
  test("foldPreorder: complex over formula") {
    assert(foldPreorder(s2t("ipxiqxynxhxxgnx"), 0)(fvoid, incifx) === 6)
  }
  test("foldPostorder: complex over terms") {
    assert(foldPostorder(s2t("ipxiqxynxhxxgnx"), 0)(fvoid, incifx) === 6)
  }
  test("foldPostorder: complex over formula") {
    assert(foldPostorder(s2t("ipxiqxynxhxxgnx"), 0)(fvoid, incifx) === 6)
  }


  test("alphaRenaming") {
  }
}


