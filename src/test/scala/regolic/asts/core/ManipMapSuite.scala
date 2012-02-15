package regolic.asts.core

import org.scalatest.FunSuite
import Manip._
import Trees._

import TestValues._

class ManipMapSuite extends FunSuite {

  private val g2Symbol = FunctionSymbol("g2", List(sort, sort), sort)
  private val g2xc = FunctionApplication(g2Symbol, List(x, c))
  private val gxc = FunctionApplication(gSymbol, List(x, c))
  private val gyc = FunctionApplication(gSymbol, List(y, c))
  private val hycz = FunctionApplication(hSymbol, List(y, c, z))
  private val pSymbol = PredicateSymbol("p", List(sort))
  private val qSymbol = PredicateSymbol("q", List(sort, sort))
  private val pc = PredicateApplication(pSymbol, List(c))
  private val qxy = PredicateApplication(qSymbol, List(x, y))
  private val simpleITE = ITE(qxy, gxc, fx)
  private val fgf = FunctionApplication(fSymbol, List(FunctionApplication(gSymbol, List(x, FunctionApplication(fSymbol, List(c))))))
  private val aSymbol = ConnectiveSymbol("a", 2)
  private val bSymbol = ConnectiveSymbol("b", 3)
  private val apq = ConnectiveApplication(aSymbol, List(pc, qxy))
  private val bppq = ConnectiveApplication(bSymbol, List(pc, pc, qxy))
  private val complexFun = FunctionApplication(hSymbol, List(fgf, FunctionApplication(gSymbol, List(fgf, gxc)), c))
  private val complexITE = ITE(bppq, fgf, complexFun)
  private val complexForm = ConnectiveApplication(bSymbol, List(bppq, apq, PredicateApplication(pSymbol, List(complexITE, complexFun)))) 
  private val gxy = FunctionApplication(gSymbol, List(x, y))
  private val gyx = FunctionApplication(gSymbol, List(y, x))
  private val itepcgxcx = ITE(pc, gxc, x)
  private val itepcgycy = ITE(pc, gyc, y)
  private val gxgxy = FunctionApplication(gSymbol, List(x, gxy))
  private val qxc = PredicateApplication(qSymbol, List(x, c))
  private val pgxy = PredicateApplication(pSymbol, List(gxy))

  private def xtoy(t: Term): Term = t match {
    case v@Variable(_,_) if v == x => y
    case t@_ => t }
  private def ytox(t: Term): Term = t match {
    case v@Variable(_,_) if v == y => x
    case t@_ => t
  }
  private def flipxy(t: Term): Term = t match {
    case v@Variable(_,_) if v == y => x
    case v@Variable(_,_) if v == x => y
    case t@_ => t
  }
  private def xtoc(t: Term): Term = t match {
    case v@Variable(_,_) if v == x => c
    case t@_ => t
  }
  private def ytoc(t: Term): Term = t match {
    case v@Variable(_,_) if v == y => c
    case t@_ => t
  }
  private def ctogxy(t: Term): Term = t match {
    case fa@FunctionApplication(_,_) if fa == c => gxy
    case t@_ => t
  }
  private def pctoqxc(f: Formula): Formula = f match {
    case pa@PredicateApplication(_, _) if pa == pc => qxc
    case t@_ => t
  }

  test("mapPreorder: identity of trivial terms") {
    assert(x === mapPreorder(x, fid _ , tid _))
    assert(c === mapPreorder(c, fid _ , tid _))
    assert(hycz === mapPreorder(hycz, fid _ , tid _))
    assert(gyc !=  mapPreorder(gxc, fid _ , tid _))
    assert(g2xc !=  mapPreorder(gxc, fid _ , tid _))
  }
  test("mapPreorder: identity of trivial formulas") {
    assert(qxy === mapPreorder(qxy, fid _, tid _))
    assert(pc === mapPreorder(pc, fid _, tid _))
  }
  test("mapPostorder: identity of trivial terms") {
    assert(x === mapPostorder(x, fid _, tid _))
    assert(c === mapPostorder(c, fid _, tid _))
    assert(hycz === mapPostorder(hycz, fid _, tid _))
    assert(gyc != mapPostorder(s2t("gxc"), fid _, tid _))
    assert(g2xc != mapPostorder(gxc, fid _, tid _))
  }
  test("mapPostorder: identity of trivial formulas") {
    assert(qxy === mapPostorder(qxy, fid _, tid _))
    assert(pc === mapPostorder(pc, fid _, tid _))
  }

  test("mapPreorder: identity of terms") {
    assert(s2t("iqxygxcfx") === mapPreorder(s2t("iqxygxcfx"), fid _, tid _))
    assert(fgf === mapPreorder(fgf, fid _, tid _))
  }
  test("mapPreorder: identity of formulas") {
    assert(pc === mapPreorder(pc, fid _, tid _))
    assert(qxy === mapPreorder(qxy, fid _, tid _))
    assert(apq === mapPreorder(apq, fid _, tid _))
    assert(bppq === mapPreorder(bppq, fid _, tid _))
  }
  test("mapPostorder: identity of terms") {
    assert(simpleITE === mapPostorder(simpleITE, fid _, tid _))
    assert(fgf === mapPostorder(fgf, fid _, tid _))
  }
  test("mapPostorder: identity of formulas") {
    assert(pc === mapPostorder(pc, fid _, tid _))
    assert(qxy === mapPostorder(qxy, fid _, tid _))
    assert(apq === mapPostorder(apq, fid _, tid _))
    assert(bppq === mapPostorder(bppq, fid _, tid _))
  }
  
  test("mapPreorder: identity of complex terms") {
    assert(complexFun === mapPreorder(complexFun, fid _, tid _))
    assert(complexITE === mapPreorder(complexITE, fid _, tid _))
  }
  test("mapPreorder: identity of complex formulas") {
    assert(complexForm === mapPreorder(complexForm, fid _, tid _))
  }
  test("mapPostorder: identity of complex terms") {
    assert(complexFun === mapPostorder(complexFun, fid _, tid _))
    assert(complexITE === mapPostorder(complexITE, fid _, tid _))
  }
  test("mapPostorder: identity of complex formulas") {
    assert(complexForm === mapPostorder(complexForm, fid _, tid _))
  }

  test("mapPreorder: basic functions over terms") {
    assert(y === mapPreorder(x, fid _, xtoy _))
    assert(c === mapPreorder(x, fid _, xtoc _))
    assert(x != mapPreorder(x, fid _, xtoc _))
    assert(gyc === mapPreorder(gxc, fid _, xtoy _))
    assert(gxy === mapPreorder(gyx, fid _, flipxy _))
    assert(itepcgycy === mapPreorder(itepcgxcx, fid _, xtoy _))
    assert(gxgxy === mapPreorder(gxc, fid _, ctogxy _))
  }
  test("mapPreorder: basic functions over formulas") {
    assert(qxc === mapPreorder(qxy, fid _, ytoc _))
    assert(pgxy === mapPreorder(pc, fid _, ctogxy _))
    assert(qxc === mapPreorder(pc, pctoqxc _, tid _))
  }
  test("mapPostorder: basic functions over terms") {
    assert(y === mapPostorder(x, fid _, xtoy _))
    assert(c === mapPostorder(x, fid _, xtoc _))
    assert(x != mapPostorder(x, fid _, xtoc _))
    assert(gyc === mapPostorder(gxc, fid _, xtoy _))
    assert(gxy === mapPostorder(gyx, fid _, flipxy _))
    assert(itepcgycy === mapPostorder(itepcgxcx, fid _, xtoy _))
    assert(gxgxy === mapPostorder(gxc, fid _, ctogxy _))
  }
  test("mapPostorder: basic functions over formulas") {
    assert(qxc === mapPostorder(qxy, fid _, ytoc _))
    assert(pgxy === mapPostorder(pc, fid _, ctogxy _))
    assert(qxc === mapPostorder(pc, pctoqxc _, tid _))
  }

  test("mapPreorder: complex functions over terms") {
    var nbc = 0
    mapPreorder(complexITE, (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == c) {
          nbc += 1
          t
        } else t
        case _ => t})
    assert(nbc === 7)
    assert(nbc != 8)

    nbc = 0
    mapPreorder(complexFun, (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == c) {
          nbc += 1
          t
        } else t
        case _ => t})
    assert(nbc === 4)
  }
  test("mapPreorder: complex functions over formulas") {
    var nbc = 0
    mapPreorder(complexForm, (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == c) {
          nbc += 1
          t
        } else t
        case _ => t})

    assert(nbc === 14)
  }
  test("mapPostorder: complex functions over terms") {
    var nbc = 0
    mapPostorder(complexITE, (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == c) {
          nbc += 1
          t
        } else t
        case _ => t})
    assert(nbc === 7)
    assert(nbc != 8)

    nbc = 0
    mapPostorder(complexFun, (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == c) {
          nbc += 1
          t
        } else t
        case _ => t})
    assert(nbc === 4)
  }
  test("mapostorder: complex functions over formulas") {
    var nbc = 0
    mapPostorder(complexForm, (f: Formula) => f, (t: Term) => t match {
        case fa@FunctionApplication(_,_) => if(fa == c) {
          nbc += 1
          t
        } else t
        case _ => t})

    assert(nbc === 14)
  }

}
