package regolic.asts.core

import org.scalatest.FunSuite
import Manip._
import Trees._

import TestValues._

class ManipMapSuite extends FunSuite {

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
  private def xton(t: Term): Term = t match {
    case v@Variable(_,_) if v == x => n
    case t@_ => t
  }
  private def yton(t: Term): Term = t match {
    case v@Variable(_,_) if v == y => n
    case t@_ => t
  }
  private def xtognm(t: Term): Term = t match {
    case v@Variable(_, _) if v == x => s2t("gnm")
    case t@_ => t
  }
  private def pxtoqnm(f: Formula): Formula = f match {
    case pa@PredicateApplication(_, _) if pa == s2f("px") => s2f("qnm")
    case t@_ => t
  }
  private def fwrapper(t: Term): Term = FunctionApplication(fSymbol, List(t))
  private def cwrapper(f: Formula): Formula = ConnectiveApplication(cSymbol, List(f))

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
    assert(s2t("gxy") === mapPreorder(s2t("gyx"), fid _, flipxy _))
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
    assert(s2t("gxy") === mapPostorder(s2t("gyx"), fid _, flipxy _))
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

}
