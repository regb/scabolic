package regolic.helper

import regolic.sat.TLiteralID
import regolic.sat.PropLiteralID

import org.scalatest.FunSuite
import org.scalatest.BeforeAndAfter

class FunSuiteWithIDReset extends FunSuite with BeforeAndAfter{
  after {
    TLiteralID.reset
    PropLiteralID.reset
  }
}

