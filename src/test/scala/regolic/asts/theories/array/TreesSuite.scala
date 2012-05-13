package regolic.asts.theories.array

import org.scalatest.FunSuite
import Trees._
import regolic.asts.core.Trees._

class TreesSuite extends FunSuite {

  val fromSort = Sort("From", List())
  val toSort = Sort("To", List())
  val arraySort = ArraySort(fromSort, toSort)

  val a1 = FunctionApplication(FunctionSymbol("a1", List(), arraySort), List())
  val a2 = FunctionApplication(FunctionSymbol("a2", List(), arraySort), List())

  val i1 = FunctionApplication(FunctionSymbol("i1", List(), fromSort), List())
  val i2 = FunctionApplication(FunctionSymbol("i2", List(), fromSort), List())

  val v1 = FunctionApplication(FunctionSymbol("v1", List(), toSort), List())
  val v2 = FunctionApplication(FunctionSymbol("v2", List(), toSort), List())


  test("Building and extracting trees") {
    val t1 = Select(Store(Store(a1, i1, v1), i2, v2), i1)
    val t2 = Store(Store(a1, i1, v1), i2, v2)
    println(t1)
    println(t2)

    t1 match {
      case Select(a, i) => {
        assert(a === Store(Store(a1, i1, v1), i2, v2), i1)
        assert(i === i1)
      }
      case _ => assert(false)
    }

    t2 match {
      case Store(a, i, v) => {
        assert(a === Store(a1, i1, v1))
        assert(i === i2)
        assert(v === v2)
      }
      case _ => assert(false)
    }

    t1 match {
      case Select(Store(Store(a, j1, s1), j2, s2), j3) => {
        assert(a === a1)
        assert(j1 === i1)
        assert(s1 === v1)
        assert(j2 === i2)
        assert(s2 === v2)
      }
      case _ => assert(false)
    }
  }

}
