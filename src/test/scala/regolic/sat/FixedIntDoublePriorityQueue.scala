package regolic.sat

import org.scalatest.FunSuite

class FixedIntDoublePriorityQueueSuite extends FunSuite {


  test("basic queue") {
    val q1 = new FixedIntDoublePriorityQueue(7)
    q1.incScore(3, 1.25)
    q1.incScore(2, 1.)
    q1.incScore(6, 2.)
    q1.incScore(3, 1.)
    q1.incScore(0, 0.5)
    q1.incScore(1, 1.5)
    q1.incScore(4, 0.7)
    assert(q1.invariant)
    assert(q1.max == 3)

    val q2 = new FixedIntDoublePriorityQueue(8)
    q2.incScore(7, 1.25)
    q2.incScore(0, 0.5)
    q2.incScore(2, 1.)
    q2.incScore(6, 2.)
    q2.incScore(3, 1.)
    q2.incScore(1, 1.5)
    q2.incScore(4, 0.7)
    q2.incScore(0, 1.7)
    q2.incScore(2, 1.6)
    q2.incScore(3, 1.7)
    assert(q2.invariant)
    assert(q2.max == 3)
  }

}
