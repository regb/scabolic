package regolic.sat

/*
 * This implements a stack of int of finite size using an array.
 * This is intended to be used for the trail in the SAT solver.
 */
class FixedIntStack(size: Int) {
  private val stack: Array[Int] = new Array(size)
  private var topIndex: Int = -1

  def push(el: Int) {
    topIndex += 1
    stack(topIndex) = el
  }
  def pop(): Int = {
    val res = stack(topIndex)
    topIndex -= 1
    res
  }
  def top: Int = stack(topIndex)
  def isEmpty: Boolean = topIndex == -1
  def contains(el: Int): Boolean = {
    var i = topIndex
    while(i >= 0) {
      if(stack(i) == el)
        return true
      i -= 1
    }
    false
  }
}
