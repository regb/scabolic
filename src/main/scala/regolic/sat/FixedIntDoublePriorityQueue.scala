package regolic.sat

/*
 * Priority queue of integer values that are sorted according
 * to a double value.
 * Scores are initialized to 0, while the elements are initialized
 * from 0 to length-1
 *
 * Elements are fixed, taking value between 0 and maxSize-1
 * When an element is removed, we remember its score, it is still
 * possible to augment its score, and when the element is added back, it
 * takes a position according to its current score.
 */
class FixedIntDoublePriorityQueue(val maxSize: Int) {

  private var _size = maxSize

  def size: Int = _size

  //uses 1-indexed arrays, this makes the parent/child relationship simpler and more efficient to compute
  private val heapScores: Array[Double] = new Array(1+size)
  private val heapElements: Array[Int] = new Array(1+size)

  //index is still 0-indexed
  private val index: Array[Int] = new Array(size)

  //and so are elements
  for(i <- 1 to size) {
    heapElements(i) = i-1
    index(i-1) = i
  }

  private def siftUp(pos: Int, score: Double) {
    val element = heapElements(pos)

    var i = pos
    while(i != 1 && heapScores(i/2) < score) {
      heapScores(i) = heapScores(i/2)
      val parentElement = heapElements(i/2)
      heapElements(i) = parentElement
      index(parentElement) = i
      i = i/2
    }

    heapScores(i) = score
    heapElements(i) = element
    index(element) = i
  }

  private def siftDown(pos: Int, score: Double) {
    val element = heapElements(pos)

    var i = pos
    var left = 2*i
    var right = left + 1
    var scoreLeft = heapScores(left)
    var scoreRight = heapScores(right)
    while(right <= size && (score < scoreLeft || score < scoreRight)) {
      if(scoreLeft > scoreRight) {
        heapScores(i) = scoreLeft
        val parentElement = heapElements(left)
        heapElements(i) = parentElement
        index(parentElement) = i
        i = left
      } else {
        heapScores(i) = scoreRight
        val parentElement = heapElements(right)
        heapElements(i) = parentElement
        index(parentElement) = i
        i = right
      }

      left = 2*i
      right = left + 1
      scoreLeft = heapScores(left)
      scoreRight = heapScores(right)
    }

    heapScores(i) = score
    heapElements(i) = element
    index(element) = i
  }

  /**
   * Increment the score
   * @require offset is positive
   */
  def incScore(el: Int, offset: Double) {
    require(offset >= 0)
    val pos = index(el)
    val newScore = heapScores(pos) + offset
    siftUp(pos, newScore)
  }

  def max: Int = heapElements(1)

  def deleteMax: Int = {
    val maxElement = heapElements(1)
    heapScores(0) = heapScores(1)
    heapElements(1) = heapElements(_size)
    val score = heapScores(_size)
    index(heapElements(1)) = 1
    heapElements(_size) = maxElement
    heapScores(_size) = heapScores(0)
    index(maxElement) = _size
    _size -= 1
    siftDown(1, score)
    maxElement
  }


  /**
   * verify that the invariant is true.
   * Meant to be called internally by the testing framework
   * Not efficient!
   */
  def invariant: Boolean = {
    var valid = true
    for(i <- 1 to size) {
      var left = i*2
      var right = i*2+1
      valid &&= (left > size || heapScores(left) <= heapScores(i))
      valid &&= (right > size || heapScores(right) <= heapScores(i))
      valid &&= (index(heapElements(i)) == i)
    }
    valid
  }

  /**
   * verify that the invariant is true.
   * Meant to be called internally for debugging purpose
   * Not efficient!
   */
  override def toString = {
    heapScores.tail.mkString("Scores: [", ", ", "]\n") +
    heapElements.tail.mkString("Elements: [", ", ", "]\n") +
    index.mkString("Index: [", ", ", "]\n")
  }

}
