package regolic.sat

class Literal(val id: Int, val polInt: Int) {
  require(id >= 0)

  def this(id: Int, polarity: Boolean) = this(id, if(polarity) 1 else 0)
  def polarity = polInt == 1

  override def toString: String = (if(!polarity) "-" else "") + "v" + id
}

