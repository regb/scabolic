package regolic.sat

// Invariant: different literal types are stored in different id intervals

// actualType is necessary because Literal can't be inherited, due to Set
// invariance (when using Set[Set[Literal]] as CNF)
class Literal(private val id: Int, private var offset: Int, val polInt: Int, val actualType: LiteralTypes) {
  require(id >= 0)

  def this(id: Int, polarity: Boolean, actualType: LiteralTypes = PropLiteral) = this(id, 0, if(polarity) 1 else 0, actualType)

  def this(id: Int, actualType: LiteralTypes) = this(id, 0, 0, actualType)

  def polarity = polInt == 1

  lazy val pos = new Literal(this.id, this.offset, 1, this.actualType) // TODO this is polluting

  def neg = this

  // getId must be extended when there are more LiteralTypes
  def getID = id + offset

  def setOffset(offset: Int) {
    println("offset: "+ offset)
    this.offset = offset
  }

  override def toString: String = (if(!polarity) "-" else "") + "v" + getID

}

sealed trait LiteralTypes
case object TLiteral extends LiteralTypes
case object PropLiteral extends LiteralTypes

