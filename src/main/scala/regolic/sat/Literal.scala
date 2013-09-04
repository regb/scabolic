package regolic.sat

// Invariant: different literal types are stored in different id intervals

// actualType is necessary because Literal can't be inherited, due to Set
// invariance (when using Set[Set[Literal]] as CNF)
class Literal(private val id: Int, val polInt: Int, val actualType: LiteralTypes) {
  require(id >= 0)

  def this(id: Int, polarity: Boolean, actualType: LiteralTypes = PropLiteral) = this(id, if(polarity) 1 else 0, actualType)

  def this(id: Int, actualType: LiteralTypes) = this(id, 0, actualType)

  def polarity = polInt == 1

  def pos = new Literal(this.id, 1, this.actualType)

  def neg = this

  // getId must be extended when there are more LiteralTypes
  def getID = id + (actualType match {
    case TLiteral => 0
    case PropLiteral => TLiteralID.count
  })

  override def toString: String = (if(!polarity) "-" else "") + "v" + id

}

trait LiteralID {
  private var counter = -1
  def next = {
    counter += 1
    counter
  }

  def count = counter + 1

  def reset = {
    counter = -1
  }
}

object TLiteralID extends LiteralID
object PropLiteralID extends LiteralID

sealed trait LiteralTypes
case object TLiteral extends LiteralTypes
case object PropLiteral extends LiteralTypes

