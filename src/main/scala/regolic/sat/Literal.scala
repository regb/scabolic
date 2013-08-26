package regolic.sat

abstract class Literal(val id: Int, val polInt: Int) {
  require(id >= 0)

  def polarity = polInt == 1

  override def toString: String = (if(!polarity) "-" else "") + "v" + id

  def neg: Literal

  def pos: Literal

  def getID: Int
}

trait LiteralID {
  var counter = -1
  def next = {
    counter += 1
    counter
  }

  def count = counter + 1
}

// Maybe more classes like TLiteral are necessary in the future. This should be
// easily extendable. getId has to be properly implemented, and possibly changed
// for the existing classes, if the order should be changed.
object TLiteralID extends LiteralID

class TLiteral(id: Int, polInt: Int) extends Literal(id, polInt) {

  def this(id: Int, polarity: Boolean) = this(id, if(polarity) 1 else 0)

  def this(id: Int) = this(id, 0)

  lazy val pos = new TLiteral(this.id, 1)

  lazy val neg = this

  def getID = id
}

object PropLiteralID extends LiteralID

class PropLiteral(id: Int, polInt: Int) extends Literal(id, polInt) {

  def this(id: Int, polarity: Boolean) = this(id, if(polarity) 1 else 0)

  def this(id: Int) = this(id, 0)

  lazy val pos = new PropLiteral(this.id, 1)

  lazy val neg = this

  def getID = id + TLiteralID.count
}
