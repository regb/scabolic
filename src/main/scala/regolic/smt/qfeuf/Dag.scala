package regolic.smt.qfeuf

import regolic.asts.core.Trees._

class Dag(
    val term: Term,
    val args: List[Dag],
    var find: Dag,
    var ccpar: Set[Dag]
) {

  def findRepr(): Dag = if(find == this) this else find.findRepr()

  def union(d: Dag) {
    val n1 = this.findRepr()
    val n2 = d.findRepr()
    n1.find = n2.find
    n2.ccpar = n1.ccpar ++ n2.ccpar
    n1.ccpar = Set()
  }

  def ===(d: Dag) = this.findRepr() == d.findRepr()

  def parents(): Set[Dag] = this.findRepr().ccpar

  override def toString: String = {
    "DAG for node " + term + 
    "\n\tRepresentative:\n\t\t" + this.findRepr().term + 
    "\n\tParents:\n\t\t" + this.parents().map(d => d.term).mkString("\n\t\t")
  }

}
