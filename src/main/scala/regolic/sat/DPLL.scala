package regolic.sat

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._

object DPLL extends Solver {

  var unitClauses: List[Clause] = List()

  //a literal with variable id > 0 and polarity indicates whether this is a NOT literal
  //we assume that all propositional variable will have an id between 0 and nbVar, so we can use basic arrays to represent information associated with variable
  class Literal(val id: Int, val polarity: Boolean) {
    require(id >= 0)

    var value: Option[Boolean] = None

    def set(b: Boolean) {
      require(isUnassigned)
      value = Some(b)
      val clauses = adjacencyLists(id)
      for(clause <- clauses) {
        for(lit <- clause.lits) {
          if(lit.id == id) {
            require(lit.isUnassigned)
            lit.value = Some(b)

            if(lit.isUnsat)
              clause.nbFalse += 1
            else
              clause.nbTrue += 1

            if(clause.isUnit)
              unitClauses ::= clause
            if(clause.isSat)
              cnfFormula.nbSat += 1
          }
        }
      }
    }

    def unset() {
      require(isAssigned)
      value = None
      val clauses = adjacencyLists(id)
      for(clause <- clauses) {
        for(lit <- clause.lits) {
          if(lit.id == id) {
            require(lit.isAssigned)
            lit.value = None

            if(clause.isSat)
              cnfFormula.nbSat -= 1

            if(lit.isUnsat)
              clause.nbFalse -= 1
            else
              clause.nbTrue -= 1

            if(clause.isSat)
              cnfFormula.nbSat += 1
            if(clause.isUnit)
              unitClauses ::= clause
          }
        }
      }
    }

    def isAssigned = value != None
    def isUnassigned = value == None

    def isSat = {
      require(isUnassigned)
      !(value.get ^ polarity)
    }
    def isUnsat = {
      require(isUnassigned)
      value.get ^ polarity
    }
  }

  class Clause(val lits: List[Literal]) {

    val nbLits = lits.length
    var nbTrue = 0
    var nbFalse = 0

    def isSat = nbTrue > 0
    def isUnsat = nbFalse == nbLits
    def isUnit = nbFalse == nbLits - 1 && nbTrue == 0
    def isConflict = nbFalse == nbLits

  }

  class CNFFormula(val clauses: List[Clause], val nbVar: Int) {
    //TODO: require nbVar is correct

    val nbClauses = clauses.size
    var nbSat = 0
  }

  //if a var only appear with the same polarity then set it to be true
  def preprocess(cnf: CNFFormula): CNFFormula = {
    null
  }

  def deduce() {
    
  }

  private sealed trait Status
  private case object Satisfiable extends Status
  private case object Conflict extends Status
  private case object Unknown extends Status

  def decide() {
    val i = model.indexWhere(_ == None)
    assert(i >= 0)
    val lit = literalRep(i)

    lit.set(true)
    model(i) = Some(true)
    assignment ::= (i, true)
  }

  def backtrack() {
    var b = false
    while(assignment != Nil || b) {
      val h = assignment.head
      val id = h._1
      val lit = literalRep(id)
      lit.unset()
      model(id) = None
      b = h._2
      assignment = assignment.tail
      if(b) {
        lit.set(false)
        model(id) = Some(false)
        assignment ::= (id, false)
      }
    }
  }

  private var visitedAtLevel: List[List[Int]] = List()
  private var assignment: List[(Int, Boolean)] = List()
  private var model: Array[Option[Boolean]] = null
  private var adjacencyLists: Array[List[Clause]] = null
  private var literalRep: Array[Literal] = null
  private var cnfFormula: CNFFormula = null
  private var status: Status = Unknown

  def isSat(clauses: CNFFormula): Option[Array[Boolean]] = {
    cnfFormula = clauses
    adjacencyLists = new Array(clauses.nbVar)
    literalRep = new Array(clauses.nbVar)
    model = Array.fill(cnfFormula.nbVar)(None)

    for(clause <- cnfFormula.clauses)
      for(lit <- clause.lits) {
        adjacencyLists(lit.id) ::= clause
        if(literalRep(lit.id) == null)
          literalRep(lit.id) = lit
      }


    while(status == Unknown) {
      decide()
      while(status == Conflict && assignment != Nil)
        backtrack()
    }

    status match {
      case Unknown => sys.error("unexpected")
      case Satisfiable => Some(model.map(v => v.getOrElse(true)))
      case Conflict => None
    }

  }

  def isSat(clauses: List[Formula]): Option[Map[PredicateApplication, Boolean]] = {
    val simpleClauses = clauses.map(simplifyOr).filterNot(isTrue)
    val (clauses2, varsMapping) = bcp(simpleClauses)
    if(clauses2.forall(isTrue))
      Some(varsMapping)
    else if(clauses2.exists(isFalse))
      None
    else {
      val chosenVar = clauses2.flatMap(f => propVars(f)).head
      val left = isSat(clauses2.map(f => substitutePropVar(f, chosenVar, True())))
      val right = isSat(clauses2.map(f => substitutePropVar(f, chosenVar, False())))
      (left, right) match {
        case (Some(m1), _) => Some((m1 ++ varsMapping) + (chosenVar -> true))
        case (_, Some(m2)) => Some((m2 ++ varsMapping) + (chosenVar -> false))
        case (None, None) => None
      }
    }
  }

  private def simplifyOr(or: Formula): Formula = or match {
    case Or(Nil) => False()
    case Or(fs) if fs.exists(isTrue) => True()
    case Or(fs) if fs.exists(isFalse) => fs.filterNot(isFalse) match {
      case Nil => False()
      case fs2 => Or(fs2)
    }
    case _ => or
  }

  def bcp(clauses: List[Formula]): (List[Formula], Map[PredicateApplication, Boolean]) = {
    def unitClause(f: Formula) = f match {
      case Or(List(PropositionalVariable(_))) => true
      case Or(List(Not(PropositionalVariable(_)))) => true
      case PropositionalVariable(_) => true
      case Not(PropositionalVariable(_)) => true
      case _ => false
    }
    clauses.find(unitClause) match {
      case None => (clauses, Map())
      case Some(o) => {
        val p = o match {
          case Or(List(p)) => p
          case p => p
        }
        val (substClauses, mappedVar) = p match {
          case Not(p@PropositionalVariable(_)) => (clauses.map(f => substitutePropVar(f, p, False())), Map[PredicateApplication, Boolean](p -> false))
          case p@PropositionalVariable(_) => (clauses.map(f => substitutePropVar(f, p, True())), Map[PredicateApplication, Boolean](p -> true))
        }
        val simpleClauses = substClauses.map(f => simplifyOr(f))
        val res = simpleClauses.filterNot(isTrue)
        if(res.exists(isFalse))
          (res, mappedVar)
        else {
          val (finalClauses, finalMap) = bcp(res)
          (finalClauses, finalMap ++ mappedVar)
        }
      }
    }
  }

  private def isTrue(f: Formula): Boolean = f match {
    case True() => true
    case Not(False()) => true
    case _ => false
  }
  private def isFalse(f: Formula): Boolean = f match {
    case False() => true
    case Not(True()) => true
    case _ => false
  }

}
