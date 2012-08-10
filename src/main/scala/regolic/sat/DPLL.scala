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

      for(clause <- adjacencyLists(id)) {
        val wasSat = clause.isSat
        //println("set in clause: " + clause)

        clause.lits.find(lit => { //assume only one occurence of each lit
          if(lit.id == id) {
            if(lit != this)
              require(lit.isUnassigned)
            lit.value = Some(b)

            if(lit.isUnsat)
              clause.nbFalse += 1
            else
              clause.nbTrue += 1

            if(clause.isUnit)
              unitClauses ::= clause
            else if(clause.isUnsat)
              status = Conflict
            else if(clause.isSat && !wasSat) {
              cnfFormula.incSat()
              if(cnfFormula.isSat)
                status = Satisfiable
            }
            true
          } else false
        })
        //println("end set in clause: " + clause)
      }
    }

    def unset() {
      require(isAssigned)
      val clauses = adjacencyLists(id)
      for(clause <- clauses) {
        for(lit <- clause.lits) {
          if(lit.id == id) {
            if(lit != this)
              require(lit.isAssigned)

            if(clause.isSat)
              cnfFormula.decSat()

            if(status == Conflict && clause.isUnsat)
              status = Unknown

            if(lit.isUnsat)
              clause.nbFalse -= 1
            else
              clause.nbTrue -= 1

            lit.value = None

            if(clause.isUnit)
              unitClauses ::= clause
            else if(clause.isUnsat)
              status = Conflict
            else if(clause.isSat) {
              cnfFormula.incSat()
              if(cnfFormula.isSat)
                status = Satisfiable
            }
          }
        }
      }
    }

    def isAssigned = value != None
    def isUnassigned = value == None

    def isSat = {
      require(isAssigned)
      !(value.get ^ polarity)
    }
    def isUnsat = {
      require(isAssigned)
      value.get ^ polarity
    }

    override def toString: String = (if(!polarity) "-" else "") + "v" + id
  }

  class Clause(val lits: List[Literal]) {

    val nbLits = lits.length
    var nbTrue = 0
    var nbFalse = 0

    def isSat = nbTrue > 0
    def isUnsat = nbFalse == nbLits
    def isUnit = nbFalse == nbLits - 1 && nbTrue == 0
    def isConflict = nbFalse == nbLits

    override def toString: String = lits.mkString(", ")

  }

  class CNFFormula(val clauses: List[Clause], val nbVar: Int) {
    //TODO: require nbVar is correct

    val nbClauses = clauses.size
    private var _nbSat = 0

    def isSat = _nbSat == nbClauses

    def incSat() {
      assert(_nbSat < nbClauses)
      _nbSat += 1
      //println("nbSat: " + _nbSat)
    }

    def decSat() {
      assert(_nbSat > 0)
      _nbSat -= 1
      //println("nbSat: " + _nbSat)
    }

    def nbSat = _nbSat

    override def toString: String = clauses.mkString("{\n", "\n", "\n}")
  }

  //if a var only appear with the same polarity then set it to be true
  //all unit clause are eliminated and the corresponding variables deleted
  //keep a map from original var id to new ones
  //must also ensure that in each clause at most one occurence of the same variable can occur
  private def preprocess(cnf: CNFFormula): (Status, CNFFormula, Array[Option[Boolean]], Array[Int]) = {
    var conflictDetected = false
    var forcedVars: Array[Option[Boolean]] = Array.fill(cnf.nbVar)(None) //list of variable that are forced to some value
    //force a var to a pol, record the information into the forcedVars array, may detect a conflict
    def force(id: Int, pol: Boolean) {
      //println("Forcing " + id + " to " + pol)
      forcedVars(id) match {
        case None => forcedVars(id) = Some(pol)
        case Some(p) if(p != pol) => conflictDetected = true
        case _ => //here it was already forced at the same polarity
      }
    }
    def isForced(id: Int): Boolean = forcedVars(id) != None

    var oldClauses: List[List[Literal]] = cnf.clauses.map(_.lits)
    var newClauses: List[List[Literal]] = Nil

    //first we eliminate duplicate in the same clause as well as clauses containing both polarity
    //of same variable. This is only needed once
    for(clause <- oldClauses) {
      val varOccurences: Array[Option[Boolean]] = Array.fill(cnf.nbVar)(None)
      var newLits: List[Literal] = Nil
      var ignoreClause = false
      for(lit <- clause) {
        varOccurences(lit.id) match {
          case None => 
            varOccurences(lit.id) = Some(lit.polarity)
            newLits ::= lit
          case Some(p) if(p != lit.polarity) => ignoreClause = true
          case _ => //ignore lit
        }
      }
      if(!ignoreClause)
        newClauses ::= newLits
    }


    oldClauses = newClauses
    newClauses = Nil
    var needRecheck = true
    while(needRecheck && !conflictDetected) {
      //println("loop")
      //println(forcedVars.mkString(", "))
      needRecheck = false //this flag is only set to true when a change really require to redo the counting and everything
      //println(oldClauses)

      //first we count all occurence in the current situation and the unit clauses
      val varsCounters: Array[(Int, Int)] = Array.fill(cnf.nbVar)((0, 0))
      for(clause <- oldClauses) {
        var nbLits = 0
        for(lit <- clause) {
          nbLits += 1
          val counters = varsCounters(lit.id)
          if(lit.polarity)
            varsCounters(lit.id) = (counters._1 + 1, counters._2)
          else
            varsCounters(lit.id) = (counters._1, counters._2 + 1)
        }
        if(nbLits == 1)
          force(clause.head.id, clause.head.polarity)
      }
      //println(varsCounters.mkString(", "))

      //here we detect the same polarity occurence and fill forcedVariables
      varsCounters.zipWithIndex.foreach(arg => {
        val ((posCount, negCount), id) = arg
        if(posCount == 0 && negCount == 0)
          forcedVars(id) = Some(forcedVars(id).getOrElse(true))
        else if(negCount == 0)
          force(id, true)
        else if(posCount == 0)
          force(id, false)
      })

      //finally we apply all forced variables
      for(clause <- oldClauses) {
        var newLits: List[Literal] = Nil
        var ignoreClause = false
        for(lit <- clause) {
          forcedVars(lit.id) match {
            case None => newLits ::= lit
            case Some(p) if(p == lit.polarity) => ignoreClause = true
            case _ => //just ignore the literal
          }
        }
        if(ignoreClause) {
          //println("ignore clause: " + clause)
          //the clause can be remove, we will need to recheck for global effects
          needRecheck = true
        } else {
          newLits match {
            case Nil => conflictDetected = true //each literal of the clause were set to false
            case lit::Nil => //we identified a new unit clause, we need to redo the loop
              needRecheck = true
              newClauses ::= newLits
            case _ => newClauses ::= newLits
          }
        }
      }
      //println(newClauses)
      //println("conflict: " + conflictDetected)

      oldClauses = newClauses
      newClauses = Nil
    }

    if(conflictDetected)
      (Conflict, null, null, null)
    else if(oldClauses.isEmpty)
      (Satisfiable, null, forcedVars, null)
    else {
      val oldVarToNewVar: Array[Int] = new Array(cnf.nbVar)
      val newVarToOldVar = new scala.collection.mutable.ArrayBuffer[Int]
      var nbVarsRemoved = 0 //will be used as a shifter for the variable id
      (0 until cnf.nbVar).foreach(i => if(isForced(i)) nbVarsRemoved += 1 else {
        oldVarToNewVar(i) = i - nbVarsRemoved
        newVarToOldVar += i
      })
      val finalClauses: List[Clause] = oldClauses.map(clause => new Clause(clause.map(lit => new Literal(oldVarToNewVar(lit.id), lit.polarity))))
      val newNbVars = cnf.nbVar - nbVarsRemoved
      (Unknown, new CNFFormula(finalClauses, newNbVars), forcedVars, oldVarToNewVar)
    }
  }

  private sealed trait Status
  private case object Satisfiable extends Status
  private case object Conflict extends Status
  private case object Unknown extends Status

  def decide() {
    val i = model.indexWhere(_ == None)
    assert(i >= 0)
    val lit = literalRep(i)
    //println("decide: " + lit)

    lit.set(true)
    model(i) = Some(true)
    assignment ::= (i, true)
    visitedAtLevel ::= Nil //add a new layer for this level
  }

  def backtrack() {
    //println("backtracking")
    var b = false
    while(assignment != Nil && !b) {
      //println("visitedAtLevel: " + visitedAtLevel)
      val h = assignment.head
      val id = h._1
      val lit = literalRep(id)
      //println("Unset " + lit)
      lit.unset()
      model(id) = None

      var currentLevel = visitedAtLevel.head
      while(currentLevel != Nil) {
        val toUnset = literalRep(currentLevel.head)
        //println("Unset " + toUnset)
        toUnset.unset()
        model(currentLevel.head) = None
        currentLevel = currentLevel.tail
      }

      visitedAtLevel = visitedAtLevel.tail
      b = h._2
      assignment = assignment.tail

      if(b) {
        //println("set " + lit + " to false")
        lit.set(false)
        model(id) = Some(false)
        assignment ::= (id, false)
        visitedAtLevel ::= Nil
      }

    }
    if(assignment == Nil)
      status = Conflict
    //println("status: " + status)
  }

  private var visitedAtLevel: List[List[Int]] = List(Nil) //we explicitly represent layer -1 so that we can apply the deduce immediately
  private var assignment: List[(Int, Boolean)] = Nil
  private var model: Array[Option[Boolean]] = null
  private var adjacencyLists: Array[List[Clause]] = null
  private var literalRep: Array[Literal] = null
  private var cnfFormula: CNFFormula = null
  private var status: Status = Unknown

  def isSat(cnf: CNFFormula): Option[Array[Boolean]] = {
    //println("isSat called on: " + cnf)
    val (st, clauses, forcedVars, oldVarToNewVar) = preprocess(cnf)
    //println("After preprocessing: " + clauses)
    //println("Status: " + st)
    //println("focedVars: " + forcedVars.mkString(", "))
    //println("old->new: " + oldVarToNewVar)

    status = st
    if(status == Unknown) {
      cnfFormula = clauses
      adjacencyLists = Array.fill(clauses.nbVar)(Nil)
      literalRep = new Array(clauses.nbVar)
      model = Array.fill(cnfFormula.nbVar)(None)

      for(clause <- cnfFormula.clauses)
        for(lit <- clause.lits) {
          adjacencyLists(lit.id) = (clause :: adjacencyLists(lit.id))
          if(literalRep(lit.id) == null)
            literalRep(lit.id) = lit
        }


      while(status == Unknown) {
        //println("assignments: " + assignment)
        //println("unitClauses: " + unitClauses.mkString("[", "\n", "]"))
        //println("model: " + model.mkString(","))
        //println("visitedAtLevel: " + visitedAtLevel)

        while(unitClauses != Nil) {
          val unitClause = unitClauses.head
          if(unitClause.isUnit) { //could no longer be true since many variables are forwarded
            val forcedLit = unitClause.lits.find(_.isUnassigned).get
            forcedLit.set(forcedLit.polarity)
            model(forcedLit.id) = Some(forcedLit.polarity)

            val currentLevel = visitedAtLevel.head
            val newCurrentLevel = forcedLit.id :: currentLevel
            visitedAtLevel = newCurrentLevel :: visitedAtLevel.tail
          }
          unitClauses = unitClauses.tail
        }

        if(status == Unknown)
          decide()

        while(status == Conflict && assignment != Nil)
          backtrack()
      }
    }

    val res = status match {
      case Unknown => sys.error("unexpected")
      case Satisfiable => {
        val completeModel: Array[Boolean] = new Array(cnf.nbVar)
        (0 until cnf.nbVar).foreach(i => forcedVars(i) match {
          case None => //then this is a new var
            val newId = oldVarToNewVar(i)
            completeModel(i) = model(newId).getOrElse(true)
          case Some(v) =>
            completeModel(i) = v
        })
        Some(completeModel)
      }
      case Conflict => None
    }
    //println(res.map(m => m.mkString(", ")))
    res
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
