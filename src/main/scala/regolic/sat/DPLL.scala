package regolic.sat

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._

import regolic.Settings

object DPLL extends Solver {

  private var nbConflicts = 0
  private var nbDecisions = 0
  private var nbLearnedLiteral = 0
  private var nbRestarts = 0

  class ImplicationGraph(nbVars: Int) {

    private abstract sealed class Node {
      var ins: List[Node] = Nil
      var outs: List[Node] = Nil
    }
    private case class DecisionNode(id: Int, polarity: Boolean, level: Int) extends Node
    private case class ConsequenceNode(id: Int, polarity: Boolean, level: Int) extends Node
    private case class ConflictNode(cl: List[Int]) extends Node

    private val nodes: Array[Node] = new Array(nbVars)
    private var lastConflict: ConflictNode = null
    
    private var decisionLevel = 0
    private var consequences: List[List[ConsequenceNode]] = List(Nil)
    private var decisions: List[DecisionNode] = Nil

    def insertDecision(id: Int, polarity: Boolean) {
      assert(nodes(id) == null)
      decisionLevel += 1
      val n = DecisionNode(id, polarity, decisionLevel)
      nodes(id) = n
      decisions ::= n
      consequences ::= Nil
    }

    def insertConsequence(reasonIds: List[Int], id: Int, polarity: Boolean) {
      assert(nodes(id) == null)
      val n = ConsequenceNode(id, polarity, decisionLevel)
      n.ins = reasonIds.map(id => { 
        assert(nodes(id) != null)
        val pn = nodes(id) 
        pn.outs ::= n
        pn
      })
      nodes(id) = n

      val currentLevel = consequences.head
      val newCurrentLevel = n :: currentLevel
      consequences = newCurrentLevel :: consequences.tail
    }

    def insertConflict(reasonIds: List[Int]) {
      assert(lastConflict == null)
      val n = ConflictNode(reasonIds)
      n.ins = reasonIds.map(id => { 
        assert(nodes(id) != null)
        val pn: Node = nodes(id) 
        pn.outs ::= n
        pn
      })
      lastConflict = n
      n
    }

    def backtrackTo(lvl: Int) {
      assert(lastConflict != null)
      lastConflict.ins.foreach(incNode => incNode.outs = incNode.outs.filterNot(_ == lastConflict))
      lastConflict = null
      while(decisionLevel != lvl) {
        val decisionNode: DecisionNode = decisions.head
        assert(decisionNode.level == decisionLevel)
        val consequenceNodes: List[ConsequenceNode] = consequences.head
        consequenceNodes.foreach(n => assert(n.level == decisionLevel))
        decisions = decisions.tail
        consequences = consequences.tail
        decisionLevel -= 1

        unset(decisionNode.id)
        nodes(decisionNode.id) = null

        consequenceNodes.foreach(n => {
          val id = n.id
          unset(id)

          //remove the occurence of the node everywhere (not all of the inc node are removed with backtracking)
          //this is not optimal, maybe a more global approach to backtracking would be better
          n.ins.foreach(incNode => incNode.outs = incNode.outs.filterNot(_ == n))
          nodes(id) = null

        })

      }
    }

    private def findDominators(start: Node, to: Node): Set[Node] = {
      var D: Map[Node, Set[Node]] = Map()
      val N: Set[Node] = nodes.flatMap(n => if(n == null) List() else List(n)).toSet + to
      D += (start -> Set(start))
      for(n <- (N-start))
        D += (n -> N)

      var change = true
      while(change) {
        change = false
        for(n <- (N-start)) {
          val preds: Set[Node] = n.ins.toSet
          val newD = preds.foldLeft(N)((a, s) => a.intersect(D(s))) + n
          if(newD != D(n)) {
            change = true
            D += (n -> newD)
          }
        }
      }

      D(to) - to
    }


    def conflictAnalysis: (Clause, Int) = if(decisionLevel == 0) (null, -1) else {
      //println(toDotString)
      assert(lastConflict != null)
      //println("computing dominator")
      val dominators = findDominators(decisions.head, lastConflict)
      //println("dominators: " + dominators)

      val (learnedClause, levels) = findRoots(lastConflict, dominators).map{ 
        case DecisionNode(id, pol, lvl) => ((id, !pol), lvl) 
        case ConsequenceNode(id, pol, lvl) => ((id, !pol), lvl)
        case _ => sys.error("unexpected")
      }.unzip
      val clause = new Clause(learnedClause.map(p => {val lit = new Literal(p._1, p._2); lit.value = Some(!p._2); lit })) //not sure but I set the literal to its correct assignment so that it is coherent with the whole state
      //println("learned clause: " + clause)
      clause.nbFalse = clause.lits.size
      val backtrackLevel = if(levels.isEmpty) -1 else if(levels.tail.isEmpty) 0 else levels.sortWith((e1, e2) => e1 > e2).tail.head //TODO: inneficient search for the second to last
      (clause, backtrackLevel)

      //var c = 0
      //val seen: Array[Boolean] = Array.fill(nbVars)(false)
      //var learnedClause: List[(Int, Boolean)] = Nil
      //var backtrackLevel = 0
      //var toSee: List[Node] = Nil
      //do {
      //  lastConflict.ins.foreach(n => {
      //    toSee ::= n
      //    val (id, pol, lvl) = n match {
      //      case DecisionNode(id, pol, lvl) => (id, pol, lvl)
      //      case ConsequenceNode(id, pol, lvl) => (id, pol, lvl)
      //      case _ => assert(false)
      //    }
      //    seen(id) = true
      //    if(lvl == decisionLevel)
      //      c += 1
      //    else if(lvl > 0) {
      //      learnedClause ::= (id, !pol)
      //      backtrackLevel = backtrackLevel.max(level)
      //    }
      //  })
      //  
      //} while(c > 0)
    }

    private def findRoots(node: Node, additionalRoots: Set[Node] = Set()): List[Node] = node match {
      case d@DecisionNode(_, _, _) => List(d)
      case n if additionalRoots.contains(n) => List(n)
      case _ => node.ins.flatMap(n => findRoots(n, additionalRoots).distinct).distinct
    }

    def toDotString: String = {
      var res = "digraph {\n"

      res += nodes.map(n => if(n==null) "" else n match {
        case DecisionNode(id, pol, level) => id + " [label=\"" + (if(pol) "" else "-") + id + " @" + level + "\" color=blue];"
        case ConsequenceNode(id, pol, level) => id + " [label=\"" + (if(pol) "" else "-") + id + " @" + level + "\" color=green];"
        case ConflictNode(_) => "C"
      }).mkString("\n")
      res += "\n"

      def printNode(n: Node): String = n match {
        case DecisionNode(id, _, _) => id.toString
        case ConsequenceNode(id, _, _) => id.toString
        case ConflictNode(_) => "C"
      }
      
      res += nodes.map(n => if(n == null) "" else {
        n.outs.map(out => printNode(n) + " -> " + printNode(out) + ";").mkString("\n")
      }).mkString("\n")

      res += "\n}"
      res
    }

  }

  private sealed trait Status
  private case object Satisfiable extends Status
  private case object Unsatisfiable extends Status
  private case object Conflict extends Status
  private case object Unknown extends Status

  class Literal(val id: Int, val polarity: Boolean) {
    require(id >= 0)
    var value: Option[Boolean] = None
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

  class CNFFormula(var clauses: List[Clause], val nbVar: Int) {
    require(clauses.forall(cl => cl.lits.forall(lit => lit.id >= 0 && lit.id < nbVar))) //could also check that there is no empty id
    //require(only one occurence of each lit)
    //actually we should write an invariant function somewhere

    var nbClauses = clauses.size
    private var _nbSat = 0

    private var vsids: Array[Int] = Array.fill(2*nbVar)(0)
    def getVSIDS(id: Int, pol: Boolean): Int = vsids(2*id + (if(pol) 1 else 0))
    def incVSIDS(id: Int, pol: Boolean) {
      val index = 2*id + (if(pol) 1 else 0)
      vsids(index) = vsids(index) + 1
    }
    def decayVSIDS() {
      var i = 0
      val size = vsids.size
      while(i < size) {
        vsids(i) = vsids(i)/2
        i += 1
      }
    }
    //init the VSIDS array
    clauses.foreach(cl => cl.lits.foreach(lit => incVSIDS(lit.id, lit.polarity)))

    def isSat = _nbSat == nbClauses
    def incSat() {
      assert(_nbSat < nbClauses)
      _nbSat += 1
    }
    def decSat() {
      assert(_nbSat > 0)
      _nbSat -= 1
    }
    def nbSat = _nbSat
    def learn(clause: Clause) {
      clauses ::= clause
      nbClauses += 1
      if(clause.isSat)
        incSat()
      for(lit <- clause.lits) {
        adjacencyLists(lit.id) = (clause :: adjacencyLists(lit.id))
        incVSIDS(lit.id, lit.polarity)
      }
      nbLearnedLiteral += clause.lits.size
    }

    override def toString: String = clauses.mkString("{\n", "\n", "\n}")
  }

  def set(id: Int, b: Boolean) {
    model(id) = Some(b)

    for(clause <- adjacencyLists(id)) {
      val wasSat = clause.isSat
      clause.lits.find(lit => { //assume only one occurence of each lit, hence the find so we can stop after finding it
        if(lit.id == id) {
          require(lit.isUnassigned)
          lit.value = Some(b)

          if(lit.isUnsat)
            clause.nbFalse += 1
          else
            clause.nbTrue += 1

          if(clause.isUnit)
            unitClauses ::= clause
          else if(status != Conflict && clause.isUnsat) {
            assert(lit.polarity != b)
            implicationGraph.insertConflict(clause.lits.map(_.id))
            status = Conflict
          }
          else if(clause.isSat && !wasSat) {
            cnfFormula.incSat()
            if(cnfFormula.isSat)
              status = Satisfiable
          }
          true
        } else false
      })
    }
  }

  def unset(id: Int) {
    model(id) = None
    val clauses = adjacencyLists(id)
    for(clause <- clauses) {
      for(lit <- clause.lits) {
        if(lit.id == id) {
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

  def decide() {
    nbDecisions += 1

    var max: Option[Int] = None
    var lit: Option[(Int, Boolean)] = None
    var i = 0
    while(i < cnfFormula.nbVar) {
      if(model(i) == None) {
        val scorePos = cnfFormula.getVSIDS(i, true)
        val scoreNeg = cnfFormula.getVSIDS(i, false)
        max match {
          case None => {
            if(scorePos > scoreNeg) {
              max = Some(scorePos)
              lit = Some((i, true))
            } else {
              max = Some(scoreNeg)
              lit = Some((i, false))
            }
          } 
          case Some(maxScore) => {
            if(scorePos > maxScore && scorePos >= scoreNeg) {
              max = Some(scorePos)
              lit = Some((i, true))
            } else if(scoreNeg > maxScore && scoreNeg >= scorePos) {
              max = Some(scoreNeg)
              lit = Some((i, false))
            }
          }
        }
      }
      i += 1
    }
    assert(max != None)
    assert(lit != None)

    val fLit = lit.get
    //println("decide: " + fLit._1 + " with polarity " + fLit._2)
    implicationGraph.insertDecision(fLit._1, fLit._2)
    set(fLit._1, fLit._2)
  }

  def backtrack() {
    nbConflicts += 1
    if(nbConflicts % 20 == 0)
      cnfFormula.decayVSIDS()
    val (learnedClause, backtrackLevel) = implicationGraph.conflictAnalysis
    if(backtrackLevel == -1)
      status = Unsatisfiable
    else {
      cnfFormula.learn(learnedClause)
      if(nbConflicts % 200 == 0) {
        nbRestarts += 1
        implicationGraph.backtrackTo(0)
      } else
        implicationGraph.backtrackTo(backtrackLevel)
    }
  }

  def deduce() {
    while(unitClauses != Nil) {
      val unitClause = unitClauses.head
      unitClauses = unitClauses.tail
      if(unitClause.isUnit) { //could no longer be true since many variables are forwarded
        val forcedLit = unitClause.lits.find(_.isUnassigned).get
        //println("force: " + forcedLit)
        implicationGraph.insertConsequence(unitClause.lits.map(_.id).filterNot(_ == forcedLit.id), forcedLit.id, forcedLit.polarity)
        set(forcedLit.id, forcedLit.polarity)
      }
    }
  }

  private var unitClauses: List[Clause] = List()
  private var model: Array[Option[Boolean]] = null
  private var adjacencyLists: Array[List[Clause]] = null
  private var cnfFormula: CNFFormula = null
  private var status: Status = Unknown
  private var implicationGraph: ImplicationGraph = null

  def isSat(cnf: CNFFormula): Option[Array[Boolean]] = {
    //println("isSat called on: " + cnf)
    val (st, clauses, forcedVars, oldVarToNewVar) = preprocess(cnf)
    //println("After preprocessing: " + clauses)

    status = st
    if(status == Unknown) {
      //INITIALIZATION
      cnfFormula = clauses
      adjacencyLists = Array.fill(clauses.nbVar)(Nil)
      model = Array.fill(cnfFormula.nbVar)(None)
      implicationGraph = new ImplicationGraph(clauses.nbVar)
      for(clause <- cnfFormula.clauses)
        for(lit <- clause.lits)
          adjacencyLists(lit.id) = (clause :: adjacencyLists(lit.id))

      //MAIN LOOP
      while(status == Unknown) {
        //println("assignments: " + assignment)
        //println("unitClauses: " + unitClauses.mkString("[", "\n", "]"))
        //println("model: " + model.mkString(","))
        //println(cnfFormula.nbClauses)
        //println(implicationGraph.toDotString)

        decide()

        var cont = true
        while(cont) {
          deduce()

          if(status == Conflict)
            backtrack()
          else
            cont = false
        }
      }
    }

    val res = status match {
      case Unknown | Conflict => sys.error("unexpected")
      case Unsatisfiable => None
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
    }
    if(Settings.stats) {
      println("Conflicts: " + nbConflicts)
      println("Decisions: " + nbDecisions)
      println("Restarts: " + nbRestarts)
      println("Learned Literals: " + nbLearnedLiteral + " --- " + nbLearnedLiteral.toDouble/nbConflicts.toDouble + " per clause")
    }
    res
  }

  def isSat(clauses: List[Formula]): Option[Map[PredicateApplication, Boolean]] = {
    null
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
      (Unsatisfiable, null, null, null)
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

}
