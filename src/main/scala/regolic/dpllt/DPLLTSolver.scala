package regolic.dpllt

import regolic.sat.Literal

import regolic.sat.Solver.Results._
import regolic.sat.FixedIntStack
import regolic.sat.FixedIntDoublePriorityQueue

import regolic.smt.TheorySolver

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.printers.SmtLib2

import collection.mutable.ListBuffer

import regolic.Settings
import regolic.StopWatch

/* The results, unknown means timeout */
object Results {
  sealed trait Result
  case class Satisfiable(model: Array[Boolean]) extends Result
  case object Unsatisfiable extends Result
  case object Unknown extends Result
}

object DPLLTSolverWrapper {
  private def solve(tSolver: regolic.smt.TheorySolver, phi: Formula): Results.Result = {

    val (clauses, encoding, nbTVars, nbPropVars) = PropositionalSkeleton(phi)

    // clauses contains literal polarity information, therefore we use it to
    // initialize the T-solver
    tSolver.initialize(clauses.flatMap(cl => {
        cl.withFilter(lit => (lit.getID < nbTVars)).map(lit => {
            if(lit.polarity)
              encoding.theory(lit.getID)
            else
              Not(encoding.theory(lit.getID))
          }
        )
      }
    ) ++ encoding.funEqs.toSet)
    //tSolver.initialize(encoding.funEqs.toSet)
    encoding.funEqs.foreach(tSolver.setTrue)

    val dplltSolver = new DPLLTSolver(nbPropVars + nbTVars, nbTVars, tSolver, encoding)
    clauses.foreach(dplltSolver.addClause)
    val retVal = dplltSolver.solve()

/*    
    println("\nACTUAL RUN DONE---NOW SANITY CHECK:\norig result: "+ retVal)

    val iSet = collection.mutable.Stack[Formula]()
    while(tSolver.iStack.nonEmpty) {
      iSet.push(tSolver.iStack.pop._2)
    }
    val ccSanity = new regolic.smt.qfeuf.CongruenceClosure

    ccSanity.initialize(clauses.flatMap(cl => {
        cl.withFilter(lit => (lit.getID < nbTVars)).map(lit => {
            if(lit.polarity)
              encoding.theory(lit.getID)
            else
              Not(encoding.theory(lit.getID))
          }
        )
      }
    ) ++ encoding.funEqs.toSet)
    //ccSanity.initialize(encoding.funEqs.toSet)
    //iSet.foreach(eq => assert(ccSanity.setTrue(eq) != None))
    iSet.foreach(ccSanity.setTrue)
*/

    retVal
  
  }
  
  def apply(tSolver: regolic.smt.TheorySolver, phi: Formula): Results.Result = {
    solve(tSolver, phi)
  }
}

object DPLLTSolver {

  /*
   * Linked list which provides efficient prepend as well as an iterator
   * that traverse elements efficiently and provide a remove method that
   * can be safely called while using the iterator, with O(1) removal of
   * the current element.
   *
   * Ideal data structure for the adjacency list of watched literals.
   *
   * It uses a pool of object and try to reuse as much as possible, the size
   * parameter declares the size of the pool. We need to collect statistics on the
   * typical size of these adjacency lists to tune the size parameter.
   */
  class ClauseList(size: Int) {

    private class ClauseNode() {
      var clause: Clause = null
      var next: ClauseNode = null
    }

    assert(size > 0)

    private var root: ClauseNode = null
    private var freeNodes: Array[ClauseNode] = new Array(size)
    private var freeNodesPointer = size - 1
    allocateNodes()

    def isEmpty = root == null

    def prepend(clause: Clause) {
      var tmp = root
      root = getFreeNode()
      root.clause = clause
      root.next = tmp
    }

    def remove(clause: Clause) {
      var node = root
      var prec: ClauseNode = null
      while(node != null && node.clause != clause) {
        prec = node
        node = node.next
      }
      if(node != null) {
        if(prec != null)
          prec.next = node.next
        if(node == root)
          root = node.next
        freeNode(node)
      }
    }

    def contains(clause: Clause): Boolean = {
      var node = root
      while(node != null && node.clause != clause) {
        node = node.next
      }
      node != null
    }

    override def toString(): String = {
      val it = iterator
      var res = "["
      while(it.hasNext()) {
        val cl = it.next()
        res += (cl + "\n")
      }
      res += "]"
      res
    }


    private def getFreeNode() = {
      if(freeNodesPointer < 0)
        allocateNodes()

      val res = freeNodes(freeNodesPointer)
      freeNodesPointer -= 1
      res
    }

    private def allocateNodes() {
      var i = size-1
      while(i >= 0) {
        freeNodes(i) = new ClauseNode()
        i -= 1
      }
      freeNodesPointer = size-1
    }

    private def freeNode(n: ClauseNode) {
      if(freeNodesPointer < size-1) {
        freeNodesPointer += 1
        n.next = null
        freeNodes(freeNodesPointer) = n
      }
    }

    class Iterator(start: ClauseNode) {

      private val fakeNode = getFreeNode() //special fake node for the start, so that hasNext can simply check for next
      fakeNode.next = start
      private var currentNode: ClauseNode = fakeNode
      private var predNode: ClauseNode = null

      def next(): Clause = {
        assert(hasNext())
        if(currentNode != fakeNode)
          predNode = currentNode
        currentNode = currentNode.next
        currentNode.clause
      }

      def hasNext(): Boolean = currentNode.next != null

      //remove will remove this element from the list without interfering with the iteration. It will not move forward the
      //current pointer element, but you should not call remove before starting the iterator nor at the end of twice on the
      //same element
      def remove() {
        val removedNode = currentNode
        fakeNode.next = removedNode.next
        currentNode = fakeNode
        if(removedNode == root) {
          root = removedNode.next
        } 
        if(predNode != null) {
          predNode.next = removedNode.next
        }
        freeNode(removedNode)
      }

    }

    def iterator: Iterator = new Iterator(root)

  }

  //ignore size 1 for watched literal, they are never kept in the db
  class Clause(val lits: Array[Int]) {
    var activity: Double = 0d
    var locked = false
    def this(listLits: Set[Literal]) = this(listLits.map{lit => 2*lit.getID + (1 - lit.polInt) }.toArray)
    
    val size = lits.size

    override def toString = lits.map(lit => (if(lit % 2 == 0) "" else "-") + (lit >> 1)).mkString("[", ", ", "]")
  }
  
}

class DPLLTSolver(nbVars: Int, nbTVars: Int, tSolver: TheorySolver, encoding: Encoding) {
  import DPLLTSolver._

  /*
    This is a SAT solver, and I am trying to make it efficient, so don't expect nice functional code
    using immutable data and everything, this will be pure procedural code with many gloabl variables.
  */

  //Enumeration for the different status of the algorithm
  private sealed trait Status
  private case object Satisfiable extends Status
  private case object Unsatisfiable extends Status
  private case object Conflict extends Status
  private case object Unknown extends Status
  private case object Timeout extends Status

  private[this] var nbConflicts = 0
  private[this] var nbDecisions = 0
  private[this] var nbPropagations = 0
  private[this] var nbLearntClauseTotal = 0
  private[this] var nbLearntLiteralTotal = 0
  private[this] var nbRemovedClauses = 0
  private[this] var nbRemovedLiteral = 0
  private[this] var nbRestarts = 0
  private[this] var nbSolveCalls = 0
         
  private[this] var decisionLevel = 0
  private[this] var trail: FixedIntStack = new FixedIntStack(nbVars) //store literals, but only one polarity at the same time, so nbVar size is enough
  private[this] var qHead = 0
  private[this] var reasons: Array[Clause] = new Array(nbVars)
  private[this] var levels: Array[Int] = Array.fill(nbVars)(-1)
  private[this] var model: Array[Int] = Array.fill(nbVars)(-1)
  private[this] var watched: Array[ClauseList] = Array.fill(2*nbVars)(new ClauseList(20))
  private[this] var incrementallyAddedClauses = new ListBuffer[Clause]
  private[this] var learntClauses: List[Clause] = Nil
  /*
   * seen can be used locally for algorithms to maintain variables that have been seen
   * They should maintain the invariant that seen is set to false everywhere.
   * History proved that locally initializing this array where needed was a killer for performance.
   */
  private[this] var seen: Array[Boolean] = Array.fill(nbVars)(false)
  private[this] var status: Status = Unknown
  private[this] var restartInterval = Settings.restartInterval
  private[this] var nextRestart = restartInterval
  private[this] val restartFactor = Settings.restartFactor

  private[this] var cnfFormula: CNFFormula = null
  private[this] var conflict: Clause = null
  private[this] var assumptions: Array[Int] = null

  private[this] val conflictAnalysisStopWatch = StopWatch("backtrack.conflictanalysis")
  private[this] val find1UIPStopWatch = StopWatch("backtrack.conflictanalysis.find1uip")
  private[this] val clauseMinimizationStopWatch = StopWatch("backtrack.conflictanalysis.clauseminimization")

  // 1 reason / var should be sufficient (instead of 1 reason / lit)
  private[this] val tReasons: Array[Formula] = new Array(nbTVars*2)

  def resetSolver() {
    nbConflicts = 0
    nbDecisions = 0
    nbPropagations = 0
    nbRemovedClauses = 0
    nbRemovedLiteral = 0
    nbRestarts = 0
    
    decisionLevel = 0
    trail = new FixedIntStack(nbVars) //store literals, but only one polarity at the same time, so nbVar size is enough
    qHead = 0
    reasons = new Array(nbVars)
    levels = Array.fill(nbVars)(-1)
    model = Array.fill(nbVars)(-1)
    watched = Array.fill(2*nbVars)(new ClauseList(20))
    
    seen = Array.fill(nbVars)(false)
    status = Unknown

    restartInterval = Settings.restartInterval
    nextRestart = restartInterval

    conflictAnalysisStopWatch.reset()
    find1UIPStopWatch.reset()
    clauseMinimizationStopWatch.reset()
  }

  def initClauses(clauses: List[Clause]) {
    var newClauses: List[Clause] = Nil
    clauses.foreach(cl => {
      val litsUnique = cl.lits.toSet
      if(litsUnique.size == 1) {
        val id = litsUnique.head >> 1
        if(model(id) == -1) {
          tEnqueueLiteral(litsUnique.head)
        }
        else if(model(id) == (litsUnique.head & 1))
          status = Unsatisfiable
      }
      else if(!litsUnique.exists(l1 => litsUnique.count(l2 => (l2 >> 1) == (l1 >> 1)) > 1)) {
        val newLits = new Clause(litsUnique.toArray)
        newClauses ::= newLits
      }
    })
    cnfFormula = new CNFFormula(newClauses, nbVars)
    for(clause <- newClauses)
      recordClause(clause)
  }


  def addClause(lits: Set[Literal]) = {
    incrementallyAddedClauses += new Clause(lits)
  }

  def solve(assumps: Array[Literal] = Array.empty[Literal]): Results.Result = {
    nbSolveCalls += 1

    if(nbSolveCalls > 1) {
      resetSolver()
      this.learntClauses :::= cnfFormula.learntClauses // save learnt clauses from previous run
    }
    initClauses(this.learntClauses ::: incrementallyAddedClauses.toList)

    assumptions = assumps.map((lit: Literal) => (lit.getID << 1) + lit.polInt ^ 1) // TODO correct literal to int conversion

    search()

  }

  private[this] def search(): Results.Result = {
    val topLevelStopWatch = StopWatch("toplevelloop")
    val deduceStopWatch = StopWatch("deduce")
    val decideStopWatch = StopWatch("decide")
    val backtrackStopWatch = StopWatch("backtrack")

    topLevelStopWatch.time {

      deduceStopWatch.time {
        deduce()
      }
      if(status == Conflict)
        status = Unsatisfiable

      val timeout: Option[Int] = Settings.timeout
      var elapsedTime: Long = 0 //in ms
      //assertWatchedInvariant
      //assertTrailInvariant
      //MAIN LOOP
      while(status == Unknown) {
        val startTime = System.currentTimeMillis
        //assertWatchedInvariant
        //assertTrailInvariant
        decideStopWatch.time {
          decide()
        }

        var cont = true
        while(cont) {
          //assertWatchedInvariant
          //assertTrailInvariant
          deduceStopWatch.time {
            deduce()
          }

          if(status == Conflict) {
            backtrackStopWatch.time {
              backtrack()
            }
          } else {
            cont = false
          }
        }

        val endTime = System.currentTimeMillis
        elapsedTime += (endTime - startTime)
        timeout.foreach(timeout => if(elapsedTime > 1000*timeout) status = Timeout)
      }
    }

    if(Settings.stats) {
      println("Conflicts: " + nbConflicts)
      println("Decisions: " + nbDecisions)
      println("Propagations: " + nbPropagations + " ( " + (nbPropagations/deduceStopWatch.seconds).toInt + " / sec)")
      println("Restarts: " + nbRestarts)
      println("Learned Literals: " + nbLearntLiteralTotal + " (" + nbLearntClauseTotal + " clauses) --- " + nbLearntLiteralTotal.toDouble/nbLearntClauseTotal.toDouble + " per clause")
      println("Removed Literals: " + nbRemovedLiteral + "(" + nbRemovedClauses + " clauses) --- " + nbRemovedLiteral.toDouble/nbRemovedClauses.toDouble + " per clause")
      println("Active Literals: " + (nbLearntLiteralTotal - nbRemovedLiteral) + "(" + (nbLearntClauseTotal - nbRemovedClauses) + ") --- " + (nbLearntLiteralTotal - nbRemovedLiteral).toDouble/(nbLearntClauseTotal-nbRemovedClauses).toDouble + " per clause")

      println("Time spend in:\n")
      println("  toplevelloop:         " + topLevelStopWatch.seconds + " sec")
      println("    decide:             " + decideStopWatch.seconds + " sec")
      println("    deduce:             " + deduceStopWatch.seconds + " sec")
      println("    backtrack:          " + backtrackStopWatch.seconds + " sec")
      println("      conflictanalysis: " + conflictAnalysisStopWatch.seconds + " sec")
      println("        clausemin:      " + clauseMinimizationStopWatch.seconds + " sec")
      println("        find1uip:       " + find1UIPStopWatch.seconds + " sec")
    }

    status match {
      case Unknown | Conflict => sys.error("unexpected")
      case Timeout => Results.Unknown
      case Unsatisfiable => Results.Unsatisfiable
      case Satisfiable => Results.Satisfiable(model.map(pol => pol == 1))
    }
  
  }

  private[this] def conflictAnalysis: Clause = {
    assert(conflict != null)
    //assert(seen.forall(b => !b))

    //the algorithm augment the cut closest to the conflict node successively by doing
    //a BFS while only searching through the nodes of the current decision level
    //it stops when only one node of the current decision level (the UIP) remain in the cut

    var learntClause: List[Int] = Nil
    var p: Int = -1 //literal
    var c = 0
    var trailIndex = trail.size
    var confl = conflict
    conflict = null

    //find 1-UIP
    find1UIPStopWatch.time {
      do {
        if(p != -1) {
          //if(p!=confl.lits(0))
            //println("p: "+ p +", confl: "+ confl)
          assert(p == (confl.lits(0)))
        }
        cnfFormula.incVSIDSClause(confl)

        val lits = confl.lits
        var i = if(p == -1) 0 else 1
        while(i < lits.size) {
          //assert(isUnsat(lits(i)))
          val id = lits(i) >> 1
          val lvl = levels(id)
          //println("seen("+ id +"): "+ seen(id))
          //println("lvl: "+ lvl +" decisionLevel: "+decisionLevel)
          if(!seen(id) && lvl > 0) {
            seen(id) = true
            //println("reasons("+id+"): "+ reasons(id))
            //if(lvl == decisionLevel || reasons(id) != null)
            if(lvl == decisionLevel)
              c += 1
            else {
              //println("adding: "+ lits(i) +", level: "+ lvl)
              //if(isTheoryLit(lits(i)))
                //println("  "+ (if((lits(i) & 1) == 0) encoding.theory(id) else Not(encoding.theory(id))))

              learntClause ::= lits(i)
            }
          }
          i += 1
        }

        //assert(learntClause.forall(lit => levels(lit >> 1) != decisionLevel))
        do {
          trailIndex -= 1
          p = trail(trailIndex)
        } while(!seen(p>>1))

        //println("p: "+ p +", c: "+ c +", level: "+ levels(p >> 1))
        //if(isTheoryLit(p))
          //println("  "+ (if((p & 1) == 0) encoding.theory(p>>1) else Not(encoding.theory(p>>1))))
              
        c = c - 1
        seen(p>>1) = false

        confl = reasons(p>>1)
        // confl is null when decision literal reached in trail

        //if(confl == null && c > 0) {
        if(false) {
          println("computing reason in conflictAnalysis")
        //if(false) {
          val expl = tSolver.explain(
            if((p & 1) == 0) encoding.theory(p>>1) else Not(encoding.theory(p>>1)), // l
            tReasons(p)//if((tReasons(p >> 1) & 1) == 0) encoding.theory(tReasons(p >> 1)>>1) else Not(encoding.theory(tReasons(p >> 1)>>1)) // lPrime
          )
          //println("expl: "+ expl.mkString("\n", "\n", "\n"))
          //println("encoding.id: "+ encoding.id.mkString("\n", "\n", "\n"))
          confl = new Clause(p +: (expl.map(tExplLit => tExplLit match {
              case Not(tExplVar) => encoding.id(tExplVar)*2
              case tExplVar => encoding.id(tExplVar)*2 + 1
            }).toArray)
          )
        // TODO set reason?
          //println("explanation of "+ (if((p & 1) == 0) encoding.theory(p>>1) else Not(encoding.theory(p>>1))) + ": "+ expl.mkString("\n", "\n", "\n"))
        }
        //if(confl != null)
          //println("reasons: "+ confl.lits.map(l => {
            //if((l >> 1) < nbTVars)
              //if((l & 1) == 0) encoding.theory(l >> 1) else Not(encoding.theory(l>>1))
            //else
              //if((l & 1) == 0) (l >> 1) else "-"+ (l>>1)
          //}).mkString("\n", "\n", "\n"))
       
        

        //if(confl != null) {
        //  assert(confl.lits(0) >> 1 == p)
        //  assert(isSat(confl.lits(0)))
        //  assert(confl.lits.tail.forall(lit => isUnsat(lit)))
        //}
      } while(c > 0)

    }
    assert(isAssigned(p))
    //p is 1-UIP
    //assert(learntClause.forall(lit => isUnsat(lit)))

    var toSetUnseen: List[Int] = learntClause

    clauseMinimizationStopWatch.time {
      def getAbstractLevel(id: Int) = 1 << (levels(id) & 31)
      //clause minimalization
      var marked: Set[Int] = learntClause.map(_ >> 1).toSet
      val levelsInClause: Set[Int] = marked.map(levels(_)) //we can optimize the search, if we see a node of a level not in the set, then for sure there will be a decision node of the same level

      def litRedundant(id: Int, abstractLevel: Int): Boolean = {
        var stack = List(id)
        var analyzeToclear: List[Int] = Nil
        var res = true
        while(!stack.isEmpty && res) {
          val reasonClause = reasons(stack.head)
          stack = stack.tail

          reasonClause.lits.foreach(l => if((l>>1) != id && res) {
            val id = l>>1

            if(!seen(id) && levels(id) > 0) {
              if(reasons(id) != null && (getAbstractLevel(id) & abstractLevel) != 0) {
                seen(id) = true
                stack ::= id
                analyzeToclear ::= id
                toSetUnseen ::= l
              } else {
                while(!analyzeToclear.isEmpty) {
                  seen(analyzeToclear.head) = false;
                  analyzeToclear = analyzeToclear.tail
                }
                res = false
              }
            }
          })
        }
        res
      }

      var absLevel: Int = 0
      learntClause.foreach(lit => absLevel |= getAbstractLevel(lit >> 1)) //maintain an abstract level
      learntClause = learntClause.filterNot(lit => {
        val reasonClause = reasons(lit >> 1) 
        reasonClause != null && litRedundant(lit >> 1, absLevel)
      })
    }

    toSetUnseen.foreach(lit => seen(lit>>1) = false)
    while(trailIndex < trail.size) {
      seen(trail(trailIndex) >> 1) = false
      trailIndex += 1
    }

    learntClause ::= (p ^ 1)  //don't forget to add p in the clause !
    new Clause(learntClause.toArray)
  }

  def litToVar(lit: Int): Int = lit >> 1
  // ...1 => false, ...0 => true
  def litPolarity(lit: Int): Boolean = (lit & 1) == 0
  def isAssigned(lit: Int): Boolean = model(lit >> 1) != -1
  def isUnassigned(lit: Int): Boolean = model(lit >> 1) == -1
  def isSat(lit: Int): Boolean = (model(lit >> 1) ^ (lit & 1)) == 1
  def isUnsat(lit: Int): Boolean = (model(lit >> 1) ^ (lit & 1)) == 0


  class CNFFormula(var originalClauses: List[Clause], val nbVar: Int) {
    require(originalClauses.forall(cl => cl.lits.forall(lit => lit >= 0 && lit < 2*nbVar)))
    require(originalClauses.forall(cl => cl.lits.size >= 2))
    require(originalClauses.forall(cl => cl.lits.forall(lit => cl.lits.count(l2 => (l2 >> 1) == (lit >> 1)) == 1)))

    private val nbProblemClauses: Int = originalClauses.size
    var nbClauses: Int = nbProblemClauses

    var learntClauses: List[Clause] = Nil
    var nbLearntClauses = 0

    private var maxLearnt: Int = nbClauses / 3
    private val maxLearntFactor: Double = 1.1

    def augmentMaxLearnt() {
      maxLearnt = (maxLearnt*maxLearntFactor + 1).toInt
    }

    /*
     * The decay mechanism is from MiniSAT, instead of periodically scaling down
     * each variable, it is equivalent to just augment the value of the increment, since
     * the scale down will not change any order and only the relative value are important.
     * We use doubles and we use the upper bound of 1e100 before scaling down everything, to
     * avoid reaching the limits of floating points.
     */

    private val VSIDS_DECAY: Double = 0.95
    private val VSIDS_CLAUSE_DECAY: Double = 0.999

    private var vsidsInc: Double = 1d
    private val vsidsDecay: Double = 1d/VSIDS_DECAY

    private var vsidsClauseInc: Double = 1d
    private val vsidsClauseDecay: Double = 1d/VSIDS_CLAUSE_DECAY

    val vsidsQueue = new FixedIntDoublePriorityQueue(nbVar)
    initVSIDS()

    def initVSIDS() {
      originalClauses.foreach(cl => cl.lits.foreach(lit => {
        vsidsQueue.incScore(lit >> 1, vsidsInc)
      }))
    }

    def incVSIDS(id: Int) {
      val newScore = vsidsQueue.incScore(id, vsidsInc)
      if(newScore > 1e100)
        rescaleVSIDS()
    }

    def rescaleVSIDS() {
      vsidsQueue.rescaleScores(1e-100)
      vsidsInc *= 1e-100
    }

    def decayVSIDS() {
      vsidsInc *= vsidsDecay
    }

    def incVSIDSClause(cl: Clause) {
      cl.activity = cl.activity + vsidsClauseInc
      if(cl.activity > 1e100)
        rescaleVSIDSClause()
    }
    def rescaleVSIDSClause() {
      for(cl <- learntClauses)
        cl.activity = cl.activity*1e-100
      vsidsClauseInc *= 1e-100
    }
    def decayVSIDSClause() {
      vsidsClauseInc *= vsidsClauseDecay
    }

    def learn(clause: Clause) {
      assert(clause.size > 1)

      learntClauses ::= clause
      nbClauses += 1
      nbLearntClauses += 1

      nbLearntClauseTotal += 1
      nbLearntLiteralTotal += clause.lits.size

      for(lit <- clause.lits)
        incVSIDS(lit >> 1)
      incVSIDSClause(clause)

      recordClause(clause)
      if(nbLearntClauses > maxLearnt)
        reduceLearntClauses()
    }

    def reduceLearntClauses() {
      val sortedLearntClauses = learntClauses.sortWith((cl1, cl2) => cl1.activity < cl2.activity)
      val (forgotenClauses, keptClauses) = sortedLearntClauses.splitAt(maxLearnt/2)
      learntClauses = keptClauses
      for(cl <- forgotenClauses) {
        if(!cl.locked) {
          unrecordClause(cl)
          nbClauses -= 1
          nbLearntClauses -= 1
          nbRemovedClauses += 1
          for(lit <- cl.lits)
            nbRemovedLiteral += 1
        } else {
          learntClauses ::= cl
        }
      }
    }

    override def toString: String = (learntClauses ++ originalClauses).mkString("{\n", "\n", "\n}")
  }

  private[this] def recordClause(cl: Clause) {
    watched(cl.lits(0)).prepend(cl)
    watched(cl.lits(1)).prepend(cl)
  }

  private[this] def unrecordClause(cl: Clause) {
    watched(cl.lits(0)).remove(cl)
    watched(cl.lits(1)).remove(cl)
  }


  private[this] def enqueueLiteral(lit: Int, from: Clause = null): Boolean = {
    val id = lit >> 1
    val pol = (lit & 1) ^ 1
    //assert(model(id) == -1) // TODO
    var retVal = false
    if(model(id) == -1) {
      model(id) = pol
      trail.push(lit)
      reasons(id) = from
      if(from != null) {
        //assert(from.lits.head == lit)
        //assert(from.lits.tail.forall(lit => isAssigned(lit)))
        //assert(from.lits.tail.forall(lit => isUnsat(lit)))
        //assert(from.lits.tail.forall(lit => trail.contains(lit>>1)))
        from.locked = true
      }
      levels(id) = decisionLevel
      retVal = true
    } else {
      // TODO seems like sometimes we enqueue a literal without having
      // backtracked it
      if(model(id) != pol)
        println("id is: "+ id)
      assert(model(id) == pol)
      //assert(false)
    }
    retVal
  }

  def isTheoryLit(lit: Int): Boolean = (lit >> 1) < nbTVars

  def tEnqueueLiteral(lit: Int, from: Clause = null) {
    //val tmpString = if((lit >> 1) < nbTVars)
      //if((lit & 1) == 0) encoding.theory(lit >> 1) else Not(encoding.theory(lit>>1))
    //else
      //if((lit & 1) == 0) (lit >> 1) else "-"+ (lit>>1)
    //println("ENQUEUING "+ tmpString +" @ "+ decisionLevel +" reason clause: "+ from)
          
    if((lit >> 1) < nbTVars) {
      val tLit = if((lit & 1) == 0) encoding.theory(lit >> 1) else Not(encoding.theory(lit >> 1))

      val (enqueuedLit, theoryLit) = if(from == null) {
        // decision
        tLit match {
          case Not(l) if tSolver.isTrue(Not(l)) => (lit, Not(l))
          case Not(l) if tSolver.isTrue(l) =>      (lit ^ 1, l)
          case l if tSolver.isTrue(Not(l)) =>      (lit ^ 1, Not(l))
          case l if tSolver.isTrue(l) =>           (lit, l)
        }
      } else {
        // bcp
        (lit, tLit)
      }
      enqueueLiteral(enqueuedLit, from)

      val solverResult = tSolver.setTrue(theoryLit)
      solverResult match {
        case Some(tConsequence) => {
          //println("t-consequence: "+ t.mkString("\n", "\n", "\n"))
          // TODO
          tConsequence.withFilter(_ != theoryLit).foreach(tConsLit => {
          //tConsequence.foreach(tConsLit => {
              tConsLit match {
                case Not(tConsVar) => {
                  println("enqueuing theory consequence: "+ tConsLit +" = "+ encoding.id(tConsVar))
                  enqueueLiteral(encoding.id(tConsVar)*2 + 1)
                  tReasons(encoding.id(tConsVar)*2 + 1) = theoryLit//enqueuedLit
                }
                case tConsVar => {
                  println("enqueuing theory consequence: "+ tConsLit +" = "+ encoding.id(tConsVar))
                  enqueueLiteral(encoding.id(tConsVar)*2)
                  tReasons(encoding.id(tConsVar)*2) = theoryLit//enqueuedLit
                }
              }
            }
          )
        } 
        case None => {
          status = Conflict

          val id = (enqueuedLit >> 1)
          val expl = tSolver.explain(
            tSolver.reason
          )
          //println("expl: "+ expl.mkString("\n", "\n", "\n"))
          //println("encoding.id: "+ encoding.id.mkString("\n", "\n", "\n"))
          var tmp = expl.map(tExplLit => tExplLit match {
            case Not(tExplVar) => encoding.id(tExplVar)*2
            case tExplVar => encoding.id(tExplVar)*2 + 1
          })
          tmp -= (enqueuedLit ^ 1)
          //.toList
          //.sortWith((x, y) => levels(x >> 1) > levels(y >> 1)) //reverse sorting if no foldLeft
          //.filter(x => {println("level: "+ levels(x>>1)); true})
          /*
          .foldLeft(List.empty[Int]){
            case (xs, y) if levels(y>>1) == decisionLevel => xs
            case (Nil, y) => y :: Nil
            case (x :: xs, y) => {
              if(levels(x >> 1) == levels(y >> 1))
                y :: xs
              else
                y :: x :: xs
            }
          }
          */

          conflict = new Clause(
            enqueuedLit +: tmp.toArray
          )
          reasons(enqueuedLit >> 1) = conflict
          
          //println("Conflict 1: "+ conflict.lits.map(l => {
            //if((l >> 1) < nbTVars)
              //if((l & 1) == 0) encoding.theory(l >> 1) else Not(encoding.theory(l>>1))
            //else
              //if((l & 1) == 0) (l >> 1) else "-"+ (l>>1)
          //}).mkString("\n", "\n", "\n"))
              
        }
      }
    } else {
      // propositional literal
      enqueueLiteral(lit, from)
    }
  }

  private[this] def decide() {
    //println("in decide")
    if(cnfFormula.vsidsQueue.isEmpty) {
      //println("1 status = SAT")
      status = Satisfiable
    } else {

      // handle assumptions
      var next = 0 // TODO next can be both a variable and a literal, which is confusing
      var foundNext = false
      while(decisionLevel < assumptions.size && !foundNext) {
        val p = assumptions(decisionLevel)
        if(isSat(p)) {
          // dummy decision level
          nbDecisions += 1
          decisionLevel += 1
        } else if(isUnsat(p)) {
          status = Unsatisfiable
          return
        } else {
          next = p
          foundNext = true // break
        }
      }
      
      if(foundNext) { // next is a literal already
        nbDecisions += 1
        decisionLevel += 1
        tEnqueueLiteral(next)
      }
      // regular decision
      else {
        next = cnfFormula.vsidsQueue.deleteMax
        while(model(next) != -1 && !cnfFormula.vsidsQueue.isEmpty)
          next = cnfFormula.vsidsQueue.deleteMax

        if(model(next) == -1) {
          nbDecisions += 1
          decisionLevel += 1
          tEnqueueLiteral(2*next | (nbDecisions & 1))
        } else{
          //println("2 status = SAT")
          //println("model:")
          //(0 until nbTVars).foreach{i => {
              //println(if(model(i) == 1) encoding.theory(i) else Not(encoding.theory(i)))
            //}
          //}
          status = Satisfiable
        }
      }
    }
    //println("end of decide")
  }

  private[this] def backtrack() {
    //println("in backtrack")
    if(decisionLevel == 0)
      status = Unsatisfiable
    else {
      nbConflicts += 1
      cnfFormula.decayVSIDS()
      cnfFormula.decayVSIDSClause()

      val learntClause = conflictAnalysisStopWatch.time { conflictAnalysis }
      //println("learntClause: "+ learntClause.lits.map(l => {
        //val litString = if((l >> 1) < nbTVars)
          //if((l & 1) == 0) encoding.theory(l >> 1) else Not(encoding.theory(l>>1))
        //else
          //if((l & 1) == 0) (l >> 1) else "-"+ (l>>1)
        //litString +" @ "+ levels(l>>1)
      //}).mkString("\n", "\n", "\n"))
      

      var lits = learntClause.lits
      //lits.sortWith((x,y) => levels(x >> 1) > levels(y >> 1))
      //var j = 1
      //while(j < lits.size && levels(lits(j) >> 1) == levels(lits(0) >> 1))
        //j+=1
      //val backtrackLevel = if(j == lits.size) 0 else levels(lits(j) >> 1)


      val backtrackLevel = if(lits.size == 1) 0 else {
        var m = levels(lits(1) >> 1)
        var i = 2
        while(i < lits.size) {
          val lvl = levels(lits(i) >> 1)
          if(lvl > m) {
            val tmp = lits(1)
            lits(1) = lits(i)
            lits(i) = tmp
            m = lvl
          }
          i += 1
        }
        m
      }
      //println("backtrackLevel: "+ backtrackLevel)

      status = Unknown
      if(nbConflicts == nextRestart) {
        if(Settings.stats) {
          println("restart after " + nbConflicts + " nb conflicts")
        }
        restartInterval = (restartInterval*restartFactor).toInt
        nextRestart = nbConflicts + restartInterval
        nbRestarts += 1
        backtrackTo(0)
        if(learntClause.size == 1) { //since we do not learn the clause 
          tEnqueueLiteral(learntClause.lits(0), learntClause)
        }
        cnfFormula.augmentMaxLearnt()
      } else {
        assert(decisionLevel > backtrackLevel)
        //println("no restart")
        backtrackTo(backtrackLevel)
        val lit = learntClause.lits(0)
        //assert(isUnassigned(lit))
        //assert(learntClause.lits.tail.forall(isUnsat))
        //if(learntClause.lits.size == 1)
          //tEnqueueLiteral(lit)
        //else
          tEnqueueLiteral(lit, learntClause) //only on non restart
        //if(status == Conflict) {
          //println("conflict after enqueuing negated literal")
          ////println("conflict: "+ conflict)
        //}
        //println("status after enqueuing backtracked literal in opposite polarity: "+ status)
        //note that if the unitClause is of size 1, there will be an auto-reset to backtrack level 0 so this is correct as well
      }
      if(learntClause.size > 1) //we only learn if it is not unit, if it is unit, then it is processed via the unitClauses and its consequences is added at level 0 which is never forgot
        cnfFormula.learn(learntClause)
    }
    //println("end of backtrack")
  }


  private[this] def backtrackTo(lvl: Int) {
    //println("backtracking to lvl: "+ lvl)
    var tDecisions = 0
    var lastTLit: Formula = null
    while(decisionLevel > lvl && !trail.isEmpty) {
      val head = trail.pop()
      decisionLevel = levels(head >> 1)
      if(decisionLevel > lvl) {
        undo(head)
        //println("undo id "+ (head >> 1))
        if(isTheoryLit(head)) {
          lastTLit = if((head & 1) == 0) encoding.theory(head >> 1) else Not(encoding.theory(head>>1))
          //println("  is tLit: "+ lastTLit)
          tDecisions += 1
        }
      } else
        trail.push(head)
    }
    //tSolver.backtrack(tDecisions)
    //println("lastTLit: "+ lastTLit)
    tSolver.backtrackTo(lastTLit)

    qHead = trail.size
    decisionLevel = lvl
  }

  private[this] def undo(lit: Int) {
    assert(isSat(lit))
    val id = lit>>1
    cnfFormula.vsidsQueue.insert(id)
    model(id) = -1
    levels(id) = -1
    val reasonClause = reasons(id)
    if(reasonClause != null) {
      reasonClause.locked = false
      reasons(id) = null
    }
  }

  private[this] def deduce() {
    //println("in deduce")

    while(qHead < trail.size && status != Conflict) {

      val forcedLit = trail(qHead)
      //negatedLit is the literals that are made false and need updating of watchers
      val negatedLit = forcedLit ^ 1
      assert(isAssigned(negatedLit))
      qHead += 1

      val ws = watched(negatedLit).iterator
      while(ws.hasNext() && status != Conflict) {
        val clause = ws.next()
        val lits = clause.lits

        assert(lits(0) == negatedLit || lits(1) == negatedLit)
        if(lits(1) != negatedLit) {
          val tmp = lits(1)
          lits(1) = negatedLit
          lits(0) = tmp
        }
        assert(lits(1) == negatedLit)

        if(isUnassigned(lits(0)) || isUnsat(lits(0))) {
          var i = 2
          var found = false
          while(!found && i < lits.size) {
            val l = lits(i)
            if(isUnassigned(l) || isSat(l))
              found = true
            else
              i += 1
          }
          if(found) {
            val tmp = lits(1)
            lits(1) = lits(i)
            lits(i) = tmp
            watched(lits(1)).prepend(clause)
            ws.remove()
          } else {
            if(isUnassigned(lits(0))) {
              nbPropagations += 1
              //println("UNASSIGNED, clause: "+ clause)
              tEnqueueLiteral(lits(0), clause)
            } else if(isUnsat(lits(0))) {
              println("Conflict 2: "+ clause)
              status = Conflict
              qHead == trail.size
              conflict = clause
              assert(conflict.lits.forall(lit => isUnsat(lit)))
            }
          }
        }
      }

    }

    //println("end of deduce: "+ status)
  }

  //some debugging assertions that can be introduced in the code to check for correctness

  //assert that there is no unit clauses in the database
  def assertNoUnits() {

    assert(qHead == trail.size) //we assume that all unit clauses queued have been processed

    for(clause <- cnfFormula.originalClauses ::: cnfFormula.learntClauses) {
      if(clause.lits.count(isUnassigned) == 1 && clause.lits.forall(lit => isUnassigned(lit) || isUnsat(lit))) {
        println("clause " + clause + " should be unit !")
        assert(false)
      }
    }

  }

  //assert the invariant of watched literal is correct
  def assertWatchedInvariant() {
    for(cl <- (cnfFormula.originalClauses ::: cnfFormula.learntClauses)) {
      if(!watched(cl.lits(0)).contains(cl)) {
        println("clause " + cl + " is not correctly watched on " + cl.lits(0))
        assert(false)
      }
      if(!watched(cl.lits(1)).contains(cl)) {
        println("clause " + cl + " is not correctly watched on " + cl.lits(1))
        assert(false)
      }
    }

    for(v <- 0 until cnfFormula.nbVar) {
      val posLit = 2*v + 0
      var it = watched(posLit).iterator
      while(it.hasNext()) {
        val cl = it.next()
        assert(cl.lits(0) == posLit || cl.lits(1) == posLit)
      }

      val negLit = 2*v + 1
      it = watched(negLit).iterator
      while(it.hasNext()) {
        val cl = it.next()
        assert(cl.lits(0) == negLit || cl.lits(1) == negLit)
      }

    }
  }

  def assertTrailInvariant() {
    val seen: Array[Boolean] = Array.fill(cnfFormula.nbVar)(false) // default value of false
    var lst: List[Int] = Nil
    var currentLevel = decisionLevel

    while(!trail.isEmpty) {
      val head = trail.pop()
      assert(isSat(head))
      if(levels(head>>1) == currentLevel - 1)
        currentLevel -= 1
      else {
       assert(levels(head>>1) == currentLevel)
      }
      lst ::= head
      
      if(reasons(head>>1) != null) {
        assert(isSat(reasons(head>>1).lits.head))
        assert(reasons(head>>1).lits.tail.forall(lit => isUnsat(lit)))
        assert(reasons(head>>1).lits.tail.forall(lit => trail.contains(lit ^ 1) ))
        assert(reasons(head>>1).lits.forall(lit => !seen(lit >> 1) ))
      }

      seen(head>>1) = true
    }
    assert(currentLevel == 1 || currentLevel == 0)

    lst.foreach(i => trail.push(i))

  }

}
