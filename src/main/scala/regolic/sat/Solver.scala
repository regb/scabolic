package regolic.sat

import regolic.Settings
import regolic.StopWatch

object Solver {

  /*
    This is a SAT solver, and I am trying to make it efficient, so don't expect nice functional code
    using immutable data and everything, this will be pure procedural code with many gloabl variables.
  */

  // TODO: use the extends AnyVal with Variable (with a Int field) when the feature will be reliable and as efficient as using directly Int

  //Enumeration for the different status of the algorithm
  private sealed trait Status
  private case object Satisfiable extends Status
  private case object Unsatisfiable extends Status
  private case object Conflict extends Status
  private case object Unknown extends Status
  private case object Timeout extends Status

  /* The results, unknown means timeout */
  object Results {
    sealed trait Result
    case class Satisfiable(model: Array[Boolean]) extends Result
    case object Unsatisfiable extends Result
    case object Unknown extends Result
  }
  
  private[this] var nbConflicts = 0
  private[this] var nbDecisions = 0
  private[this] var nbPropagations = 0
  private[this] var nbLearntClauseTotal = 0
  private[this] var nbLearntLiteralTotal = 0
  private[this] var nbRemovedClauses = 0
  private[this] var nbRemovedLiteral = 0
  private[this] var nbRestarts = 0
         
  private[this] var decisionLevel = 0
  private[this] var trail: FixedIntStack = null
  private[this] var qHead = 0
  private[this] var reasons: Array[Clause] = null
  private[this] var levels: Array[Int] = null
  private[this] var conflict: Clause = null
  private[this] var model: Array[Int] = null
  private[this] var watched: Array[ClauseList] = null
  private[this] var cnfFormula: CNFFormula = null
  private[this] var status: Status = Unknown
  private[this] var restartInterval = 32
  private[this] var nextRestart = restartInterval
  private[this] val restartFactor = 1.1

  private[this] def getWatched(id: Int, pol: Int) = watched((id<<1) | pol) //2*id + pol, dunno if this is faster, does not really semm to make a difference

  def solve(clauses: List[Clause], nbVars: Int): Results.Result = {

    val preprocessStopWatch = StopWatch("preprocess")
    val deduceStopWatch = StopWatch("deduce")
    val decideStopWatch = StopWatch("decide")
    val backtrackStopWatch = StopWatch("backtrack")
    val topLevelStopWatch = StopWatch("toplevelloop")
    
    nbConflicts = 0
    nbDecisions = 0
    nbPropagations = 0
    nbLearntClauseTotal = 0
    nbLearntLiteralTotal = 0
    nbRemovedClauses = 0
    nbRemovedLiteral = 0
    nbRestarts = 0

    status = Unknown
    conflict = null
    trail = new FixedIntStack(nbVars)
    qHead = 0
    model = Array.fill(nbVars)(-1)
    watched = Array.fill(2*nbVars)(new ClauseList(20))
    restartInterval = 32
    nextRestart = restartInterval
    reasons = new Array(nbVars)
    levels = Array.fill(nbVars)(-1)
    decisionLevel = 0

    var newClauses: List[Clause] = Nil
    clauses.foreach(cl => {
      val litsUnique = cl.lits.map(lit => (lit.id, lit.polInt)).toSet
      if(litsUnique.size == 1) {
        val id = litsUnique.head._1
        val pol = litsUnique.head._2
        if(model(id) == -1)
          enqueueLiteral(id, litsUnique.head._2)
        else if(model(id) == 1 - pol)
          status = Unsatisfiable
      }
      else if(!litsUnique.exists(p => litsUnique.count(_._1 == p._1) > 1)) {
        val newLits = new Clause(litsUnique.map(p => new Literal(p._1, p._2)).toList)
        newClauses ::= newLits
      }
    })
    cnfFormula = new CNFFormula(newClauses, nbVars)
    for(clause <- newClauses)
      recordClause(clause)
    deduceStopWatch.time {
      deduce()
    }
    if(status == Conflict)
      status = Unsatisfiable

    val timeout: Option[Int] = Settings.timeout
    var elapsedTime: Long = 0 //in ms
    //assertNoUnits
    //assertWatchedInvariant
    //assertTrailInvariant
    //MAIN LOOP
    topLevelStopWatch.time {
      while(status == Unknown) {
        val startTime = System.currentTimeMillis
        //assertNoUnits
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
            //if(status != Unsatisfiable)
            //  assertNoUnits
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
      println("Propagations: " + nbPropagations + " ( " + nbPropagations/deduceStopWatch.seconds + " / sec)")
      println("Restarts: " + nbRestarts)
      println("Learned Literals: " + nbLearntLiteralTotal + " (" + nbLearntClauseTotal + " clauses) --- " + nbLearntLiteralTotal.toDouble/nbLearntClauseTotal.toDouble + " per clause")
      println("Removed Literals: " + nbRemovedLiteral + "(" + nbRemovedClauses + " clauses) --- " + nbRemovedLiteral.toDouble/nbRemovedClauses.toDouble + " per clause")
      println("Active Literals: " + (nbLearntLiteralTotal - nbRemovedLiteral) + "(" + (nbLearntClauseTotal - nbRemovedClauses) + ") --- " + (nbLearntLiteralTotal - nbRemovedLiteral).toDouble/(nbLearntClauseTotal-nbRemovedClauses).toDouble + " per clause")

      println("Time spend in:\n")
      println("  preprocess:           " + preprocessStopWatch.seconds + " sec")
      println("  toplevelloop:         " + topLevelStopWatch.seconds + " sec")
      println("    decide:             " + decideStopWatch.seconds + " sec")
      println("    deduce:             " + deduceStopWatch.seconds + " sec")
      println("    backtrack:          " + backtrackStopWatch.seconds + " sec")
    }

    status match {
      case Unknown | Conflict => sys.error("unexpected")
      case Timeout => Results.Unknown
      case Unsatisfiable => Results.Unsatisfiable
      case Satisfiable => Results.Satisfiable(model.map(pol => pol == 1))
    }
  }

  private[this] def conflictAnalysis: (Clause, Int) = if(decisionLevel == 0) (null, -1) else {
    assert(conflict != null)

    import scala.collection.mutable.Queue

    //the algorithm augment the cut closest to the conflict node successively by doing
    //a BFS while only searching through the nodes of the current decision level
    //it stops when only one node of the current decision level (the UIP) remain in the cut
    val seen: Array[Boolean] = Array.fill(cnfFormula.nbVar)(false) // default value of false
    var learntClause: List[Literal] = Nil
    var p: Int = -1
    var c = 0
    var confl = conflict
    conflict = null

    //find 1-UIP
    do {
      cnfFormula.incVSIDSClause(confl)

      confl.lits.foreach(lit => {
        val id = lit.id
        val lvl = levels(id)
        val pol = 1-model(id)
        if(!seen(id) && lvl > 0) {
          seen(id) = true
          if(lvl == decisionLevel)
            c += 1
          else
            learntClause ::= new Literal(id, pol)
        }
      })


      assert(learntClause.forall(lit => levels(lit.id) != decisionLevel))

      do { //we already start undo the trail here, probably not the cleanest approach but if we are careful this should work, and this is more efficient
        if(p != -1) //p must be undo, except for the last one which we will need its value in the end
          undo(p)
        p = trail.pop()
      } while(!seen(p))

      c = c - 1

      confl = reasons(p)
    } while(c > 0)
    seen(p) = true
    trail.push(p) //need to keep p in the trail
    //p is 1-UIP

    def getAbstractLevel(id: Int) = 1 << (levels(id) & 31)
    //clause minimalization
    var marked: Set[Int] = learntClause.map(_.id).toSet
    val levelsInClause: Set[Int] = marked.map(levels(_)) //we can optimize the search, if we see a node of a level not in the set, then for sure there will be a decision node of the same level

    def litRedundant(lit: Int, abstractLevel: Int): Boolean = {
      var stack = List(lit)
      var analyzeToclear: List[Int] = Nil
      var res = true
      while(!stack.isEmpty && res) {
        val reasonClause = reasons(stack.head)
        stack = stack.tail

        reasonClause.lits.foreach(l => if(l.id != lit && res) {
          val id = l.id

          if(!seen(id) && levels(id) > 0) {
            if(reasons(id) != null && (getAbstractLevel(id) & abstractLevel) != 0) {
              seen(id) = true
              stack ::= id
              analyzeToclear ::= id
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
    learntClause.foreach(lit => absLevel |= getAbstractLevel(lit.id)) //maintain an abstract level

    learntClause = learntClause.filterNot(lit => {
      val reasonClause = reasons(lit.id) 
      reasonClause != null && litRedundant(lit.id, absLevel)
    })

    //compute backtrack level
    val backtrackLevel = if(learntClause.isEmpty) 0 else learntClause.map((lit: Literal) => levels(lit.id)).max
    learntClause ::= new Literal(p, 1-model(p))  //don't forget to add p in the clause !

    (new Clause(learntClause.sortWith((lit1, lit2) => levels(lit1.id) > levels(lit2.id))), backtrackLevel)
  }

  def isAssigned(lit: Literal): Boolean = model(lit.id) != -1
  def isUnassigned(lit: Literal): Boolean = model(lit.id) == -1
  def isSat(lit: Literal): Boolean = (model(lit.id) ^ lit.polInt) == 0
  def isUnsat(lit: Literal): Boolean = (model(lit.id) ^ lit.polInt) == 1


  class Clause(val lits: List[Literal]) {
    var activity: Double = 0d
    var locked = false
    val size = lits.size

    //ignore size 1 for watched literal, they are never kept in the db

    var wl1: Literal = lits.head
    var wl2: Literal = if(size == 1) wl1 else lits(1)
    //private var uwl: Literal = if(size == 3) lits(2) else null

    var arrayLits: Array[Literal] = lits.toArray
    var wli1: Int = 0
    var wli2: Int = 1

    override def toString: String = lits.mkString(", ") + " | wl1: " + wl1 + ", wl2: " + wl2
  }

  class CNFFormula(val originalClauses: List[Clause], val nbVar: Int) {
    require(originalClauses.forall(cl => cl.lits.forall(lit => lit.id >= 0 && lit.id < nbVar)))
    require(originalClauses.forall(cl => cl.lits.size >= 2))
    require(originalClauses.forall(cl => cl.lits.forall(lit => cl.lits.count(_.id == lit.id) == 1)))

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
    originalClauses.foreach(cl => cl.lits.foreach(lit => {
      vsidsQueue.incScore(lit.id, vsidsInc)
    }))

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
      //println("learning: " + clause.lits.map(lit => lit.toString + "@" + levels(lit.id) + " -> " + model(lit.id)))
      assert(clause.size > 1)
      learntClauses ::= clause
      nbClauses += 1
      nbLearntClauses += 1
      for(lit <- clause.lits)
        incVSIDS(lit.id)
      incVSIDSClause(clause)
      if(!clause.lits.tail.isEmpty)//only record if not unit
        recordClause(clause)
      nbLearntClauseTotal += 1
      nbLearntLiteralTotal += clause.lits.size
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
    getWatched(cl.wl1.id, cl.wl1.polInt).prepend(cl)
    getWatched(cl.wl2.id, cl.wl2.polInt).prepend(cl)
  }

  private[this] def unrecordClause(cl: Clause) {
    getWatched(cl.wl1.id, cl.wl1.polInt).remove(cl)
    getWatched(cl.wl2.id, cl.wl2.polInt).remove(cl)
  }


  //maybe use Lit instead of (id, pol). For that we need decide() to be able to find a Literal
  private[this] def enqueueLiteral(lit: Int, pol: Int, from: Clause = null) {
    assert(model(lit) == -1)
    model(lit) = pol
    trail.push(lit)
    reasons(lit) = from
    if(from != null)
      from.locked = true
    levels(lit) = decisionLevel
  }

  private[this] def decide() {
    if(cnfFormula.vsidsQueue.isEmpty)
      status = Satisfiable
    else {
      var next = cnfFormula.vsidsQueue.deleteMax
      while(model(next) != -1 && !cnfFormula.vsidsQueue.isEmpty)
        next = cnfFormula.vsidsQueue.deleteMax
      if(model(next) == -1) {
        nbDecisions += 1
        decisionLevel += 1
        enqueueLiteral(next, nbDecisions & 1)
      } else
        status = Satisfiable
    }
  }

  private[this] def backtrack() {
    nbConflicts += 1
    cnfFormula.decayVSIDS()
    cnfFormula.decayVSIDSClause()
    val (learnedClause, backtrackLevel) = conflictAnalysis
    if(backtrackLevel == -1)
      status = Unsatisfiable
    else {
      if(nbConflicts == nextRestart) {
        if(Settings.stats) {
          println("restart after " + nbConflicts + " nb conflicts")
        }
        restartInterval = (restartInterval*restartFactor).toInt
        nextRestart = nbConflicts + restartInterval
        nbRestarts += 1
        backtrackTo(0)
        if(learnedClause.size == 1) //since we do not learn the clause
          enqueueLiteral(learnedClause.lits.head.id, learnedClause.lits.head.polInt, learnedClause)
        cnfFormula.augmentMaxLearnt()
      } else {
        assert(decisionLevel > backtrackLevel)
        backtrackTo(backtrackLevel)
        val lit = learnedClause.lits.find(isUnassigned).get
        enqueueLiteral(lit.id, lit.polInt, learnedClause) //only on non restart
        //note that if the unitClause is of size 1, there will be an auto-reset to backtrack level 0 so this is correct as well
      }
      if(learnedClause.size > 1) //we only learn if it is not unit, if it is unit, then it is processed via the unitClauses and its consequences is added at level 0 which is never forgot
        cnfFormula.learn(learnedClause)
      status = Unknown
    }
  }


  private[this] def backtrackTo(lvl: Int) {
    while(decisionLevel > lvl && !trail.isEmpty) {
      val head = trail.pop()
      decisionLevel = levels(head)
      if(decisionLevel > lvl)
        undo(head)
      else
        trail.push(head)
    }
    qHead = trail.size
    if(trail.isEmpty)
      decisionLevel = 0
  }

  private[this] def undo(id: Int) {
    assert(model(id) != -1)
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

    while(qHead < trail.size && status != Conflict) {

      val forcedLit = trail(qHead)
      qHead += 1

      val ws = getWatched(forcedLit, 1 - model(forcedLit) ).iterator
      while(ws.hasNext() && status != Conflict) {
        val w = ws.next()

        assert(w.wl1.id == forcedLit || w.wl2.id == forcedLit)

        if(w.wl1.id != forcedLit) {
          val tmpi = w.wli1
          w.wli1 = w.wli2
          w.wli2 = tmpi
          val tmp = w.wl1
          w.wl1 = w.wl2
          w.wl2 = tmp
        }
        assert(w.wl1.id == forcedLit)

        var newWatchedIndex = 0
        var found = false
        while(!found && newWatchedIndex < w.size) {
          val l = w.arrayLits(newWatchedIndex)
          if(newWatchedIndex != w.wli1 && newWatchedIndex != w.wli2 && !isUnsat(l))
            found = true
          else
            newWatchedIndex += 1
        }

        if(found) {
          w.wl1 = w.arrayLits(newWatchedIndex)
          w.wli1 = newWatchedIndex
          getWatched(w.wl1.id, w.wl1.polInt).prepend(w)
          ws.remove()
        } else {
          
          if(isUnsat(w.wl2)) {
            status = Conflict
            qHead == trail.size
            conflict = w
          } else if(isUnassigned(w.wl2)) {
            nbPropagations += 1
            enqueueLiteral(w.wl2.id, w.wl2.polInt, w)
          }
        }
      }

    }

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
      if(!getWatched(cl.wl1.id, cl.wl1.polInt).contains(cl)) {
        println("clause " + cl + " is not correctly watched on " + cl.wl1)
        assert(false)
      }
      if(!getWatched(cl.wl2.id, cl.wl2.polInt).contains(cl)) {
        println("clause " + cl + " is not correctly watched on " + cl.wl2)
        assert(false)
      }
    }

    for(v <- 0 until cnfFormula.nbVar) {
      var it = getWatched(v, 1).iterator
      while(it.hasNext()) {
        val cl = it.next()
        assert((cl.wl1.id == v && cl.wl1.polarity) || (cl.wl2.id == v && cl.wl2.polarity))
      }

      it = getWatched(v, 0).iterator
      while(it.hasNext()) {
        val cl = it.next()
        assert((cl.wl1.id == v && !cl.wl1.polarity) || (cl.wl2.id == v && !cl.wl2.polarity))
      }

    }
  }

  def assertTrailInvariant() {
    val seen: Array[Boolean] = Array.fill(cnfFormula.nbVar)(false) // default value of false
    var lst: List[Int] = Nil
    var currentLevel = decisionLevel

    while(!trail.isEmpty) {
      val head = trail.pop()
      if(levels(head) == currentLevel - 1)
        currentLevel -= 1
      else {
       assert(levels(head) == currentLevel)
      }
      assert(model(head) != -1)
      lst ::= head
      
      if(reasons(head) != null)
        assert(reasons(head).lits.forall(lit => !seen(lit.id)))

      seen(head) = true
    }
    assert(currentLevel == 1 || currentLevel == 0)

    lst.foreach(i => trail.push(i))

  }

}
