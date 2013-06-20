package regolic.sat

/* Naive and (surely) correct sat solver. Useful for unit test with simple formulas. */
object NaiveSolver {

  def isSat(cnf: Set[Set[Literal]]): Option[Array[Boolean]] = {
    val nbVars = cnf.map(cl => cl.map(lit => lit.id).max).max + 1

    val model = Array.fill(nbVars)(true)
    var modelIsValid = false

    /* I hate to do those kind of enumerations, always confusing... */
    def rec(index: Int) {
      if(modelIsValid) ()
      else if(index >= nbVars)
        modelIsValid = Eval(cnf, model)
      else {
        model(index) = true
        rec(index + 1)
        if(!modelIsValid) {
          model(index) = false
          rec(index + 1)
        }
      }
    }
    rec(0)

    if(modelIsValid) Some(model) else None
  }

}
