package regolic
package smt

import asts.core.Trees._

/*
 * id is unique per predicate, different literals with same predicate but different polarity
 * will have the same id
 */
class Literal(val predicate: PredicateApplication, val id: Int, val polarity: Boolean)
