package regolic
package dpllt

import scala.reflect._

/*
 * Combination of two theories. Assume the theories are disjoint.
 * Need to be careful, because shared variables among theories are not handled.
 */
class TheoryWithBoolean[T <: TheoryComponent](val t: T) extends BinaryTheory[BooleanTheory.type, T](BooleanTheory, t)
