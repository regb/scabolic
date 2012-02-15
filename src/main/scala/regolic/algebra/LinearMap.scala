package regolic.algebra

trait LinearMap[T, F <: Field[F], V <: VectorSpace[V, F], W <: VectorSpace[W, F]] extends VectorSpace[T, F] {

  def apply(vector: V): W

}
