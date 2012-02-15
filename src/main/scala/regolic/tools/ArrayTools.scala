package regolic.tools

object ArrayTools {

	def arrayCopy[T](src: Array[T])(implicit m: ClassManifest[T]): Array[T] = {
		val l = src.length
		val res = new Array[T](l)
		var i = 0
		while(i < l) {
			res(i) = src(i)
			i += 1
		}
		res
	}

	def matrixCopy[T](src: Array[Array[T]])(implicit m: ClassManifest[T]): Array[Array[T]] = {
		val row = src.length
		var i = 0
		var j = 0
		val res = new Array[Array[T]](row)
		while(i < row) {
			j = 0
			val col = src(i).length
			res(i) = new Array[T](col)
			while(j < col) {
				res(i)(j) = src(i)(j)
				j += 1
			}
			i += 1
		}
		res
	}

	def isSquare[T](matrix: Array[Array[T]], row: Int, col: Int): Boolean = {
		var i = 0
		var res = true
		val realRow = matrix.length
		if(realRow != row) res = false
		while(i < realRow) {
			if(matrix(i).length != col) res = false
			i += 1
		}
		res
	}

	def arrayForAll[T](a1: Array[T], a2: Array[T], p: ((T,T) => Boolean)): Boolean = {
      var i = 0
      var res = true
      val l1 = a1.length
      if(l1 != a2.length) res = false
      else {
          while(i < l1) {
              if(!(p(a1(i),a2(i)))) res = false
              i += 1
          }
      }
      res
	}

	def matrixForAll[T](m1: Array[Array[T]], m2: Array[Array[T]], p: ((T,T) => Boolean)): Boolean = {
      var i = 0
      var res = true
      val row = m1.length
      if(row != m2.length) res = false
      else {
          while(i < row) {
              if(!arrayForAll(m1(i),m2(i),p)) res = false
              i += 1
          }
      }
      res
	}

	def swapRows[T](m: Array[Array[T]], r1: Int, r2: Int) {
		val nbCol = m(r1).length
		var j = 0
		while(j < nbCol) {
			val tmp = m(r1)(j)
			m(r1)(j) = m(r2)(j)
			m(r2)(j) = tmp
			j += 1
		}
	}
	
	def mapElements[T](m: Array[T], f: (T => T), start: Int, until: Int) {
		val max = until - 1
		var i = start
		while(i <= max) {
			m(i) = f(m(i))
			i += 1
		}
	}

	
}
