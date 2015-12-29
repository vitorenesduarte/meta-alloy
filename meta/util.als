module meta/util

open util/integer

fun range[min : Int, max : Int] : set Int {
	min.*next & *next.max
}

// why functions like arity, domain and range are not here:
// http://stackoverflow.com/questions/27700724/how-to-reuse-facts-by-means-of-modules-in-alloy
