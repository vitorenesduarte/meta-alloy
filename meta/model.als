module meta/model

open meta/util 

/* SIGNATURES */
sig Name {}

// to simplify, only one Model
one sig Model {
	signatures : set Signature,
	relations : set Relation
}

sig Signature {
	sigName : one Name
}{ 
	all s : Signature | facts[s]
}

pred facts[s : Signature] {
 	// * a signature belongs to the model
	s in Model.signatures

	// * signature names are unique
	#(s.sigName).~sigName = 1
}

sig Relation {
	relName : one Name,
	relation : Int -> Signature -- map
}{
	all r : Relation | facts[r] 
}

pred facts[r : Relation] {
	// * a relation belongs to the model relations
	r in Model.relations 

	// * min key is 0
	let K = keys[r] | min[K] = 0

	// * the keys are consecutive
	let K = keys[r] |  K = range[min[K], max[K]] 

	// * there's only one value for each key
	all k : keys[r] | #(r.relation[k]) = 1
}

// INSTANCES

sig ModelInstance {
	atoms : set Atom,
	relations : set RelationInstance
}

sig Atom {
	atomName : one Name 
	// if the atom name is equal to some Signature name
	// then it's an instance of that Signature
} {
	all a : Atom | facts[a]
}

pred facts[a : Atom] {
	// * an atom belongs to a model instance
	a in ModelInstance.atoms

	// * an atom is an instance of a signature
	a.atomName in Signature.sigName
}

sig RelationInstance {
	riName : one Name,
	// if the relation instance name is equal to some Relation name
	// then it's an instance of that Relation
	relation : Int -> Atom
} {
	all ri : RelationInstance | facts[ri]
}

pred facts[ri : RelationInstance] {
	// * a relation instance belongs to a model instance
	ri in ModelInstance.relations

	// * a relation instance is an instance of a relation
	ri.riName in Relation.relName

	// * min key is 0
	let K = keys[ri] | min[K] = 0

	// * the values of the keys are consecutive
	let K = keys[ri] |  K = range[min[K], max[K]] 
}



/* FUNCTIONS and PREDICATES */

fun keys[r : Relation] : set Int {
	(r.relation).Signature
}

fun keys[ri : RelationInstance] : set Int {
	(ri.relation).Atom
}

fun lastKey[r : Relation] : Int {
	max[keys[r]]
}

fun arity[s : Signature] : Int { 1 }

fun arity[r : Relation] : Int {
	#(keys[r]) 
}

fun domain[r : Relation] : Signature {
	r.relation[0]
}

fun range[r : Relation] : Signature {
	r.relation[lastKey[r]]
}

pred validJoin[s : Signature, r : Relation] {
	domain[r] = s
}

pred validJoin[r : Relation, s : Signature] {
	 range[r] = s
}

pred validJoin[r1, r2 : Relation] {
	validJoin[r1, domain[r2]]
}

pred join[s : Signature, r : Relation, r' : Relation] {
	validJoin[s, r] 
	arity[r] = plus[arity[r'], 1]
	let K = keys[r] - 0 | 
		all k : K | r'.relation = r'.relation + (minus[k, 1] -> r.relation[k])
}

pred join[r : Relation, s : Signature, r' : Relation] {
	validJoin[r, s]
	arity[r] = plus[arity[r'], 1]
	let K = keys[r] - lastKey[r] | 
		all k : K | r'.relation = r'.relation + (k -> r.relation[k])
}

pred join[r1, r2, r' : Relation] {
	validJoin[r1, r2]
	plus[arity[r1], arity[r2]] = plus[arity[r'], 2]
	let K = keys[r1] - lastKey[r1] | 
		all k : K | r'.relation = r'.relation + (k -> r1.relation[k])
	let K = keys[r2] - 0, start = lastKey[r1] | 
		all k : K | let i = plus[start, minus[k, 1]] |  r'.relation = r'.relation + (i -> r2.relation[k])
}

pred isTransitive[r : Relation] {
	validJoin[r, r]
	some r' : Relation | join[r, r, r'] and r' = r
}

fun getRelationByName[ri : RelationInstance] : Relation {
	ri.riName.~relName
}

pred validRelationInstance[ri : RelationInstance] {
	let r = getRelationByName[ri] | 
		#keys[r] = #keys[ri] and r.relation.sigName = ri.relation.atomName
}

