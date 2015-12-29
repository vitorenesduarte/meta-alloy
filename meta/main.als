module meta/main

open util/boolean
open meta/model as M

pred someTernaryRelation {
	no ModelInstance 
	one Relation
	some r : Relation | let interesting = domain[r] != range[r] |
		interesting and arity[r] = 3
}

run someTernaryRelation for 3 but 3 Int 

pred someLeftJoin {
	no ModelInstance 
	#(Relation) = 2
	some s : Signature, r, r' : Relation | let interesting = arity[r] > 2 and domain[r] != range[r'] |
		interesting and join[s,r,r']
}

pred someRightJoin {
	no ModelInstance
	#(Relation) = 2
	some s : Signature, r, r' : Relation | let interesting = arity[r] > 2 |
		interesting and join[r,s,r']	
}

pred someJoin {
	no ModelInstance
	some disj r1, r2, r' : Relation | let interesting = arity[r1] > 1 and arity[r2] > 1 and domain[r'] != range[r'] | 
		interesting and join[r1,r2, r']
}

run someLeftJoin for 3 but 3 Int
run someRightJoin for 3 but 3 Int
run someJoin for 3 but 3 Int

check theArityOfAJoinIsAlwaysTwoLessThanTheSumOfTheAritiesOfItsArguments {
	all r1, r2, r' : Relation, s : Signature |
		join[s, r1, r'] implies arity[r'] = minus[plus[arity[r1], arity[s]], 2] and
		join[r1, s, r'] implies arity[r'] = minus[plus[arity[r1], arity[s]], 2] and
		join[r1, r2, r'] implies arity[r'] = minus[plus[arity[r1], arity[r2]], 2]
}

pred someTransitiveRelation {
	no ModelInstance
	one Relation
	some r : Relation |  isTransitive[r]
}

run someTransitiveRelation for 3 but 3 Int

check allTransitiveRelationsAreBinary {
	all r : Relation | isTransitive[r] => arity[r] = 2
}

pred someValidRelationInstance_[b : Bool] {
	one ModelInstance
	one Relation
	one RelationInstance
	some ri : RelationInstance |	let interesting = some k : keys[ri] | #ri.relation[k] > 1 | 
		interesting and (isTrue[b] => validRelationInstance[ri] else !validRelationInstance[ri])
}

pred someValidRelationInstance{ someValidRelationInstance_[True] }
pred someInvalidRelationInstance{ someValidRelationInstance_[False] }

run someValidRelationInstance for 3 but 3 Int
run someInvalidRelationInstance for 3 but 3 Int
