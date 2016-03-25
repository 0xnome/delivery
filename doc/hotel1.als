open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Key {}
sig Time {}

sig Room 
{
	keys: set Key,
	currentKey: keys one -> Time
}

fact DisjointKeySets 
{
	-- each key belongs to at most one room
	Room<:keys   in   Room lone-> Key
}

one sig FrontDesk 
{
	lastKey: (Room -> Key) -> Time,
	occupant: (Room -> Guest) -> Time
}

sig Guest 
{
	keys: Key -> Time
}

pred go {}
run go

fun nextKey [k: Key, ks: set Key]: set Key 
{
	min [k.nexts & ks]
}
