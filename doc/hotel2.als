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

fun nextKey [k: Key, ks: set Key]: set Key 
{
	min [k.nexts & ks]
}

pred init [t: Time] 
{
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t
}

pred go
{
    init [first]
}
run go
