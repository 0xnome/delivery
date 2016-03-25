open util/ordering[Time] as to

sig Time {}

one sig Grille
{
  	cases: set Case,
}

sig Case
{
	x: Int,
	y: Int
}

// Toutes les cases appartiennent à une Grille
fact UneGrille
{
	Grille<: cases in Grille one -> Case 
}

fact ContraintesCases
{
	// Toutes les cases appartiennent ont des coordonées différentes
   all c1:Case, c2:Case | c1 != c2 => c1.x != c2.x && c1.y != c2.y
	// Les cases ont des positions entières et pas trop grandes
	all c:Case | c.x >= 0 && c.y >= 0 && c.x <= 4 && c.y <= 4
}


sig Drone
{
	position: Case one -> Time
}

one sig Entrepot
{
	position: Case
}

sig Receptacle
{
	position: Case
}

fact PositionReceptacle
{
	all r:Receptacle | r.position != Entrepot.position
	all r1:Receptacle, r2:Receptacle | r1 != r2 => r1.position != r2.position
}

pred init [t: Time] 
{
	all d:Drone | d.position.t = Entrepot.position
}

fun abs[x:Int]:Int
{
	x >= 0 => x else x.mul[-1]
}

fun distance[p1:Case, p2:Case]: Int
{
	abs[p1.x - p2.x] + abs[p1.y - p2.y]
}

fact simulation
{
	init[first]
}

pred a {}

run a for 3 but 10 Case, 6 Int, 5 Time
