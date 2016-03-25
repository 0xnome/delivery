module test
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
   all c1:Case, c2:Case | c1 != c2 => c1.x != c2.x || c1.y != c2.y

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

pred init [t: Time] 
{
	// Tous les drones sont à l'entrepot au départ
	all d:Drone | d.position.t = Entrepot.position

	// les réceptacles ne sont pas sur l'entrepot, et tous à des endroits différents
	all r:Receptacle | r.position != Entrepot.position
	all r1:Receptacle, r2:Receptacle | r1 != r2 => r1.position != r2.position
}

fun abs[x:Int]:Int
{
	x >= 0 => x else x.mul[-1]
}

fun distance[p1:Case, p2:Case]: Int
{
	abs[p1.x - p2.x] + abs[p1.y - p2.y]
}

pred deplacement[t, t':Time, d:Drone]
{
	distance[d.position.t, d.position.t'] = 1
}

fact simulation
{
	init[first]
   /* all t:Time-last | let t'=t.next
	{
		all d:Drone | deplacement[t, t', d]
    }*/
}

pred a {}

run a for 4 but exactly 1  Drone
