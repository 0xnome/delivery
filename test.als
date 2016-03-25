open util/ordering[Time] as to

sig Time {}

sig Drone
{
	position: Case
}

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

fact DisjointCasePosition
{
	// Toutes les cases appartiennent ont des coordonées différentes
   all c1:Case, c2:Case | c1 != c2 => c1.x != c2.x && c1.y != c2.y
	// Les cases ont des positions entières et pas trop grandes
	all c:Case | c.x >= 0 && c.y >= 0 && c.x <= 4 && c.y <= 4
}

pred init [t: Time] 
{

}

pred a {}

run a for 3 but 10 Case, 6 Int, 5 Time