module test
open util/ordering[Time] as to

sig Time {}

// ******* Constantes **********
// Capacité des réceptacles
let RCAP = -1
// capacité des drones
let DCAP = -1
// capacité de la batterie
let BCAP = -1
//******************************

one sig Grille
{
  	cases: set Case,
}

sig Case
{
	x: Int,
	y: Int
}

fact ContraintesCases
{
	// Toutes les cases appartiennent à une Grille
	Grille<: cases in Grille one -> Case 

	// Toutes les cases appartiennent ont des coordonées différentes
   all c1:Case, c2:Case | c1 != c2 => c1.x != c2.x || c1.y != c2.y

	// Les cases ont des positions entières et pas trop grandes
	all c:Case | c.x >= 0 && c.y >= 0 && c.x <= 4 && c.y <= 4
}

one sig Entrepot
{
	position: Case,
	commandes: set Commande
}

sig Drone
{
	position: Case one -> Time,
	commande:  Commande lone -> Time
}

sig Commande
{
	destination: one Receptacle
}


sig Receptacle
{
	position: Case
}

// 2 drones ne peuvent pas avoir la meme commande à l'instant t
fact
{
	all d, d' :Drone | all t:Time | d != d' && d.commande.t != none
														 => d.commande.t != d'.commande.t
}

pred init [t: Time] 
{
	// Tous les drones sont à l'entrepot au départ
	all d:Drone | d.position.t = Entrepot.position

	// Toutes les cases appartiennent à une Grille
	Entrepot<: commandes in Entrepot one -> Commande 

	// aucun Drone n'a de commande
	all d:Drone | d.commande.t = none

	// les réceptacles ne sont pas sur l'entrepot, et tous à des endroits différents
	all r:Receptacle | r.position != Entrepot.position
	all r1:Receptacle, r2:Receptacle | r1 != r2 => r1.position != r2.position
}

// retourne la valeur absolue d'un nombre
fun abs[x:Int]:Int
{
	x >= 0 => x else x.mul[-1]
}

// retourne la distance entre deux cases
fun distance[p1:Case, p2:Case]: Int
{
	abs[p1.x - p2.x] + abs[p1.y - p2.y]
}

// se déplace ou non
pred Deplacement[t, t':Time, d:Drone]
{
	//précondition
	d.commande.t != none

	//post condition
	distance[d.position.t, d.position.t'] < distance[d.position.t, d.commande.destination.position [t]] 
			&& distance[d.position.t, d.position.t'] <= 1 && d.commande.t = d.commande.t'
		
}

// récupère une commande
pred PrendreCommande[t, t':Time, d:Drone]
{
	//précondition
	d.commande.t = none

	//post condition
	some c:Commande | d.commande.t' = c => d.commande.t' = c
}

// Dépose une commande si le drone est sur le receptacle de la commande courante
pred DeposerCommande[t, t':Time, d:Drone]
{
	// précondition
	d.commande.t != none && d.commande.destination.position [t] = d.position.t

	//post condition
	d.commande.t' = none
}

// lance la simulation principale
fact simulation
{
	init[first]
   all t:Time-last | let t'=t.next
	{
		 all d:Drone |
			PrendreCommande[t, t', d] or
			Deplacement[t, t', d] or
			DeposerCommande[t, t', d]
    }
}

pred a {}

run a for 4 but exactly 1 Drone, exactly 2 Commande, exactly 10 Time
