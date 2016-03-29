module test
open util/ordering[Time] as to
open util/ordering[Commande] as co

// ******* Constantes **********
// Capacité des réceptacles
let RCAP = -1
// capacité des drones
let DCAP = -1
// capacité de la batterie
let BCAP = -1

// ************ Signatures *****************
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

one sig Entrepot
{
	position: Case,
	commandeCourante: Commande -> Time
}

one sig CommandesLivrees
{
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

// ************ invariants  *****************

fact ContraintesCases
{
	// Toutes les cases appartiennent à une Grille
	Grille<: cases in Grille one -> Case 

	// Toutes les cases appartiennent ont des coordonées différentes
   all c1:Case, c2:Case | c1 != c2 => c1.x != c2.x || c1.y != c2.y

	// Les cases ont des positions entières et pas trop grandes
	all c:Case | c.x >= 0 && c.y >= 0 && c.x <= 4 && c.y <= 4
}

// 2 drones ne peuvent pas avoir la meme commande à l'instant t
fact
{
	all d, d' :Drone | all t:Time | d != d' && d.commande.t != none
														 => d.commande.t != d'.commande.t
}

// ************* FONCTIONS ************************

// retourne la valeur absolue d'un nombre
fun abs[x:Int]:Int
{
	x >= 0 => x else x.mul[-1]
}

// retourne la distance entre deux cases
fun distance[p1:Case, p2:Case]: Int
{
	plus[	abs[minus[p1.x, p2.x]],abs[minus[p1.y,p2.y]]]
}

//*************** PREDICATS *****************

pred pasDeplacementDrone[t, t' : Time, ds: set Drone]
{
		all d:Drone - ds | d.position.t = d.position.t'
}

pred pasChangementCommande[t, t' : Time, ds: set Drone]
{
		all d:Drone-ds | d.commande.t = d.commande.t'
}

// récupère une commande
pred PrendreCommande[t, t':Time, d:Drone]
{
	//précondition
	d.commande.t = none
   
	/*Postcondition:*/
	let c = Entrepot.commandeCourante.t
	{
		d.commande.t' = c
		Entrepot.commandeCourante.t' = c.next
	}

	pasDeplacementDrone[t, t', none]
	pasChangementCommande[t, t', d]
}

// deplacement d'un drone
pred Deplacement[t, t':Time, d:Drone]
{
	//précondition
	d.commande.t != none

	//post condition
	distance[d.position.t', d.commande.destination.position [t]] < distance[d.position.t, d.commande.destination.position [t]] 
	distance[d.position.t, d.position.t'] = 1
	d.commande.t = d.commande.t'	

	pasDeplacementDrone[t, t', d]
}

// Dépose une commande si le drone est sur le receptacle de la commande courante
pred DeposerCommande[t, t':Time, d:Drone]
{
	// précondition
	d.commande.t != none && d.commande.destination.position [t] = d.position.t

	//post condition
	d.commande.t' = none

	//pasDeplacementDrone[t, t', none]
}

// lance la simulation principale
fact simulation
{
	init[first]
   all t:Time-last | let t'=t.next
	{
		 some d:Drone|
			PrendreCommande[t, t', d]
			// or Deplacement[t, t', d] 
			// or DeposerCommande[t, t', d]
    }
}

pred init [t: Time] 
{
	// la commande courante est la première de la liste
	Entrepot.commandeCourante.t = first
	
	//aucune commande n'est livrée
	CommandesLivrees.commandes = none

	// Tous les drones sont à l'entrepot au départ
	all d:Drone | d.position.t = Entrepot.position

	// aucun Drone n'a de commande
	all d:Drone | d.commande.t = none

	// les réceptacles ne sont pas sur l'entrepot, et tous à des endroits différents
	all r:Receptacle | r.position != Entrepot.position
	all r1:Receptacle, r2:Receptacle | r1 != r2 => r1.position != r2.position
}

pred a {}

run a for 4 but exactly 3 Drone, exactly 4 Commande, exactly 4 Time
