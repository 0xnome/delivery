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
	position: Case
	// commandeCourante: Commande -> Time
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

one sig CommandesLivrees
{
	commandes: set Commande -> Time
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

fact ContraintesLivraisons
{
	all t :Time-last | let t'= t.next
	{
		// Un commande livrée reste livrée
		all c: Commande |
			c in CommandesLivrees.commandes.t => c in CommandesLivrees.commandes.t'
		}  
}

fact ContraintesLivraisons
{
	all t :Time-last | let t'= t.next
	{
	//Une commande n'etant pas dans un drone ne peut etre livrée
		all c: Commande |
			c not in Drone.commande.t && c not in CommandesLivrees.commandes.t 
					=> c not in CommandesLivrees.commandes.t'
	}  
}

// 2 drones ne peuvent pas avoir la meme commande à l'instant t
fact
{
	all d, d' :Drone | all t:Time | d != d' && d.commande.t != none
														 => d.commande.t != d'.commande.t
	all d, d' :Drone | all t:Time | d != d' && d.position.t != Entrepot.position 
																	=> d.position.t != d'.position.t
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

pred pasDeplacementDrone[t, t' : Time, d:Drone]
{
		d.position.t = d.position.t'
}

pred pasChangementCommande[t, t' : Time, d:Drone]
{
		d.commande.t = d.commande.t'
}

pred pasDeCommandeLivree[t, t' : Time, d:Drone]
{
	d.commande.t not in CommandesLivrees.commandes.t'
}

// récupère une commande
pred PrendreCommande[t, t':Time, d:Drone]
{
	//précondition
	d.commande.t = none && d.position.t = Entrepot.position
   
	/*Postcondition:*/
	d.commande.t' != none //&& d.commande.t' not in CommandesLivrees
	pasDeplacementDrone[t, t', d]
}

// deplacement d'un drone
pred Deplacement[t, t':Time, d:Drone]
{
	//précondition
	d.commande.t != none && d.position.t != d.commande.t.destination.position

	//post condition
	distance[d.position.t', d.commande.destination.position [t]] < distance[d.position.t, d.commande.destination.position [t]] 
	distance[d.position.t, d.position.t'] = 1
	d.commande.t = d.commande.t'	

	pasChangementCommande[t, t', d]
	pasDeCommandeLivree[t, t', d]
}

// Dépose une commande si le drone est sur le receptacle de la commande courante
pred DeposerCommande[t, t':Time, d:Drone]
{
	// précondition
	d.commande.t != none && d.commande.t.destination.position = d.position.t


	//post condition
	CommandesLivrees.commandes.t' = CommandesLivrees.commandes.t ++ d.commande.t
	d.commande.t' = none

	pasDeplacementDrone[t, t', d]
}

pred RetourEntrepot[t, t':Time, d:Drone]
{
	//precondition
	d.commande.t = none && d.position.t != Entrepot.position
	
	//postcondition
	distance[d.position.t', Entrepot.position] < distance[d.position.t,  Entrepot.position]
	distance[d.position.t, d.position.t'] = 1

	pasChangementCommande[t, t', d]
}

pred Attendre[t, t' :Time, d:Drone]
{

	// Précondition
	pasChangementCommande[t, t', d]
	pasDeplacementDrone[t, t', d]
	pasDeCommandeLivree[t, t', d]
}

// lance la simulation principale
fact simulation
{
	init[first]
   	all t:Time-last | let t'=t.next
	{
		all d:Drone|
			PrendreCommande[t, t', d]
			or Deplacement[t, t', d] 
			or DeposerCommande[t, t', d]
			or RetourEntrepot[t,t',d]
			//or Attendre[t,t',d]


			//il faudrait ajouter la logique : 
			// SI il n'a pas de commande
			//		SI il n'est pas a l'entreprot
			//			Retour entrepot
			//		SINON 
			//			il recupere un commande
			// SINON
			//		SI il est sur le receptacle
			//			il livre
			//		SINON
			//			Il se déplace vers la livraison
    }
}

pred init [t: Time] 
{
	//aucune commande n'est livrée
	CommandesLivrees.commandes.t = none

	// Tous les drones sont à l'entrepot au départ
	all d:Drone | d.position.t = Entrepot.position

	// aucun Drone n'a de commande
	all d:Drone | d.commande.t = none

	// les réceptacles ne sont pas sur l'entrepot, et tous à des endroits différents
	all r:Receptacle | r.position != Entrepot.position
	all r1:Receptacle, r2:Receptacle | r1 != r2 => r1.position != r2.position
}

assert commandesLivrees {
	CommandesLivrees.commandes.last != none
}



pred a {}

run a for 4 but exactly 3 Drone, exactly 2 Commande, 4 Case, exactly 20 Time
check commandesLivrees for 4 but exactly 3 Drone, exactly 4 Commande, exactly 20 Time
run a for 3 but exactly 1 Drone, exactly 15 Time, exactly 3 Commande
