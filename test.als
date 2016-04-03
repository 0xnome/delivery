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

one sig Grille {cases: set Case}

sig Case {
	x: Int,
	y: Int
}

one sig Entrepot {position: Case}

sig Receptacle {position: Case }

sig Drone {
	position: Case one -> Time,
	commande:  Commande lone -> Time
}

sig Commande {destination: one Receptacle}

one sig CommandesLivrees {
	commandes: set Commande -> Time
}


// ************ invariants  *****************

fact ContraintesCases {
	// Toutes les cases appartiennent à une Grille
	Grille<: cases in Grille one -> Case 

	// Toutes les cases appartiennent ont des coordonées différentes
   all c1:Case, c2:Case | c1 != c2 => c1.x != c2.x || c1.y != c2.y

	// Les cases ont des positions entières et pas trop grandes
	all c:Case | c.x >= 0 && c.y >= 0 && c.x <= 8 && c.y <= 8
}

fact ContraintesLivraisons {
	all t :Time-last | let t'= t.next
	{
		// Un commande livrée reste livrée
		all c: Commande |
			c in CommandesLivrees.commandes.t => c in CommandesLivrees.commandes.t'

    	//Une commande n'etant pas dans un drone ne peut etre livrée
		all c: Commande |
			c not in Drone.commande.t && c not in CommandesLivrees.commandes.t 
					=> c not in CommandesLivrees.commandes.t'	
	}  
}


// 2 drones ne peuvent pas avoir la meme commande à l'instant t (sauf sur l'entrepot)
fact DroneSurUneMemeCaseEtCommandeDifferente {
	all d, d' :Drone | all t:Time | d != d' && d.commande.t != none
														 => d.commande.t != d'.commande.t
	all d, d' :Drone | all t:Time | d != d' && d.position.t != Entrepot.position 
																	=> d.position.t != d'.position.t
}

// ************* FONCTIONS ************************

// retourne la valeur absolue d'un nombre
fun abs[x:Int]:Int {
	x >= 0 => x else x.mul[-1]
}

// retourne la distance entre deux cases
fun distance[p1:Case, p2:Case]: Int {
	plus[	abs[minus[p1.x, p2.x]],abs[minus[p1.y,p2.y]]]
}

//*************** PREDICATS *****************

// Contraintes statiques
pred pasDeplacementDrone[t, t' : Time, d:Drone] {	d.position.t = d.position.t' }

pred pasChangementCommande[t, t' : Time, d:Drone] {	d.commande.t = d.commande.t' }

pred pasDeCommandeLivree[t, t' : Time, d:Drone] { d.commande.t not in CommandesLivrees.commandes.t'}


/****** Prédicats de Précondition *************/
pred PrendreCommandePrecondition[t, t':Time, d:Drone]{
	// le drone n'a pas de commande et est sur l'entrepot
	d.commande.t = none && d.position.t = Entrepot.position && 	(Commande - Drone.commande.t - CommandesLivrees.commandes.t != none)
}

pred DeplacementPrecondition[t, t':Time, d:Drone]{
	// le drone a une commande et n'est pas sur un réceptacle
	d.commande.t != none && d.position.t != d.commande.t.destination.position
}

pred DeposerCommandePrecondition[t, t':Time, d:Drone] {
	// le drone est sur la postion du receptacle de la commande
	d.commande.t != none && d.commande.t.destination.position = d.position.t
}

pred RechargementPrecondition[t,t':Time,d:Drone] {
	// le drone est sur un réceptacle et n'a pas de commande pour ce réceptacle
	
}

pred RetourEntrepotPrecondition[t, t':Time, d:Drone]{
	// le drone n'a plus de commande et sa postion n'est pas celle de l'entrepot
	d.commande.t = none && d.position.t != Entrepot.position
}

/****** Prédicats d'action *************/

// récupère une commande
pred PrendreCommande[t, t':Time, d:Drone]{
	PrendreCommandePrecondition[t, t', d]   

	/*Postcondition:*/
	d.commande.t' != none && d.commande.t' not in CommandesLivrees.commandes.t
	pasDeplacementDrone[t, t', d]
}


// deplacement d'un drone
pred Deplacement[t, t':Time, d:Drone] {

	DeplacementPrecondition[t, t', d]

	//post condition
	distance[d.position.t', d.commande.destination.position [t]] < distance[d.position.t, d.commande.destination.position [t]] 
	distance[d.position.t, d.position.t'] = 1

	pasChangementCommande[t, t', d]
	pasDeCommandeLivree[t, t', d]
}


// Dépose une commande si le drone est sur le receptacle de la commande courante
pred DeposerCommande[t, t':Time, d:Drone]{

	DeposerCommandePrecondition[t,t',d]

	//post condition
	CommandesLivrees.commandes.t' = CommandesLivrees.commandes.t ++ d.commande.t
	d.commande.t' = none

	pasDeplacementDrone[t, t', d]
}

// Rechargement sur un réceptacle
pred Rechargement[t, t':Time, d:Drone]{
	RechargementPrecondition[t,t',d]

	// postcondition
	pasChangementCommande[t,t',d]
	pasDeplacementDrone[t, t', d]
	pas CommandeLivree[t,t',d]
}

// retour à l'entrepot
pred RetourEntrepot[t, t':Time, d:Drone] {

	RetourEntrepotPrecondition[t,t',d]

	//postcondition
	distance[d.position.t', Entrepot.position] < distance[d.position.t,  Entrepot.position]
	distance[d.position.t, d.position.t'] = 1

	pasChangementCommande[t, t', d]
}

// Vrai lorsqu'un drone ne peut rien faire
pred PasDActionPossible[t, t' :Time, d:Drone] {
	not ( DeplacementPrecondition[t, t', d]  or
	 RetourEntrepotPrecondition[t, t', d] or
	 DeposerCommandePrecondition[t, t', d] or
	 PrendreCommandePrecondition[t, t', d] )
}

pred AttentePlusCommande[t, t' :Time, d:Drone] {
	// Si plus de livraisons à faire
	PasDActionPossible[t,t',d]
	//or MouvementImpossible[t,t',d]

	pasChangementCommande[t, t', d]
	pasDeplacementDrone[t, t', d]
}

pred Action[t, t' :Time, d:Drone]{
	PrendreCommande[t, t', d]
	or Deplacement[t, t', d] 
	or DeposerCommande[t, t', d]
	or RetourEntrepot[t,t',d]	
}

/***** SIMULATION *******/
fact Simulation
{
	init[first]
   	all t:Time-last | let t'=t.next
	{
		not (all d:Drone|
			AttentePlusCommande[t,t',d] or Action[t,t',d]) =>
		 (some d:Drone | Action[t,t',d])  

			// SI il n'a pas de commande
			//		SI il n'est pas a l'entreprot
			//			SI deplacement vers entrepot possible
			//				Retour entrepot
			//			SINON 
			//				Attendre
			//		SINON
			//			SI il y a une commande
			//				il recupere un commande
			//			SINON
			//				attendre
			// SINON
			//		SI il est sur le receptacle
			//			il est l'ivre
			//		SINON
			//			SI deplacement possible
			//				Il se déplace vers la livraison
			//			SINON
			//				Attendre
    }
}

pred init [t: Time] {
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

//run a for 4 but exactly 2 Drone, exactly 2 Commande, 4 Case, exactly 20 Time
//check commandesLivrees for 4 but exactly 3 Drone, exactly 4 Commande, exactly 20 Time
//run a for 6 but exactly 2 Drone, exactly 15 Time, 2 Commande, 5 Int
run a for 2 but exactly 2 Drone, exactly 8 Time, exactly 2 Commande, 5 Int, exactly 1 Receptacle, exactly 2 Case
