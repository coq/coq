(***************************************************************************

  Binary trees a la Hullot.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

Obsolete header:

  CiME Project - Démons research team - LRI - Université Paris XI

  $Id$

***************************************************************************)

open Bit_field

module type BINARY_TREE =
sig
  type t
  val arbre_binaire : 
    int -> (t -> bool) -> (t -> bool) -> t list
end

module Make_binary_tree = 
  functor (BF : Bit_field.S) ->

struct

type t = BF.t

type test = AssezPetit | AssezGrand

let filsg_ag b_length h noeud =  
    BF.bit_and noeud (BF.bit_not (BF.bit_nth h b_length))


let filsd_ag b_length h noeud = 
    BF.bit_and noeud (BF.bit_not (BF.bit_nth_first (pred h) b_length))

let filsg_ap b_length h noeud = 
    BF.bit_or noeud (BF.bit_nth_first (pred h) b_length)


let filsd_ap b_length h noeud = 
    BF.bit_or noeud (BF.bit_nth h b_length)

let rec arbre_binaire_rec length ag ap accu = function
    (0,noeud,AssezGrand) -> 
      if ag noeud then noeud :: accu else accu
  | (0,noeud,AssezPetit) ->
      if ap noeud then noeud :: accu else accu
  | (h,noeud,AssezGrand) ->
      if ag noeud 
      then 
	let left = 
	  arbre_binaire_rec length ag ap accu
	    (pred h,(filsg_ag length (pred h) noeud),AssezGrand) in
	let right_and_left =
	  arbre_binaire_rec length ag ap left
	    (pred h,(filsd_ag length (pred h) noeud),AssezPetit) in
          right_and_left
      else accu
  | (h,noeud,AssezPetit) ->
      if ap noeud 
      then 
	let left = 
	  arbre_binaire_rec length ag ap accu
	    (pred h, (filsg_ap length (pred h) noeud),AssezGrand) in
	let right_and_left = 
	  arbre_binaire_rec length ag ap left
	    (pred h, (filsd_ap length (pred h) noeud),AssezPetit) in
          right_and_left
      else accu
	
let arbre_binaire n assez_grand assez_petit = 
  let root = BF.all_one n in
  let b_length = BF.bit_length root in
  arbre_binaire_rec b_length assez_grand assez_petit [] (n, root, AssezGrand)

end

module Small_binary_tree = Make_binary_tree (Small_bit_field)
module Large_binary_tree = Make_binary_tree (Large_bit_field)


