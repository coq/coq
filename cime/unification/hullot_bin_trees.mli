(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

module type BINARY_TREE =
  sig
    type t
    val arbre_binaire : int -> (t -> bool) -> (t -> bool) -> t list
  end

module Small_binary_tree : 
  BINARY_TREE with type t = int 

module Large_binary_tree : 
  BINARY_TREE with type t = int array
