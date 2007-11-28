(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: subproof.mli aspiwack $ *)


(* This module implements the primitive data type of the interractive
   proof system : subproofs. A subproof is essentially a forest of 
   subproof. The subproofs on the leaves are said open (they are visible
   by the user), the subproofs on the nodes are either partially resolved
   (some of their children are leaves) or resolved (no more of their 
   children are leaves). The node with no children are not considered 
   leaves (they are the simplest form of resolved nodes).

   Very little invariants are actually enforced in this module
   only the basic functions for use in the more complete proof sytem
   which starts in proof.ml. *)

(* The two main types subproof et pointer are, in essence, mutually 
   recursive. Pointers have to be understood as references to subproofs.
   But subproof, as containing mutable parts are not a persistent datatype.

   The second parameter of the types subproof and pointer is a parameter
   stating the shape of the proof. The different shapes are `Subproof,
   `Open and `Resolved. `Open corresponds to a subproof containing a single
   open goal. `Resolved corresponds to a subproof which is resolved.
   `Subproof corresponds to a node in the tree, a partially resolved
   subproof.

   For the subproof type, this shape parameter should be seen as the
   root of the proof. For a pointer, it represents the type of subproof
   it can hold.*)

(* The following invariants are enforced:
   - it is not possible to build a (t,[`Open]) subproof where
     t is not Term.constr.
   - all the function are pure except mutate and reorder

   Some invariants are not enforced:
   - it seemed too inefficient to try and keep the internal structure
     sound. The system handling the reordering of the open goals is
     the cause of it. Thus it is not as transparent as it might appear
     by reading the API. It is advised to avoid mutating a pointer unless 
     it has no open goal on the leaves or you are reversing an earlier
     mutation. If you do not use the API with care, you might mess up the
     internal structure, and get rather unexpected results.
   (* spiwack: some might argue the choice of separating proof and subproof
      in to different files, since the API of subproof is not really
      independant from that of proof. However, I considered it interesting
      since it allowed a better separation of matters and, hopefully,
      much clearer code*)
*)
open Term

type ('a,+'b) subproof constraint 'b = [< `Open | `Resolved | `Subproof ] 
type ('a,+'b) pointer  constraint 'b = [< `Open | `Resolved | `Subproof ] 

(* Gives the subproof held by a pointer *)
val get : ('a,'b) pointer -> ('a,'b) subproof

(* Changes the subproof held by a pointer *)
val mutate : ('a,'b) pointer -> ('a,'b) subproof -> unit


(* Type of functions to  be used with [percolate] *)
type iterator =
    { iterator : 'a.('a,[ `Subproof | `Open | `Resolved ]) pointer -> unit }

(* The percolation function applies a function to all node pointer in the
   subproof. It is guaranteed that an ancestor node will have the function
   applied after all its descendants. *)
(* This function may be a little ad hoc, it has been design mostly solely
   for the interaction with [resolve] and [mutate] and being able to add 
   undo information around the resolution. *)
val percolate : iterator -> ('a,'b)  pointer -> unit

(* This function is meant to turn a subproof that is actually
   resolved into a Resolved Goal.
   It can fail by raising the exception Unresolved when the current goal is
   open or when not all it's immediate children are Resolved.
   It is meant to be use later as the main tile of building a general
   recursive resolve function which will take care of the additional
   bureaucracy (such as the undo and such) *)
exception Unresolved
val resolve : ('a,'b) subproof -> ('a, [> `Resolved]) subproof

(* This function returns [true] if it's argument is resolved, and
   [false] otherwise] *)
val is_resolved : ('a,'b) subproof -> bool

(* This function returns the array containing pointers to all the open 
   subgoals of a given subproof pointer *)
val opengoals : ('a,'b) pointer -> (constr, [> `Open]) pointer array

(* This function returns the result of a resolved subproof *)
val get_result : ('a,[< `Resolved ]) subproof -> 'a

(* This function returns the actual goal represented by an open 
   goal subproof *)
val get_goal : (constr, [< `Open ]) subproof -> Goal.goal

(* Reorders the open goals of the given pointer, according to the 
   permutation *)
val reorder : Permutation.permutation -> ('a, 'b) pointer -> unit

(* The following function creates a new subproof *)
val open_subproof : ?subgoals:Goal.goal array -> 
                    ?instantiate_once_resolved:(Evd.evar_map -> 'a -> 'a) ->
                    (constr array -> 'a) ->
                    ('a, [>`Subproof]) subproof

(* The following function creates a new pointer with a new subproof in it *)
val start_subproof : ?subgoals:Goal.goal array -> 
                    (constr array -> 'a) ->
                    ('a, [>`Subproof]) pointer


(* arnaud:
open Term
open Goal

(* A type which corresponds to the `Subproof case of subproofs *)
type 'a proof_node

(* The type 'a subproof represents the type of subproof "returning"
   an object of type 'a. *)
type 'a subproof = 
    [ `Open of goal
    | `Resolved of 'a
    | `Subproof of 'a proof_node ]


(* The type to identify a specific node or leaf of a subproof.
   Be careful, it indicates a physical position. It can give
   unexpected results if it is used after a proof has mutated *)
type 'a position


(* This function is meant to turn a PartiallyResolvedGoal that is actually
   resolved into a Resolved Goal.
   It can fail by raising the exception Unresolved when the current goal is
   open or when not all it's immediate children are Resolved.
   It is meant to be use later as the main tile of building a general
   recursive resolve function which will take care of the additional
   bureaucracy (such as the undo and such).
   It is a pure function. *)
exception Unresolved

val resolve : [< 'a subproof ] -> [> `Resolved of 'a ]


(* The following function creates a new subproof *)
val open_proof : ?subgoals:goal array -> 
                 callback:(constr array -> 'a) -> 
               [ `Subproof of 'a proof_node ]

(* The following function returns the position of the nth opened subgoal.
   Raises not_found if there is not that many subgoals. *)
val nth_subgoal : int -> [< `Subproof of 'a proof_node 
                          | `Position of 'a position ] -> 'a position
  
(* This function changes the goal at a certain position *)
val mutate : 'a position -> constr subproof -> unit

(* This function returns the subproof pointed by the position [pos] *)
val of_position : 'a position -> constr subproof

(* This function iters a function on all the subproofs of a proof node,
   except the node of the root *)
val iter : ('a position -> constr subproof ->unit) -> constr proof_node -> unit


(* This function iters a function on all the subproof of the root proof
   node *)
val root_iter : ('a position -> constr subproof->unit) -> 'a proof_node -> unit
*)
