(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* arnaud: repasser sur cette description *)
(* This module implements the primitive data type of the interactive
   proof system : subproofs. A subproof is essentially a forest of 
   subgoals. The subgoal on the leaves are said open (they are visible
   by the user), the subgoal on the nodes are either partially resolved
   (some of their children are leaves) or resolved (no more of their 
   children are leaves). The node with no children are not considered 
   leaves (they are the simplest form of resolved nodes).

   Very little invariants are actually enforced in this module
   only the basic functions for use in the more complete proof sytem
   which starts in proof.ml . *)
(* arnaud: rajouter quelque chose sur le fait qu'il y a peu de fonctions
   mutables <= from .mli.
           rechecker un peu la doc des fonctions 
           rajouter les histoires de return value dans le .mli *)

open Term
open Goal


(* We give a type ('a,+'b) pointer 'a is the type of the "return value"
   of the proof 'b is a phantom argument stating the shape of the root
   it can be any subtype of [< `Open | `Resolved | `Subproof ]
   `Open is a single open goal, `Resolved is a node of the subproof
   which knows its value `Subproof is a node which has partial information
   on its value and opens a subproof *)

(* The internal reprentation of the pointer type is 'a _pointer.
   It is actually a type giving a way to access and mutate a subproof.
   That is either a reference or a position in an array.
   The reference is used to carry the mutable behavior down to the root *)
type 'a _subproof =
    (* An open goal *)
    | Open of goal
    (* A subproof whose content is resolved, holds its "return value" *)
    (*arnaud: expliquer les machins de instantiate *)
    | Resolved of (Evd.evar_map -> 'a -> 'a)*'a
    (* A partially resolved subproof *)
    | Subproof of 'a partially_resolved_subproof
    (* A proof whose open goals have been permuted *)
    | Permutation of constr _pointer array * 'a _subproof
    (* A subproof which is routed because there has been a permutation *)
    | Route of 'a _pointer

(* A partially_resolved_subproof is that data of an array of subsubproofs
   and a resolver function to close the subproof when every subproof above is
   resolved *)
(* In essence a partially resolved subproof could be an existential type:
   {exists b. subproof b _subproof array; resolver : 'b array -> 'a}. There
   is two main obstactle to this design choice :
   1/ There is no existential type in OCaml
   2/ There is sometimes need to know that internal subproofs
      actually are constr _subproof, since tactics create such new goals.
   The 1/ could be avoided by additional boxings and a bit of extra
   verbosity, though it will probably impair a bit the legibility of
   the code. The 2/ seems more of a problem thus the actual design 
   choice is probably definite *)
   (* arnaud: raconter les histoire d'instanciations *)
and  'a partially_resolved_subproof = 
    { node : constr _subproof array;
      resolver : constr array -> 'a;
      instantiate_once_resolved: Evd.evar_map -> 'a -> 'a
    }
and 'a _pointer = 
    | Root of 'a _subproof ref
    | Node of 'a _subproof array*int

type ('a,+'b) pointer = 'a _pointer 
     constraint 'b = [< `Open | `Resolved | `Subproof ] 

(* This type gives *)
type ('a,+'b) subproof = 'a _subproof
     constraint 'b = [< `Open | `Resolved | `Subproof ] 

(* Internal function which gives the subproof contained by the pointer *)
let get = function
  | Root r_sp -> !r_sp
  | Node(sp_array,ix) -> sp_array.(ix)

(* Internal function which gives the "real" subproof represented by a subproof.
   it goes through the Route-s and Permutation-s to give the useful content
   of the proof *)
let rec simplify = function
  | (Open _ as sp) 
  | (Resolved _ as sp)
  | (Subproof _ as sp)
  | Permutation(_,sp) -> sp
  | Route pt -> simplify (get pt)

(* composition of the above two functions *)
let get_simplify sp = simplify (get sp)

let mutate pt sp =
  match pt with
  | Root r_nd -> r_nd := sp
  | Node(sp_array,ix) -> sp_array.(ix) <- sp

(* Type of the iterators (used with the iteration function) *)
(* The need to define a new type is due the universal quantification
   since not all the nodes have the same type case *)
type iterator = { iterator : 'a.'a _pointer -> unit }

(* The percolation function applies a function to all node pointer in the
   subproof. It is guaranteed that an ancestor node will have the function
   applied after all its descendants. *)
(* This function may be a little ad hoc, it has been design mostly solely
   for the interaction with [resolve] and [mutate] and being able to add 
   undo information around the resolution. *)
(* The extra seemingly unnecessary functions are here for typing issue,
   the idea is that traverse_deep (: iterator -> constr _subproof -> unit) 
   doesn't have the same type as traverse 
   (: iterator -> 'a -> _subproof -> unit) *)
let percolate =
  let rec percolate_body traverse it pt =
     match get pt with
     | Resolved _ -> ()
     | Open _ -> it.iterator pt
     | Subproof prs 
     | Permutation(_, Subproof prs) -> traverse it prs ; it.iterator pt
     | Permutation(_, _) -> it.iterator pt
     | Route pt -> percolate_body traverse it pt
  in
  let traverse_body traverse_deep it prs =
    Array.iteri (fun i _ -> percolate_body traverse_deep it (Node(prs.node,i)))
                                prs.node
  in
  let rec traverse_deep it prs = 
    traverse_body traverse_deep it prs
  in
  let rec traverse it prs =
    traverse_body traverse_deep it prs
  in
  fun it pt -> percolate_body traverse it pt


(* This function is meant to turn a subproof that is actually
   resolved into a Resolved Goal.
   It can fail by raising the exception Unresolved when the current goal is
   open or when not all it's immediate children are Resolved.
   It is meant to be use later as the main tile of building a general
   recursive resolve function which will take care of the additional
   bureaucracy (such as the undo and such) *)
exception Unresolved

let resolve = 
  let atomic_convert sp = (*converts a Resolved _ into a constr *)
    match simplify sp with
    | Resolved (_,constr) -> constr
    | _ -> raise Unresolved
  in 
  let convert arr =
    Array.map atomic_convert arr
  in
  fun sp ->
    match simplify sp with
    | Open _ -> raise Unresolved
    | Resolved _ as sp -> sp
    | Subproof psr -> let sub_constr = convert psr.node in
	              Resolved (psr.instantiate_once_resolved,
				psr.resolver sub_constr)
    | _ -> Util.anomaly "Subproof.resolve: failure of simplify"

(* This function perform one step of instantiation (of evars) of a subproof, 
   it is pure, and is meant to be used together with percolate and the 
   undo mechanism *)
let instantiate em = function
  | Open g -> Open (Goal.instantiate em g)
  (* arnaud: Evarutil ou ...? cf goal.ml *)
  | Resolved (f,constr) -> Resolved (f, f em constr)
  | _ as sp -> sp


(* This function returns [true] if it's argument is resolved, and
   [false] otherwise] *)
let is_resolved sp =
  match simplify sp with
  | Resolved _ -> true
  | _ -> false

(* This function returns the array containing pointers to all the open 
   subgoals of a given subproof pointer *)
(* extra functions due to typing issue *)
(* arnaud: ça mérite un peu d'être creusé. loga = list_opengoals_array *)
let opengoals =
  let list_opengoals_node_body loga next cont pt = 
      match get pt with
      (* by construction a pointer containing an Open goal are
	 always constr _pointer. If we omit the magic, then we
         cannot express opengoals in all generality *)
      | Open _ -> [(Obj.magic pt:constr _pointer)]
      | Resolved _ -> next cont
      | Subproof psr -> loga next cont psr.node 0
      (* For the semantics to be correct here we need all the
         open goals to be contained in subproofs from the permuted 
         array all such open goal to be actually linked to the subproof. 
         This invariant is not enforced by typing (unfortunately), but
         should be kept correct as long as one does not do absurd things
         with proofs *)
      | Permutation (arr,_) ->let sp_arr = Array.map get arr in
                              loga next cont sp_arr ((Array.length arr) - 1)
      | Route _ -> Util.anomaly "Subproof.opengoals: abnormal Route node"
  in
  let rec list_opengoals_array return cont sp_arr ix =
    if ix < 0 then
      return cont
    else
      let next new_cont = list_opengoals_array return new_cont sp_arr ix in
      list_opengoals_node_body list_opengoals_array next cont (Node(sp_arr,ix))
  in
  let list_opengoals_node pt =
    list_opengoals_node_body list_opengoals_array (fun cont -> cont) [] pt
  in
  fun pt ->
    Array.of_list (list_opengoals_node pt)

(* This function returns the result of a resolved subproof *)
let get_result sp = 
  match simplify sp with
  | Resolved (_,res) -> res
  | _ -> Util.anomaly "Subproof.get_result: failure of simplify"

(* This function returns the actual goal represented by an open 
   goal subproof *)
let get_goal sp =
  match simplify sp with
  | Open gl -> gl
  | _ -> Util.anomaly "Subproof.get_goal: failure of simplify"

(* Reorders the open goals of the given pointer, according to the 
   permutation *)
let reorder =
  let copy pt = (* creates a new pointer towards the same content *)
    Root (ref (get pt))
  in
  let route pt_route pt_content =  (* mutates [pt_route] into a route to *)
                                   (* [pt_content] *)
    mutate pt_route (Route (pt_content))
  in
  fun perm pt ->
    let og = opengoals pt in
    let copied_og = Array.map copy og in
    Array.iteri (fun i pt -> route pt copied_og.(i)) og;
    let reordered_og = Permutation.permute perm copied_og in
    mutate pt (Permutation(reordered_og, get pt))


(* The following function creates a new subproof *)
let no_instantiate _ _ = Util.anomaly "Subproof.instantiate: this proof does not support instantiation in its resolved form"
let open_subproof ?(subgoals=[||]) ?(instantiate_once_resolved= no_instantiate) resolver =
   Subproof { node = Array.map (fun g -> Open g) subgoals;
              resolver = resolver;
	      instantiate_once_resolved = instantiate_once_resolved}

(* The following function creates a new pointer with a new subproof in it *)
(* arnaud: vérifier qu'on a pas besoin d'un instantiate *)
let start_subproof ?(subgoals=[||]) resolver =
  Root (ref (open_subproof ~subgoals:subgoals resolver))

(* [iteri f s] takes a function [f] of indices and [Subproof.pointer]
   and apply it to all the subproofs of [s], provided [s] is a
   [[`Subproof] subproof] *)
let iteri f s = 
  match simplify s with
  | Subproof {node=a} -> Array.iteri (fun i _ -> f i (Node(a,i)))
  | _  -> Util.anomaly "Subproof.iteri: failure of simplify"
