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

let rec resolve = 
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

(* This function returns [true] if it's argument is resolved, and
   [false] otherwise] *)
let is_resolved sp =
  match simplify sp with
  | Resolved _ -> true
  | _ -> false

(* This function returns the array containing pointers to all the open 
   subgoals of a given subproof pointer *)
(* extra functions due to typing issue *)
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



(*arnaud:
  let list_opengoals_body log_deep traverse return cont sp_arr ix =
    let next cont = traverse cont sp_arr (ix-1) in
    if ix < 0 then
      return cont
    else
      match get sp_arr.(ix) with
      | Open _ -> [Node(sp_arr,ix)]
      | Resolved _ -> next cont
      | Subproof psr -> log_deep next cont psr.node 0
      (* For the semantics to be correct here we need all the
         open goals to be contained in subproofs from the permuted 
         array all such open goal to be actually linked to the subproof. 
         This invariant is not enforced by typing (unfortunately), but
         should be kept correct as long as one does not do absurd things
         with proofs *)
      | Permutation (arr,_) -> log_deep next cont arr ((Array.length arr) - 1)
      | Route (_, _) -> anomaly "Subproof.opengoals: abnormal Route node"
  in
  let rec deep_list_opengoals return cont sp_arr ix =
    list_opengoals_body deep_list_opengoals (deep_list_opengoals return)
  in
  let rec list_opengoals cont sp_arr ix =
    list_opengoals_body deep_list_opengoals 
                        traverse 
                        (fun cont -> cont)
  in
  function 
  | Root r_sp -> match !sp with
                 | Subproof
  | Node(sp_arr, ix) -> Array.of_list (list_opengoals [] sp ix) *)



(* arnaud:

(* The type 'a subproof represents the type of subproofs "returning"
   an object of type 'a. *)
(* In essence the type 'a proof_node should be an existential type
   of the shape 'a proof_node = exists 'b.{ node : 'b subproof array;
                                            fallback : 'b array -> 'a}
   However, this extra layer of abstraction is hardly needed in practice
   and since existential types are not primitive in OCaml (though 
   somewhat encodable through some additional boxing) it wasn't worth
   the extra complication.
   The type of nodes is specialized (in constr subproof) to allow clearer
   and more efficient code *)
(* arnaud: rather old style
type 'a proof_node = 
    { node : constr subproof array;
      callback : constr array -> 'a
    }
and 'a subproof = 
    [ `Open of goal
    | `Resolved of 'a
    | `Subproof of 'a proof_node ] *)

(* arnaud: old style
    | OpenGoal of goal
    | PartiallyResolvedGoal of 'a proof_node
    | ResolvedGoal of 'a *)

(* This type replaces an existential typing *)
type 'a deep_node = 
    | Root of 'a proof_node
    | Node of constr proof_node

(* The type to identify a specific node or leaf of a subproof *)
type 'a position = { handle:'a deep_node;
		     index:int}

(* This function is meant to turn a `Subproof that is actually
   resolved into a Resolved Goal.
   It can fail by raising the exception Unresolved when the current goal is
   open or when not all it's immediate children are Resolved.
   It is meant to be use later as the main tile of building a general
   recursive resolve function which will take care of the additional
   bureaucracy (such as the undo and such) *)
exception Unresolved

let resolve = 
  let convert arr =(* converts an array of `Resolved into an array of constr *)
    Array.map 
      (function | `Resolved constr -> constr
                | _ -> raise Unresolved) arr
  in

  function | `Subproof sp -> 
                    let sub_constr = convert sp.node in
		    `Resolved (sp.callback sub_constr)
           | (`Resolved _) as rg -> rg
	   | `Open _ -> raise Unresolved


(* arnaud: virer ce truc inutile, comprendre une solution à base de dictionaire
   ou filtre éventuellement
(* The following function switches two proof_node (identified by their indices)
   of a given subproof. *)
(* spiwack: I don't really know if it will prove a useful function. It has
     the very big default that it does not scale up very well. Indeed,
     it does not allow switching proofs that are in different subtrees,
     which is what the user may wants to do, but can't be done at this 
     level.
     It is  not currently in the .mli would require a bit of thinking
     to get the right version. *)
(* arnaud : cette fonction mute le callback, faire attention à bien faire
   l'undo proprement *)
let switch =
  let array_switch i j arr =
    let buf_i = arr.(i) in
    let buf_j = arr.(j) in (* not necessary, could be replaced by a 
                              length check *)
    arr.(i) <- buf_j; arr.(j) <- buf_i
  in

  fun i j sp ->
    array_switch i j sp.node;
    sp.callback <- (fun arr -> array_switch i j arr; 
		                                (* the array that is switched
						   back is a newly born array
						   no risk of corrupting data
						   by modifying it *)
		               sp.callback arr)    
*)

(* The following function creates a new subproof *)
let open_proof ?(subgoals=[||]) ~callback =
  `Subproof { node = Array.map (fun g -> `Open g) subgoals;
              callback = callback }


(* This function returns the subproof pointed by the position [pos] *)
let of_position pos =
  match pos.handle with
  | Root sp -> sp.node.(pos.index)
  | Node sp -> sp.node.(pos.index)

(* The following function returns the position of the nth opened subgoal.
   Raises not_found if there is not that many subgoals. 
   It acts either on a subproof of the form `Subproof _ or on a position *)
let rec nth_subgoal = 
  (* [nth_subgoal] basically does a depth-first search of the proof
     subtree.
     The implementation of the function is a bit tricky, due to typing
     issue (again the absence of existential types makes things a bit 
     more tedious (yet less than if we used an encoding)).
     The main subfunction is the function [abstract_traverse] which
     takes as arguments the recursive calls. The argument [traverse]
     is the function that is called when checking the next goal of
     a node (and is abstracted inside the function [next]). The
     argument [deep_traverse] is called when going one node deeper
     in the subproof tree. The [return] argument is used when
     backtracking to a parent node. [n] is the number of open goals
     to find before we find the goal we look for: it is decreased by
     [1] each time we find a open subgoal, except if it is already [1]
     in which case we terminate the algorithm on the first open subgoal
     we find. [ix] represent the current index in the array of the node.
     [pn] is the current subproof node we are currently traversing.
     Finally [box] is a function giving a way to coerce the current
     [proof_node] (namely [pn]) into the appropriate ['a deep_node]
     where ['a] correspond to the return type of the root of the proof
     we consider.
     This function being defined we can define the two main subroutines
     [deep_traverse] is basically [abstract_traverse deep_traverse 
     deep_traverse]. It performs the search inside any non-root node
     since all of them are of type [constr proof_node] it is simply
     self-recursive.
     The function [traverse] takes care of the search on the root node.
     That is, basically, [abstract_traverse traverse deep_traverse].
     Because of the heterogeneous typing of the root and deep nodes
     it calls deep_traverse when it goes deeper in the tree *)
  let abstract_traverse traverse deep_traverse return n ix pn box =
    if ix < Array.length pn.node then
      let next n = traverse n (ix+1) pn in
      match pn.node.(ix) with
      | `Open _ when n = 1     -> {handle=box pn;index=ix}
      | `Open _                -> next (n-1)
      | `Resolved _            -> next n
      | `Subproof rpn -> deep_traverse next n 0 rpn
    else
      return n
  in
  let node u = Node u in
  let rec deep_traverse return n ix pn =
    abstract_traverse (deep_traverse return) deep_traverse return n ix pn node
  in
  let root u = Root u in
  let rec traverse n ix pn =
    abstract_traverse traverse
                      deep_traverse
                      (fun _ -> raise Not_found)
                      n
                      ix
                      pn root
  in
  fun n sp ->
    if n < 1 then
      invalid_arg "Subproof.nth_subgoal: no non-positive open goal"
    else
      match sp with
      | `Subproof pn -> traverse n 0 pn
      | `Position pos ->  
	  match of_position pos with
	  | `Subproof pn     -> deep_traverse (fun _ -> raise Not_found) n 0 pn
	  | `Open _ when n=1 -> pos
	  | `Open _          -> raise Not_found
	  | `Resolved _      -> raise Not_found

(* arnaud: to clean  
  let abstract_traverse traverse n parents ix sp dsp =
    if ix < Array.length sp.node then
      match sp.node.(ix) with
      | `Open _ when n = 1     -> {handle=dsp;index=ix}
      | `Open _                -> traverse (n-1) parents (ix+1) dsp
      | `Resolved _            -> traverse n parents (ix+1) dsp
      | `Subproof rsp -> traverse n ((dsp, ix)::parents)
	                                      0 (Node rsp)
    else
      match parents with
      | (dsp, jx)::q -> traverse n q (jx+1) dsp
      | [] -> raise Not_found
  in
  let rec traverse n parents ix = function
    | (Root sp) as dsp -> abstract_traverse traverse n parents ix sp dsp
    | (Node sp) as dsp -> abstract_traverse traverse n parents ix sp dsp
  in
  fun n (`Subproof sp )->
    if n < 1 then
      invalid_arg "Subproof.nth_subgoal: no non-positive open goal"
    else
      traverse n [] 0 (Root sp) *)


(* This function changes the goal at a certain position *)
let mutate pos new_content =
  match pos.handle with
  | Root sp -> sp.node.(pos.index) <- new_content
  | Node sp -> sp.node.(pos.index) <- new_content


(* This function iters a function on all the subproofs of a proof node,
   except the node of the root *)
let iter f pn =
  let bpn = Node pn in
  Array.iteri (fun i -> f { handle=bpn ; index=i}) pn.node

(* This function iters a function on all the subproof of the root proof
   node *)
let root_iter f pn =
  let bpn = Root pn in
  Array.iteri (fun i -> f { handle=bpn ; index=i}) pn.node
*)
