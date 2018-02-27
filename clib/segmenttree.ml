(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module is a very simple implementation of "segment trees".

    A segment tree of type ['a t] represents a mapping from a union of
    disjoint segments to some values of type 'a. 
*)

(** Misc. functions. *)
let list_iteri f l =
  let rec loop i = function
    | [] -> ()
    | x :: xs -> f i x; loop (i + 1) xs
  in
    loop 0 l

let log2 x = log x /. log 2.

let log2n x = int_of_float (ceil (log2 (float_of_int x))) 

(** We focus on integers but this module can be generalized. *)
type elt = int

(** A value of type [domain] is interpreted differently given its position 
    in the tree. On internal nodes, a domain represents the set of 
    integers which are _not_ in the set of keys handled by the tree. On 
    leaves, a domain represents the st of integers which are in the set of 
    keys. *)
type domain = 
    (** On internal nodes, a domain [Interval (a, b)] represents 
	the interval [a + 1; b - 1]. On leaves, it represents [a; b]. 
	We always have [a] <= [b]. *)
  | Interval of elt * elt
      (** On internal node or root, a domain [Universe] represents all
	  the integers. When the tree is not a trivial root,
	  [Universe] has no interpretation on leaves. (The lookup
	  function should never reach the leaves.) *)
  | Universe

(** We use an array to store the almost complete tree. This array
    contains at least one element. *)
type 'a t = (domain * 'a option) array

(** The root is the first item of the array. *)

(** Standard layout for left child. *)
let left_child i = 2 * i + 1

(** Standard layout for right child. *)
let right_child i = 2 * i + 2

(** Extract the annotation of a node, be it internal or a leaf. *)
let value_of i t = match t.(i) with (_, Some x) -> x | _ -> raise Not_found

(** Initialize the array to store [n] leaves. *)
let create n init = 
  Array.make (1 lsl (log2n n + 1) - 1) init

(** Make a complete interval tree from a list of disjoint segments. 
    Precondition : the segments must be sorted. *)
let make segments = 
  let nsegments = List.length segments in
  let tree = create nsegments (Universe, None) in 
  let leaves_offset = (1 lsl (log2n nsegments)) - 1 in

    (** The algorithm proceeds in two steps using an intermediate tree
	to store minimum and maximum of each subtree as annotation of
	the node. *)

    (** We start from leaves: the last level of the tree is initialized
	with the given segments... *)
    list_iteri 
      (fun i ((start, stop), value) ->
	 let k = leaves_offset + i in
	 let i = Interval (start, stop) in
	   tree.(k) <- (i, Some i))
      segments;
    (** ... the remaining leaves are initialized with neutral information. *)
    for k = leaves_offset + nsegments to Array.length tree -1 do 
      tree.(k) <- (Universe, Some Universe)
    done;
    
    (** We traverse the tree bottom-up and compute the interval and
	annotation associated to each node from the annotations of its
	children. *)
    for k = leaves_offset - 1 downto 0 do
      let node, annotation = 
	match value_of (left_child k) tree, value_of (right_child k) tree with
	  | Interval (left_min, left_max), Interval (right_min, right_max) ->
	      (Interval (left_max, right_min), Interval (left_min, right_max))
	  | Interval (min, max), Universe -> 
	      (Interval (max, max), Interval (min, max))
	  | Universe, Universe -> Universe, Universe
	  | Universe, _ -> assert false
      in
	tree.(k) <- (node, Some annotation)
    done;

    (** Finally, annotation are replaced with the image related to each leaf. *)
    let final_tree = 
      Array.mapi (fun i (segment, value) -> (segment, None)) tree
    in
      list_iteri 
	(fun i ((start, stop), value) -> 
	   final_tree.(leaves_offset + i) 
	   <- (Interval (start, stop), Some value))
	segments;      
      final_tree

(** [lookup k t] looks for an image for key [k] in the interval tree [t]. 
    Raise [Not_found] if it fails. *)
let lookup k t = 
  let i = ref 0 in 
    while (snd t.(!i) = None) do
      match fst t.(!i) with
	| Interval (start, stop) -> 
	    if k <= start then i := left_child !i
	    else if k >= stop then i:= right_child !i 
	    else raise Not_found
	| Universe -> raise Not_found
    done;
    match fst t.(!i) with
      | Interval (start, stop) -> 
	  if k >= start && k <= stop then
	    match snd t.(!i) with 
	      | Some v -> v
	      | None -> assert false
	  else 
	    raise Not_found
      | Universe -> assert false
      

