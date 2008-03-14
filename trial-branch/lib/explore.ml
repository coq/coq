(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Format

(*s Definition of a search problem. *)

module type SearchProblem = sig
  type state
  val branching : state -> state list
  val success : state -> bool
  val pp : state -> unit
end

module Make = functor(S : SearchProblem) -> struct

  type position = int list

  let pp_position p = 
    let rec pp_rec = function
      | [] -> ()
      | [i] -> printf "%d" i
      | i :: l -> pp_rec l; printf ".%d" i
    in
    open_hbox (); pp_rec p; close_box ()

  (*s Depth first search. *)

  let rec depth_first s = 
    if S.success s then s else depth_first_many (S.branching s)
  and depth_first_many = function
    | [] -> raise Not_found
    | [s] -> depth_first s
    | s :: l -> try depth_first s with Not_found -> depth_first_many l

  let debug_depth_first s = 
    let rec explore p s =
      pp_position p; S.pp s;
      if S.success s then s else explore_many 1 p (S.branching s)
    and explore_many i p = function
      | [] -> raise Not_found
      | [s] -> explore (i::p) s
      | s :: l -> 
	  try explore (i::p) s with Not_found -> explore_many (succ i) p l
    in
    explore [1] s

  (*s Breadth first search. We use functional FIFOS à la Okasaki. *)

  type 'a queue = 'a list * 'a list

  exception Empty

  let empty = [],[]

  let push x (h,t) = (x::h,t)

  let pop = function
    | h, x::t -> x, (h,t)
    | h, [] -> match List.rev h with x::t -> x, ([],t) | [] -> raise Empty

  let breadth_first s = 
    let rec explore q =
      let (s, q') = try pop q with Empty -> raise Not_found in
      enqueue q' (S.branching s)
    and enqueue q = function
      | [] -> explore q
      | s :: l -> if S.success s then s else enqueue (push s q) l
    in
    enqueue empty [s]

  let debug_breadth_first s = 
    let rec explore q =
      let ((p,s), q') = try pop q with Empty -> raise Not_found in 
      enqueue 1 p q' (S.branching s)
    and enqueue i p q = function
      | [] -> 
	  explore q
      | s :: l ->
	  let ps = i::p in 
	  pp_position ps; S.pp s;
	  if S.success s then s else enqueue (succ i) p (push (ps,s) q) l
    in
    enqueue 1 [] empty [s]

end
