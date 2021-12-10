(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp

(*s Definition of a search problem. *)

module type SearchProblem = sig
  type state
  val branching : state -> state list
  val success : state -> bool
  val pp : state -> Pp.t
end

module Make = functor(S : SearchProblem) -> struct

  type position = int list

  let msg_with_position (p : position) pp =
    let rec pp_rec = function
      | [] -> mt ()
      | [i] -> int i
      | i :: l -> pp_rec l ++ str "." ++ int i
    in
    Feedback.msg_debug (h (pp_rec p) ++ pp)

  (*s Depth first search. *)

  let rec depth_first s =
    if S.success s then s else depth_first_many (S.branching s)
  and depth_first_many = function
    | [] -> raise Not_found
    | [s] -> depth_first s
    | s :: l -> try depth_first s with Not_found -> depth_first_many l

  let debug_depth_first s =
    let rec explore p s =
      msg_with_position p (S.pp s);
      if S.success s then s else explore_many 1 p (S.branching s)
    and explore_many i p = function
      | [] -> raise Not_found
      | [s] -> explore (i::p) s
      | s :: l ->
          try explore (i::p) s with Not_found -> explore_many (succ i) p l
    in
    explore [1] s

end
