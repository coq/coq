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

  let msg_with_position (p : position) s = match p with
  | [] -> ()
  | _ :: _ ->
    let pp = S.pp s in
    let rec pp_rec = function
      | [] -> mt ()
      | [i] -> int i
      | i :: l -> pp_rec l ++ str "." ++ int i
    in
    Feedback.msg_debug (h (pp_rec p) ++ pp)

  let push i p = match p with [] -> [] | _ :: _ -> i :: p

  let depth_first ?(debug=false) s =
    let rec explore p s =
      let () = msg_with_position p s in
      if S.success s then s else explore_many 1 p (S.branching s)
    and explore_many i p = function
      | [] -> raise Not_found
      | [s] -> explore (push i p) s
      | s :: l ->
          try explore (push i p) s with Not_found -> explore_many (succ i) p l
    in
    let pos = if debug then [1] else [] in
    explore pos s

end
