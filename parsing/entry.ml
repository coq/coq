(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util

type 'a t = string * string

type repr =
| Static of string * string
| Dynamic of string

type universe = string

(* The univ_tab is not part of the state. It contains all the grammars that
   exist or have existed before in the session. *)

let univ_tab = (Hashtbl.create 7 : (string, unit) Hashtbl.t)

let create_univ s =
  Hashtbl.add univ_tab s (); s

let univ_name s = s

let uprim   = create_univ "prim"
let uconstr = create_univ "constr"
let utactic = create_univ "tactic"
let uvernac = create_univ "vernac"

let get_univ s =
  try
    Hashtbl.find univ_tab s; s
  with Not_found ->
    anomaly (Pp.str ("Unknown grammar universe: "^s))

(** Entries are registered with a unique name *)

let entries = ref String.Set.empty

let create u name =
  let uname = u ^ ":" ^ name in
  let () =
    if String.Set.mem uname !entries then
    anomaly (Pp.str ("Entry " ^ uname ^ " already defined"))
  in
  let () = entries := String.Set.add uname !entries in
  (u, name)

let dynamic name = ("", name)

let unsafe_of_name (u, s) =
  let uname = u ^ ":" ^ s in
  assert (String.Set.mem uname !entries);
  (u, s)

let repr = function
| ("", u) -> Dynamic u
| (u, s) -> Static (u, s)
