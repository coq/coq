(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util

type 'a t = string

(** Entries are registered with a unique name *)

let entries = ref String.Set.empty

let create name =
  let () =
    if String.Set.mem name !entries then
    anomaly (Pp.str ("Entry " ^ name ^ " already defined"))
  in
  let () = entries := String.Set.add name !entries in
  name

let unsafe_of_name name =
  assert (String.Set.mem name !entries);
  name

let repr s = s
