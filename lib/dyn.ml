(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util

(* Dynamics, programmed with DANGER !!! *)

type t = string * Obj.t

let dyntab = ref ([] : string list)

let create s =
  if List.mem s !dyntab then
    anomaly ("Dyn.create: already declared dynamic " ^ s);
  dyntab := s :: !dyntab;
  ((fun v -> (s,Obj.repr v)),
   (fun (s',rv) ->
      if s = s' then Obj.magic rv else failwith "dyn_out"))

let tag (s,_) = s
