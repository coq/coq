(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_macro.cmo" i*)

(* Compatibility file depending on ocaml version *)

IFDEF CAMLP5 THEN

type loc = Stdpp.location
let dummy_loc = Stdpp.dummy_loc
let make_loc = Stdpp.make_loc
let unloc loc = Stdpp.first_pos loc, Stdpp.last_pos loc
let join_loc loc1 loc2 =
 if loc1 = dummy_loc or loc2 = dummy_loc then dummy_loc
 else Stdpp.encl_loc loc1 loc2
type token = string*string
type lexer = token Token.glexer

ELSE (* official camlp4 of ocaml >= 3.10 *)

TODO

END
