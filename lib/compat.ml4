(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Compatibility file depending on ocaml version *)

(* IFDEF not available in 3.06; use ifdef instead *)

(* type loc is different in 3.08 *)
ifdef OCAML308 then
module M = struct
type loc = Token.flocation
let dummy_loc = Token.dummy_loc
let unloc (b,e) = (b.Lexing.pos_cnum,e.Lexing.pos_cnum)
let make_loc loc = Token.make_loc loc
end
else
module M = struct
type loc = int * int
let dummy_loc = (0,0)
let unloc x = x
let make_loc x = x
end

type loc = M.loc
let dummy_loc = M.dummy_loc
let unloc = M.unloc
let make_loc = M.make_loc
