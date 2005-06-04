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
ifdef OCAML_308 then
module M = struct
type loc = Token.flocation
let dummy_loc = Token.dummy_loc
let make_loc loc = Token.make_loc loc
let unloc (b,e) =
  let loc = (b.Lexing.pos_cnum,e.Lexing.pos_cnum) in
  (* Ensure that we unpack a char location that was encoded as a line-col
     location by make_loc *)
(* Gram.Entry.parse may send bad loc in 3.08, see caml-bugs #2954
  assert (dummy_loc = (b,e) or make_loc loc = (b,e));
*)
  loc
end
else
module M = struct
type loc = int * int
let dummy_loc = (0,0)
let make_loc x = x
let unloc x = x
end

type loc = M.loc
let dummy_loc = M.dummy_loc
let unloc = M.unloc
let make_loc = M.make_loc
