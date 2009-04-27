(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_macro.cmo" i*)

(* Compatibility file depending on ocaml version *)

IFDEF OCAML309 THEN DEFINE OCAML308 END

IFDEF CAMLP5 THEN 
module M = struct 
type loc = Stdpp.location
let dummy_loc = Stdpp.dummy_loc
let make_loc = Stdpp.make_loc
let unloc loc = Stdpp.first_pos loc, Stdpp.last_pos loc
let join_loc loc1 loc2 =
 if loc1 = dummy_loc or loc2 = dummy_loc then dummy_loc
 else Stdpp.encl_loc loc1 loc2
type token = string*string
type lexer = token Token.glexer
end
ELSE IFDEF OCAML308 THEN
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
let join_loc loc1 loc2 =
 if loc1 = dummy_loc or loc2 = dummy_loc then dummy_loc
 else (fst loc1, snd loc2) 
type token = Token.t
type lexer = Token.lexer
end
ELSE 
module M = struct
type loc = int * int
let dummy_loc = (0,0)
let make_loc x = x
let unloc x = x
let join_loc loc1 loc2 =
 if loc1 = dummy_loc or loc2 = dummy_loc then dummy_loc
 else (fst loc1, snd loc2)
type token = Token.t
type lexer = Token.lexer
end
END
END

type loc = M.loc
let dummy_loc = M.dummy_loc
let make_loc = M.make_loc
let unloc = M.unloc
let join_loc = M.join_loc
type token = M.token
type lexer = M.lexer
