(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma"  i*)

(* arnaud: on a sans doute besoin des noms dans la liste. *)
(* arnaud: est-ce que VtNow signifie bien qu'on ne peut pas skipper la preuve? *)
let classify_derive_command _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]),VtNow)

VERNAC COMMAND EXTEND Derive CLASSIFIED BY classify_derive_command
| [ "Derive" ident(f) "From" constr(init) "Upto" constr(r) "As" ident(lemma) ] ->
     [ Derive.start_deriving f init r lemma ]
END
