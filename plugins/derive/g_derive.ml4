(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma"  i*)

let classify_derive_command _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]),VtLater)

VERNAC COMMAND EXTEND Derive CLASSIFIED BY classify_derive_command
| [ "Derive" ident(f) "SuchThat" constr(suchthat) "As" ident(lemma) ] ->
     [ Derive.start_deriving f suchthat lemma ]
END
