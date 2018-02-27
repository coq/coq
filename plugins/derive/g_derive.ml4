(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Stdarg

DECLARE PLUGIN "derive_plugin"

let classify_derive_command _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]),VtLater)

VERNAC COMMAND EXTEND Derive CLASSIFIED BY classify_derive_command
| [ "Derive" ident(f) "SuchThat" constr(suchthat) "As" ident(lemma) ] ->
     [ Derive.start_deriving f suchthat lemma ]
END
