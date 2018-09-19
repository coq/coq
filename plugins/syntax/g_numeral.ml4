(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

DECLARE PLUGIN "numeral_notation_plugin"

open Notation
open Numeral
open Pp
open Names
open Vernacinterp
open Ltac_plugin
open Stdarg
open Pcoq.Prim

let pr_numnot_option _ _ _ = function
  | Nop -> mt ()
  | Warning n -> str "(warning after " ++ str n ++ str ")"
  | Abstract n -> str "(abstract after " ++ str n ++ str ")"

ARGUMENT EXTEND numnotoption
  PRINTED BY pr_numnot_option
| [ ] -> [ Nop ]
| [ "(" "warning" "after" bigint(waft) ")" ] -> [ Warning waft ]
| [ "(" "abstract" "after" bigint(n) ")" ] -> [ Abstract n ]
END

VERNAC COMMAND EXTEND NumeralNotation CLASSIFIED AS SIDEFF
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) numnotoption(o) ] ->
    [ vernac_numeral_notation (Locality.make_module_locality atts.locality) ty f g (Id.to_string sc) o ]
END
