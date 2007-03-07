(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* ML names *)

open Vernacexpr
open Pcoq
open Genarg
open Pp

open Intextr

(* Internal extraction commands *)

VERNAC COMMAND EXTEND InternalExtraction
(* Internal extraction in the Coq toplevel *)
| [ "Internal" "Extraction" global(x) ] -> [ internal_extraction x ]
END
