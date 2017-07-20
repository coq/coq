(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Warning, this file should respect the dependency order established
   in Coq. To see such order issue the comand:

   ```
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done && echo -e "\n## highparsing files" && cat parsing/highparsing.mllib' > API/link
   ```

   Note however that files in intf/ are located manually now as their
   conceptual linking order in the Coq codebase is incorrect (but it
   works due to these files being implementation-free.

   See below in the file for their concrete position.
*)

open Pretyping_API

(************************************************************************)
(* Modules from stm/                                                    *)
(************************************************************************)

module Vernac_classifier :
sig
  val declare_vernac_classifier :
    Vernacexpr.extend_name -> (Genarg.raw_generic_argument list -> unit -> Vernacexpr.vernac_classification) -> unit
  val classify_as_proofstep : Vernacexpr.vernac_classification
  val classify_as_query : Vernacexpr.vernac_classification
  val classify_as_sideeff : Vernacexpr.vernac_classification
  val classify_vernac : Vernacexpr.vernac_expr -> Vernacexpr.vernac_classification
end

(************************************************************************)
(* End of modules from stm/                                             *)
(************************************************************************)
