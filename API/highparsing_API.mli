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
open Parsing_API

(************************************************************************)
(* Modules from highparsing/                                            *)
(************************************************************************)

module G_vernac :
sig

  val def_body : Vernacexpr.definition_expr Pcoq.Gram.entry
  val section_subset_expr : Vernacexpr.section_subset_expr Pcoq.Gram.entry
  val query_command : (Vernacexpr.goal_selector option -> Vernacexpr.vernac_expr) Pcoq.Gram.entry

end

module G_proofs :
sig

  val hint : Vernacexpr.hints_expr Pcoq.Gram.entry
  val hint_proof_using : 'a Pcoq.Gram.entry -> 'a option -> 'a option

end

(************************************************************************)
(* End of modules from highparsing/                                     *)
(************************************************************************)
