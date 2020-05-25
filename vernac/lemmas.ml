(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to lemma proofs in
   file command.ml, Aug 2009 *)

(************************************************************************)
(* Creating a lemma-like constant                                       *)
(************************************************************************)

(* Starting a goal *)
let start_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Declare.Info.make ()) ?(impargs=[]) sigma c =
  Declare.start_proof sigma ~name ~udecl ~poly ~impargs ~info c

(* Note that proofs opened by start_dependent lemma cannot be closed
   by the regular terminators, thus we don't need to update the [thms]
   field. We will capture this invariant by typing in the future *)
let start_dependent_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Declare.Info.make ()) telescope =
  Declare.start_dependent_proof ~name ~udecl ~poly ~info telescope
