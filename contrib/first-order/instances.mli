(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Term
open Tacmach
open Names
open Libnames
open Rules
  
val collect_quantified : Sequent.t -> Formula.t list * Sequent.t

val quantified_tac : Formula.t list -> seqtac




