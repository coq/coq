(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open General
open Dpctypes

exception Not_unifiable

val unif_atoms : atom_id * term list -> atom_id * term list 
                   -> (term * term) list
val unif_terms : term -> term -> (term * term) list

val assoc_unif : 'a -> ('a * 'a) list -> 'a
val apply_unif : (term * term) list -> term -> term
val appear_var_term : term -> term -> bool

exception Up_error

val up : (term * term) list -> (term * term) list -> (term * term) list

