(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(* $Id$ *)

open Term
open Past

(* reduction on intermediate programs 
 * get rid of redexes of the kind let (x1,...,xn) = e in (x1,...,xn) *)

val red : cc_term -> cc_term


(* Ad-hoc reduction on partial proof terms *)

val red_cci : constr -> constr


