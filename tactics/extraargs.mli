(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Tacexpr
open Term
open Names
open Proof_type
open Topconstr
open Rawterm

val rawwit_orient : bool raw_abstract_argument_type
val wit_orient : bool closed_abstract_argument_type
val orient : bool Pcoq.Gram.Entry.e

val rawwit_raw : constr_expr raw_abstract_argument_type
val wit_raw : rawconstr closed_abstract_argument_type
val raw : constr_expr Pcoq.Gram.Entry.e

type 'id gen_place= ('id * hyp_location_flag,unit) location

type loc_place = identifier Util.located gen_place
type place = identifier gen_place

val rawwit_hloc : loc_place raw_abstract_argument_type
val wit_hloc : place closed_abstract_argument_type
val hloc : loc_place Pcoq.Gram.Entry.e

