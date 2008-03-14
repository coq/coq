(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id$ i*)

open Past
open Rawterm

(* On-the-fly generation of needed (possibly dependent) tuples. *)

val check_product_n : int -> unit
val check_dep_product_n : int -> unit

(* transforms intermediate functional programs into (raw) CIC terms *)

val rawconstr_of_prog : cc_term -> rawconstr

