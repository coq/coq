(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pcoq
open Ptype
open Past
open Topconstr

(* Grammar for the programs and the tactic Correctness *)

module Programs :
  sig
    val program : program Gram.Entry.e
    val type_v  : constr_expr ml_type_v Gram.Entry.e
    val type_c  : constr_expr ml_type_c Gram.Entry.e
  end
