(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(* $Id$ *)

open Pcoq
open Ptype
open Past

(* Grammar for the programs and the tactic Correctness *)

module Programs :
  sig
    val program : program Gram.Entry.e
    val type_v  : Coqast.t ml_type_v Gram.Entry.e
    val type_c  : Coqast.t ml_type_c Gram.Entry.e
  end

