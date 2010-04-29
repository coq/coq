(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Finite sets library *)

(** This file proposes an implementation of the non-dependant
    interface [FSetInterface.WS] using lists without redundancy. *)

Require Import FSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.

(** This is just a compatibility layer, the real implementation
    is now in [MSetWeakList] *)

Require Equalities FSetCompat MSetWeakList.

Module Make (X: DecidableType) <: WS with Module E := X.
 Module E := X.
 Module X' := Equalities.Update_DT X.
 Module MSet := MSetWeakList.Make X'.
 Include FSetCompat.Backport_WSets X MSet.
End Make.
