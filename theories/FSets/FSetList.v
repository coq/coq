(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Finite sets library *)

(** This file proposes an implementation of the non-dependant
    interface [FSetInterface.S] using strictly ordered list. *)

Require Export FSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.

(** This is just a compatibility layer, the real implementation
    is now in [MSetList] *)

Require FSetCompat MSetList Orders OrdersAlt.

Module Make (X: OrderedType) <: S with Module E := X.
 Module X' := OrdersAlt.Update_OT X.
 Module MSet := MSetList.Make X'.
 Include FSetCompat.Backport_Sets X MSet.
End Make.
