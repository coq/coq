(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * Finite sets library *)

(** This module proves many properties of finite sets that 
    are consequences of the axiomatization in [FsetInterface] 
    Contrary to the functor in [FsetWeakProperties] it uses 
    sets operations instead of predicates over sets, i.e.
    [mem x s=true] instead of [In x s], 
    [equal s s'=true] instead of [Equal s s'], etc. *)

Require Import FSetProperties Zerob Sumbool Omega DecidableTypeEx.

(** Since the properties that used to be there do not depend on 
    the element ordering, we now simply import them from 
    FSetWeakEqProperties *)

Require FSetWeakEqProperties.

Module EqProperties (M:S).
  Module D := OT_as_DT M.E.
  Include FSetWeakEqProperties.EqProperties M D.
End EqProperties.
