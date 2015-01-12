(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Names
open Ind_tables

(** This file is about the automatic generation of schemes about
    decidable equality,
    @author Vincent Siles
    Oct 2007 *)

(** {6 Build boolean equality of a block of mutual inductive types } *)

exception EqNotFound of inductive * inductive
exception EqUnknown of string
exception UndefinedCst of string
exception InductiveWithProduct
exception InductiveWithSort
exception ParameterWithoutEquality of constant
exception NonSingletonProp of inductive

val beq_scheme_kind : mutual scheme_kind
val build_beq_scheme : mutual_scheme_object_function

(** {6 Build equivalence between boolean equality and Leibniz equality } *)

val lb_scheme_kind : mutual scheme_kind
val make_lb_scheme : mutual_scheme_object_function
val bl_scheme_kind : mutual scheme_kind
val make_bl_scheme : mutual_scheme_object_function

(** {6 Build decidability of equality } *)

val eq_dec_scheme_kind : mutual scheme_kind
val make_eq_decidability : mutual_scheme_object_function
