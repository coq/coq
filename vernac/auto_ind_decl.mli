(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Ind_tables

(** This file is about the automatic generation of schemes about
    decidable equality,
    @author Vincent Siles
    Oct 2007 *)

(** {6 Build boolean equality of a block of mutual inductive types } *)

exception EqNotFound of inductive
exception EqUnknown of string
exception UndefinedCst of string
exception InductiveWithProduct
exception InductiveWithSort
exception ParameterWithoutEquality of GlobRef.t
exception NonSingletonProp of inductive
exception DecidabilityMutualNotSupported
exception NoDecidabilityCoInductive
exception ConstructorWithNonParametricInductiveType of inductive
exception DecidabilityIndicesNotSupported
exception InternalDependencies

val beq_scheme_kind : mutual scheme_kind

(** {6 Build decidability of equality } *)

val eq_dec_scheme_kind : mutual scheme_kind
