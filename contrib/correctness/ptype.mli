(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(* Generated automatically by ocamlc -i *)

type 'a precondition = { p_assert: bool; p_name: Names.name; p_value: 'a }
type 'a assertion = { a_name: Names.name; a_value: 'a }
type 'a postcondition = 'a assertion 
type predicate = Term.constr assertion
type 'a binder_type = | BindType of 'a | BindSet | Untyped
type 'a binder = Names.identifier * 'a binder_type
type variant = Term.constr * Term.constr * Term.constr
type 'a ml_type_v =
  | Ref of 'a ml_type_v
  | Array of 'a * 'a ml_type_v
  | Arrow of 'a ml_type_v binder list * 'a ml_type_c
  | TypePure of 'a
and 'a ml_type_c =
  (Names.identifier * 'a ml_type_v) * Peffect.t * 'a precondition list *
  'a postcondition option
type type_v = Term.constr ml_type_v
type type_c = Term.constr ml_type_c
val is_mutable : 'a ml_type_v -> bool
val is_pure : 'a ml_type_v -> bool
