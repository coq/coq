
(* $Id$ *)

open Names
open Univ
open Generic
open Term
open Sign

type lazy_constant_value =
  | Cooked of constr
  | Recipe of (unit -> constr)

type constant_value = lazy_constant_value ref

type constant_body = {
  const_kind : path_kind;
  const_body : constant_value option;
  const_type : typed_type;
  const_hyps : typed_type signature;
  const_constraints : constraints;
  mutable const_opaque : bool }

let is_defined cb = 
  match cb.const_body with Some _ -> true | _ -> false

let is_opaque cb = cb.const_opaque

let cook_constant = function
  | { contents = Cooked c } -> c
  | { contents = Recipe f } as v -> let c = f () in v := Cooked c; c

type constant_entry = {
  const_entry_body : lazy_constant_value;
  const_entry_type : constr option }

