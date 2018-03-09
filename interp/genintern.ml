(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Mod_subst
open Genarg

module Store = Store.Make ()

type glob_sign = {
  ltacvars : Id.Set.t;
  genv : Environ.env;
  extra : Store.t;
}

let empty_glob_sign env = {
  ltacvars = Id.Set.empty;
  genv = env;
  extra = Store.empty;
}

type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb
type 'glb subst_fun = substitution -> 'glb -> 'glb
type 'glb ntn_subst_fun = Tactypes.glob_constr_and_expr Id.Map.t -> 'glb -> 'glb

module InternObj =
struct
  type ('raw, 'glb, 'top) obj = ('raw, 'glb) intern_fun
  let name = "intern"
  let default _ = None
end

module SubstObj =
struct
  type ('raw, 'glb, 'top) obj = 'glb subst_fun
  let name = "subst"
  let default _ = None
end

module NtnSubstObj =
struct
  type ('raw, 'glb, 'top) obj = 'glb ntn_subst_fun
  let name = "notation_subst"
  let default _ = None
end

module Intern = Register (InternObj)
module Subst = Register (SubstObj)
module NtnSubst = Register (NtnSubstObj)

let intern = Intern.obj
let register_intern0 = Intern.register0

let generic_intern ist (GenArg (Rawwit wit, v)) =
  let (ist, v) = intern wit ist v in
  (ist, in_gen (glbwit wit) v)

(* Useful to have this available already outside Ltac *)
let (intern_open_constr_forward, intern_open_constr_hook) = Hook.make ()

(** Substitution functions *)

let substitute = Subst.obj
let register_subst0 = Subst.register0

let generic_substitute subs (GenArg (Glbwit wit, v)) =
  in_gen (glbwit wit) (substitute wit subs v)

let () = Hook.set Detyping.subst_genarg_hook generic_substitute

(* Useful to have this available already outside Ltac *)
let (subst_open_constr_forward, subst_open_constr_hook) = Hook.make ()

(** Notation substitution *)

let substitute_notation = NtnSubst.obj
let register_ntn_subst0 = NtnSubst.register0

let generic_substitute_notation env (GenArg (Glbwit wit, v)) =
  let v = substitute_notation wit env v in
  in_gen (glbwit wit) v
