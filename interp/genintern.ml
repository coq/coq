(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Mod_subst
open Genarg

type glob_sign = {
  ltacvars : Id.Set.t;
  ltacrecvars : Nametab.ltac_constant Id.Map.t;
  genv : Environ.env }

type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb
type 'glb subst_fun = substitution -> 'glb -> 'glb

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

module Intern = Register (InternObj)
module Subst = Register (SubstObj)

let intern = Intern.obj
let register_intern0 = Intern.register0

let generic_intern ist v =
  let unpacker wit v =
    let (ist, v) = intern wit ist (raw v) in
    (ist, in_gen (glbwit wit) v)
  in
  unpack { unpacker; } v

(** Substitution functions *)

let substitute = Subst.obj
let register_subst0 = Subst.register0

let generic_substitute subs v =
  let unpacker wit v = in_gen (glbwit wit) (substitute wit subs (glb v)) in
  unpack { unpacker; } v

let () = Hook.set Detyping.subst_genarg_hook generic_substitute
