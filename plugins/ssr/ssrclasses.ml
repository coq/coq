(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compatibility layer for [under] and [setoid_rewrite]; see [ssrclasses.v]. *)

(* Clone of [Rewrite.find_global] not using [Coqlib.find_reference] (deprec.) *)
let find_global s =
  let gr = lazy (Coqlib.lib_ref s) in
    fun (evd,cstrs) ->
      let (evd, c) = Evarutil.new_global evd (Lazy.force gr) in
        (evd, cstrs), c

(* Copy of [Rewrite.app_poly_check] *)
let app_poly_check env evars f args =
  let (evars, cstrs), fc = f evars in
  let evars, t = Typing.solve_evars env evars (EConstr.mkApp (fc, args)) in
  (evars, cstrs), t

(* Copy of [Rewrite.goalevars], [Rewrite.cstrevars] *)
let goalevars evars = fst evars
let cstrevars evars = snd evars

(* Copy of [Rewrite.extends_undefined] *)
let extends_undefined evars evars' =
  let f ev evi found = found || not (Evd.mem evars ev)
  in Evd.fold_undefined f evars' false

(* Copy of [Rewrite.find_class_proof] *)
let find_class_proof proof_type proof_method env evars carrier relation =
  try
    let evars, goal = app_poly_check env evars proof_type [| carrier ; relation |] in
    let evars', c = Typeclasses.resolve_one_typeclass env (goalevars evars) goal in
      if extends_undefined (goalevars evars) evars' then raise Not_found
      else app_poly_check env (evars',cstrevars evars) proof_method [| carrier; relation; c |]
  with e when Logic.catchable_exception e -> raise Not_found

(* Copy of [Rewrite.get_lemma_proof *)
let get_lemma_proof f env evm x y =
  let (evm, _), c = f env (evm,Evar.Set.empty) x y in
    evm, c

(* Clone of [Rewrite.PropGlobal.get_reflexive_proof] *)
let get_reflexive_proof_aux env =
  let reflexive_type = find_global "plugins.ssreflect.reflexive_type" in
  let reflexive_proof = find_global "plugins.ssreflect.reflexive_proof" in
  find_class_proof reflexive_type reflexive_proof env

(* Clone of [Rewrite.get_reflexive_proof],
   using [Coq.ssr.ssrclasses.Reflexive]
   instead of [Coq.Classes.RelationClasses.Reflexive] *)
let get_reflexive_proof_ssr =
  get_lemma_proof get_reflexive_proof_aux
