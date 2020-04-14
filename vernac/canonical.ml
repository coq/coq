(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Names
open Libobject
open Recordops

let open_canonical_structure i (_, (o,_)) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if Int.equal i 1 then register_canonical_structure env sigma ~warn:false o

let cache_canonical_structure (_, (o,_)) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  register_canonical_structure ~warn:true env sigma o

let discharge_canonical_structure (_,((gref, _ as x), local)) =
  if local || (Globnames.isVarRef gref && Lib.is_in_section gref) then None
  else Some (x, local)


let inCanonStruc : (GlobRef.t * inductive) * bool -> obj =
  declare_object {(default_object "CANONICAL-STRUCTURE") with
                  open_function = simple_open open_canonical_structure;
                  cache_function = cache_canonical_structure;
                  subst_function = (fun (subst,(c,local)) -> subst_canonical_structure subst c, local);
                  classify_function = (fun x -> Substitute x);
                  discharge_function = discharge_canonical_structure }

let add_canonical_structure x = Lib.add_anonymous_leaf (inCanonStruc x)

let declare_canonical_structure ?(local=false) ref =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  add_canonical_structure (check_and_decompose_canonical_structure env sigma ref, local)
