(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Mod_subst

(** [constr_substituted] are [constr] with possibly pending
    substitutions of kernel names. *)

type constr_substituted = constr substituted

let from_val = from_val

let force = force subst_mps

let subst_constr_subst = subst_substituted

(** Opaque proof terms might be in some external tables.
    The [force_opaque] function below allows to access these tables,
    this might trigger the read of some extra parts of .vo files.
    In the [Indirect] case, we accumulate "manually" a substitution
    list, the younger one coming first. Nota: no [Direct] constructor
    should end in a .vo, this is checked by coqchk.
*)

type lazy_constr =
  | Indirect of substitution list * DirPath.t * int (* lib,index *)
  | Direct of constr_substituted (* opaque in section or interactive session *)

(* TODO : this hcons function could probably be improved (for instance
   hash the dir_path in the Indirect case) *)

let hcons_lazy_constr = function
  | Direct c -> Direct (from_val (hcons_constr (force c)))
  | Indirect _ as lc -> lc

let subst_lazy_constr sub = function
  | Direct cs -> Direct (subst_constr_subst sub cs)
  | Indirect (l,dp,i) -> Indirect (sub::l,dp,i)

let default_get_opaque dp _ =
  Errors.error
    ("Cannot access an opaque term in library " ^ DirPath.to_string dp)

let default_mk_opaque _ = None

let get_opaque = ref default_get_opaque
let mk_opaque = ref default_mk_opaque
let set_indirect_opaque_accessor f = (get_opaque := f)
let set_indirect_opaque_creator f = (mk_opaque := f)
let reset_indirect_opaque_creator () = (mk_opaque := default_mk_opaque)

let force_lazy_constr = function
  | Direct c -> c
  | Indirect (l,dp,i) ->
    List.fold_right subst_constr_subst l (from_val (!get_opaque dp i))

let turn_indirect lc = match lc with
  | Indirect _ ->
    Errors.anomaly (Pp.str "Indirecting an already indirect opaque")
  | Direct c ->
    (* this constr_substituted shouldn't have been substituted yet *)
    assert (fst (Mod_subst.repr_substituted c) == None);
    match !mk_opaque (force c) with
      | None -> lc
      | Some (dp,i) -> Indirect ([],dp,i)

let force_opaque lc = force (force_lazy_constr lc)

let opaque_from_val c = Direct (from_val c)
