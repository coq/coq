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

type work_list = Id.t array Cmap.t * Id.t array Mindmap.t
type cooking_info = { modlist : work_list; abstract : Context.named_context } 

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

type proofterm = (constr * Univ.constraints) Future.computation
type lazy_constr =
  (* subst, lib, index *)
  | Indirect of substitution list * DirPath.t * int
  (* opaque in section or interactive session *)
  | Direct of cooking_info list * (constr_substituted * Univ.constraints) Future.computation

(* TODO : this hcons function could probably be improved (for instance
   hash the dir_path in the Indirect case) *)

let subst_lazy_constr sub = function
  | Direct ([],cu) ->
      Direct ([],Future.chain ~greedy:true ~pure:true cu (fun (c, u) ->
        subst_constr_subst sub c, u))
  | Direct _ -> Errors.anomaly (Pp.str"still direct but not discharged")
  | Indirect (l,dp,i) -> Indirect (sub::l,dp,i)

let iter_direct_lazy_constr f = function
  | Indirect _ -> Errors.anomaly (Pp.str "iter_direct_lazy_constr")
  | Direct (d,cu) ->
      Direct (d, Future.chain ~greedy:true ~pure:true cu (fun (c, u) -> f (force c); c, u))

let discharge_direct_lazy_constr modlist abstract  f = function
  | Indirect _ -> Errors.anomaly (Pp.str "discharge_direct_lazy_constr")
  | Direct (d,cu) ->
      Direct ({ modlist; abstract }::d,
        Future.chain ~greedy:true ~pure:true cu (fun (c, u) ->
          from_val (f (force c)), u))

let default_get_opaque dp _ =
  Errors.error
    ("Cannot access opaque proofs in library " ^ DirPath.to_string dp)
let default_get_univ dp _ =
  Errors.error
    ("Cannot access universe constraints of opaque proofs in library " ^
    DirPath.to_string dp)

let default_mk_indirect _ = None

let default_join_indirect_local_opaque _ _ = ()
let default_join_indirect_local_univ _ _ = ()

let get_opaque = ref default_get_opaque
let get_univ = ref default_get_univ
let join_indirect_local_opaque = ref default_join_indirect_local_opaque
let join_indirect_local_univ = ref default_join_indirect_local_univ

let mk_indirect = ref default_mk_indirect
let set_indirect_opaque_accessor f = (get_opaque := f)
let set_indirect_univ_accessor f = (get_univ := f)
let set_indirect_creator f = (mk_indirect := f)
let set_join_indirect_local_opaque f = join_indirect_local_opaque := f
let set_join_indirect_local_univ f = join_indirect_local_univ := f

let reset_indirect_creator () = mk_indirect := default_mk_indirect

let force_lazy_constr = function
  | Direct (_,c) -> Future.force c
  | Indirect (l,dp,i) ->
      let c = Future.force (!get_opaque dp i) in
      List.fold_right subst_constr_subst l (from_val c),
      Future.force
        (Option.default
          (Future.from_val Univ.empty_constraint)
          (!get_univ dp i))

let join_lazy_constr = function
  | Direct (_,c) -> ignore(Future.force c)
  | Indirect (_,dp,i) ->
      !join_indirect_local_opaque dp i;
      !join_indirect_local_univ dp i

let turn_indirect lc = match lc with
  | Indirect _ ->
    Errors.anomaly (Pp.str "Indirecting an already indirect opaque")
  | Direct (d,cu) ->
    let cu = Future.chain ~greedy:true ~pure:true cu (fun (c,u) ->
      (* this constr_substituted shouldn't have been substituted yet *)
      assert (fst (Mod_subst.repr_substituted c) == None);
      hcons_constr (force c),u) in
    match !mk_indirect (d,cu) with
      | None -> lc
      | Some (dp,i) -> Indirect ([],dp,i)

let force_opaque lc =
  let c, _u = force_lazy_constr lc in force c
let force_opaque_w_constraints lc =
  let c, u = force_lazy_constr lc in force c, u
let get_opaque_future_constraints lc = match lc with
  | Indirect (_,dp,i) -> !get_univ dp i
  | Direct (_,cu) -> Some(snd (Future.split2 ~greedy:true cu))
let get_opaque_futures lc = match lc with
  | Indirect _ -> assert false
  | Direct (_,cu) ->
      let cu =
        Future.chain ~greedy:true ~pure:true cu (fun (c,u) -> force c, u) in
      Future.split2 ~greedy:true cu

let opaque_from_val cu =
  Direct ([],Future.chain ~greedy:true ~pure:true cu (fun (c,u) -> from_val c, u))
