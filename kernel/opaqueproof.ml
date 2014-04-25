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
type proofterm = (constr * Univ.constraints) Future.computation
type opaque =
  | Indirect of substitution list * DirPath.t * int (* subst, lib, index *)
  | Direct of cooking_info list * proofterm
  | NoIndirect of substitution list * proofterm

(* hooks *)
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
(* /hooks *)

let create cu = Direct ([],cu)

let turn_indirect o = match o with
  | Indirect _
  | NoIndirect _ -> Errors.anomaly (Pp.str "Already an indirect opaque")
  | Direct (d,cu) ->
      let cu = Future.chain ~pure:true cu (fun (c, u) -> hcons_constr c, u) in
      match !mk_indirect (d,cu) with
      | None -> Future.sink cu; NoIndirect([],cu)
      | Some (dp,i) -> Indirect ([],dp,i)

let subst_opaque sub = function
  | Indirect (s,dp,i) -> Indirect (sub::s,dp,i)
  | NoIndirect (s,uc) -> NoIndirect (sub::s,uc)
  | Direct _ -> Errors.anomaly (Pp.str "Substituting a Direct opaque")

let iter_direct_opaque f = function
  | Indirect _
  | NoIndirect _ -> Errors.anomaly (Pp.str "Not a direct opaque")
  | Direct (d,cu) ->
      Direct (d,Future.chain ~pure:true cu (fun (c, u) -> f c; c, u))

let discharge_direct_opaque ~cook_constr ci = function
  | Indirect _
  | NoIndirect _ -> Errors.anomaly (Pp.str "Not a direct opaque")
  | Direct (d,cu) ->
      Direct (ci::d,Future.chain ~pure:true cu (fun (c, u) -> cook_constr c, u))

let join_opaque = function
  | Direct (_,cu) -> ignore(Future.join cu)
  | NoIndirect (_,cu) -> ignore(Future.join cu)
  | Indirect (_,dp,i) ->
      !join_indirect_local_opaque dp i;
      !join_indirect_local_univ dp i

let force_proof = function
  | Direct (_,cu) ->
      fst(Future.force cu)
  | NoIndirect (l,cu) ->
      let c, _ = Future.force cu in
      force_constr (List.fold_right subst_substituted l (from_val c))
  | Indirect (l,dp,i) ->
      let c = Future.force (!get_opaque dp i) in
      force_constr (List.fold_right subst_substituted l (from_val c))

let force_constraints = function
  | Direct (_,cu)
  | NoIndirect(_,cu) -> snd(Future.force cu)
  | Indirect (_,dp,i) ->
      match !get_univ dp i with
      | None -> Univ.empty_constraint
      | Some u -> Future.force u

let get_constraints = function
  | Direct (_,cu)
  | NoIndirect(_,cu) -> Some(Future.chain ~pure:true cu snd)
  | Indirect (_,dp,i) -> !get_univ dp i

let get_proof = function
  | Direct (_,cu) -> Future.chain ~pure:true cu fst
  | NoIndirect(l,cu) ->
      Future.chain ~pure:true cu (fun (c,_) ->
        force_constr (List.fold_right subst_substituted l (from_val c)))
  | Indirect (l,dp,i) ->
      Future.chain ~pure:true (!get_opaque dp i) (fun c ->
        force_constr (List.fold_right subst_substituted l (from_val c)))
