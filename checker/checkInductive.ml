(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Environ
open Names
open Univ
open Util

[@@@ocaml.warning "+9+27"]

exception InductiveMismatch of MutInd.t * string

let check mind field b = if not b then raise (InductiveMismatch (mind,field))

let to_entry (mb:mutual_inductive_body) : Entries.mutual_inductive_entry =
  let open Entries in
  let nparams = List.length mb.mind_params_ctxt in (* include letins *)
  let mind_entry_record = match mb.mind_record with
    | NotRecord -> None | FakeRecord -> Some None
    | PrimRecord data -> Some (Some (Array.map (fun (x,_,_,_) -> x) data))
  in
  let mind_entry_universes = match mb.mind_universes with
    | Monomorphic univs -> Monomorphic_entry univs
    | Polymorphic auctx -> Polymorphic_entry (AUContext.names auctx, AUContext.repr auctx)
  in
  let mind_entry_inds = Array.map_to_list (fun ind ->
      let mind_entry_arity, mind_entry_template = match ind.mind_arity with
        | RegularArity ar ->
          let ctx, arity = Term.decompose_prod_n_assum nparams ar.mind_user_arity in
          ignore ctx; (* we will check that the produced user_arity is equal to the input *)
          arity, false
        | TemplateArity ar ->
          let ctx = ind.mind_arity_ctxt in
          let ctx = List.firstn (List.length ctx - nparams) ctx in
          Term.mkArity (ctx, Sorts.sort_of_univ ar.template_level), true
      in
      {
        mind_entry_typename = ind.mind_typename;
        mind_entry_arity;
        mind_entry_template;
        mind_entry_consnames = Array.to_list ind.mind_consnames;
        mind_entry_lc = Array.map_to_list (fun c ->
            let ctx, c = Term.decompose_prod_n_assum nparams c in
            ignore ctx; (* we will check that the produced user_lc is equal to the input *)
            c
          ) ind.mind_user_lc;
      })
      mb.mind_packets
  in
  {
    mind_entry_record;
    mind_entry_finite = mb.mind_finite;
    mind_entry_params = mb.mind_params_ctxt;
    mind_entry_inds;
    mind_entry_universes;
    mind_entry_variance = mb.mind_variance;
    mind_entry_private = mb.mind_private;
  }

let check_arity env ar1 ar2 = match ar1, ar2 with
  | RegularArity ar, RegularArity {mind_user_arity;mind_sort} ->
    Constr.equal ar.mind_user_arity mind_user_arity &&
    Sorts.equal ar.mind_sort mind_sort
  | TemplateArity ar, TemplateArity {template_param_levels;template_level} ->
    List.equal (Option.equal Univ.Level.equal) ar.template_param_levels template_param_levels &&
    UGraph.check_leq (universes env) template_level ar.template_level
    (* template_level is inferred by indtypes, so functor application can produce a smaller one *)
  | (RegularArity _ | TemplateArity _), _ -> false

let check_kelim k1 k2 = Sorts.family_leq k1 k2

(* Use [eq_ind_chk] because when we rebuild the recargs we have lost
   the knowledge of who is the canonical version.
   Try with to see test-suite/coqchk/include.v *)
let eq_recarg a1 a2 = match a1, a2 with
  | Norec, Norec -> true
  | Mrec i1, Mrec i2 -> eq_ind_chk i1 i2
  | Imbr i1, Imbr i2 -> eq_ind_chk i1 i2
  | (Norec | Mrec _ | Imbr _), _ -> false

let eq_reloc_tbl = Array.equal (fun x y -> Int.equal (fst x) (fst y) && Int.equal (snd x) (snd y))

let eq_in_context (ctx1, t1) (ctx2, t2) =
  Context.Rel.equal Constr.equal ctx1 ctx2 && Constr.equal t1 t2

let check_packet env mind ind
    { mind_typename; mind_arity_ctxt; mind_arity; mind_consnames; mind_user_lc;
      mind_nrealargs; mind_nrealdecls; mind_kelim; mind_nf_lc;
      mind_consnrealargs; mind_consnrealdecls; mind_recargs; mind_relevance;
      mind_nb_constant; mind_nb_args; mind_reloc_tbl } =
  let check = check mind in

  ignore mind_typename; (* passed through *)
  check "mind_arity_ctxt" (Context.Rel.equal Constr.equal ind.mind_arity_ctxt mind_arity_ctxt);
  check "mind_arity" (check_arity env ind.mind_arity mind_arity);
  ignore mind_consnames; (* passed through *)
  check "mind_user_lc" (Array.equal Constr.equal ind.mind_user_lc mind_user_lc);
  check "mind_nrealargs" Int.(equal ind.mind_nrealargs mind_nrealargs);
  check "mind_nrealdecls" Int.(equal ind.mind_nrealdecls mind_nrealdecls);
  check "mind_kelim" (check_kelim ind.mind_kelim mind_kelim);

  check "mind_nf_lc" (Array.equal eq_in_context ind.mind_nf_lc mind_nf_lc);
  (* NB: here syntactic equality is not just an optimisation, we also
     care about the shape of the terms *)

  check "mind_consnrealargs" (Array.equal Int.equal ind.mind_consnrealargs mind_consnrealargs);
  check "mind_consnrealdecls" (Array.equal Int.equal ind.mind_consnrealdecls mind_consnrealdecls);

  check "mind_recargs" (Rtree.equal eq_recarg ind.mind_recargs mind_recargs);

  check "mind_relevant" (Sorts.relevance_equal ind.mind_relevance mind_relevance);

  check "mind_nb_args" Int.(equal ind.mind_nb_args mind_nb_args);
  check "mind_nb_constant" Int.(equal ind.mind_nb_constant mind_nb_constant);
  check "mind_reloc_tbl" (eq_reloc_tbl ind.mind_reloc_tbl mind_reloc_tbl);

  ()

let check_same_record r1 r2 = match r1, r2 with
  | NotRecord, NotRecord | FakeRecord, FakeRecord -> true
  | PrimRecord r1, PrimRecord r2 ->
    (* The kernel doesn't care about the names, we just need to check
       that the saved types are correct. *)
    Array.for_all2 (fun (_,_,r1,tys1) (_,_,r2,tys2) ->
        Array.equal Sorts.relevance_equal r1 r2 &&
        Array.equal Constr.equal tys1 tys2)
      r1 r2
  | (NotRecord | FakeRecord | PrimRecord _), _ -> false

let check_inductive env mind mb =
  let entry = to_entry mb in
  let { mind_packets; mind_record; mind_finite; mind_ntypes; mind_hyps;
        mind_nparams; mind_nparams_rec; mind_params_ctxt;
        mind_universes; mind_variance;
        mind_private; mind_typing_flags; }
    =
    (* Locally set the oracle for further typechecking *)
    let env = Environ.set_oracle env mb.mind_typing_flags.conv_oracle in
    Indtypes.check_inductive env mind entry
  in
  let check = check mind in

  Array.iter2 (check_packet env mind) mb.mind_packets mind_packets;
  check "mind_record" (check_same_record mb.mind_record mind_record);
  check "mind_finite" (mb.mind_finite == mind_finite);
  check "mind_ntypes" Int.(equal mb.mind_ntypes mind_ntypes);
  check "mind_hyps" (Context.Named.equal Constr.equal mb.mind_hyps mind_hyps);
  check "mind_nparams" Int.(equal mb.mind_nparams mind_nparams);

  check "mind_nparams_rec" (mb.mind_nparams_rec <= mind_nparams_rec);
  (* module substitution can increase the real number of recursively
     uniform parameters, so be tolerant and use [<=]. *)

  check "mind_params_ctxt" (Context.Rel.equal Constr.equal mb.mind_params_ctxt mind_params_ctxt);
  ignore mind_universes; (* Indtypes did the necessary checking *)
  ignore mind_variance; (* Indtypes did the necessary checking *)
  ignore mind_private; (* passed through Indtypes *)

  ignore mind_typing_flags;
  (* TODO non oracle flags *)

  add_mind mind mb env
