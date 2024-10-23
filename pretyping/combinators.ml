(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Rocqlib
open CErrors
open Util
open Termops
open EConstr
open Retyping
open Typing
open Inductiveops

module RelDecl = Context.Rel.Declaration

(**************)
(** Telescope *)

type family = SPropF | PropF | TypeF
let family_of_sort_family = let open Sorts in function
    | InSProp -> SPropF
    | InProp -> PropF
    | InSet | InType | InQSort -> TypeF

let get_sigmatypes sigma ~sort ~predsort =
  let open EConstr in
  let which, sigsort = match predsort, sort with
    | SPropF, _ | _, SPropF ->
      user_err Pp.(str "SProp arguments not supported by Program Fixpoint yet.")
    | PropF, PropF -> "ex", PropF
    | PropF, TypeF -> "sig", TypeF
    | TypeF, (PropF|TypeF) -> "sigT", TypeF
  in
  let sigma, ty = Evd.fresh_global (Global.env ()) sigma (lib_ref ("core."^which^".type")) in
  let uinstance = snd (destRef sigma ty) in
  let intro = mkRef (lib_ref ("core."^which^".intro"), uinstance) in
  let p1 = mkRef (lib_ref ("core."^which^".proj1"), uinstance) in
  let p2 = mkRef (lib_ref ("core."^which^".proj2"), uinstance) in
  sigma, ty, intro, p1, p2, sigsort

let rec telescope sigma l =
  let open EConstr in
  let open Vars in
  match l with
  | [] -> assert false
  | [RelDecl.LocalAssum (n, t), _] ->
    sigma, t, [RelDecl.LocalDef (n, mkRel 1, t)], mkRel 1
  | (LocalAssum (n, t), tsort) :: tl ->
      let sigma, ty, _tysort, tys, (k, constr) =
        List.fold_left
          (fun (sigma, ty, tysort, tys, (k, constr)) (decl,sort) ->
            let t = RelDecl.get_type decl in
            let pred = mkLambda (RelDecl.get_annot decl, t, ty) in
            let sigma, ty, intro, p1, p2, sigsort = get_sigmatypes sigma ~predsort:tysort ~sort in
            let sigty = mkApp (ty, [|t; pred|]) in
            let intro = mkApp (intro, [|lift k t; lift k pred; mkRel k; constr|]) in
              (sigma, sigty, sigsort, (pred, p1, p2) :: tys, (succ k, intro)))
          (sigma, t, tsort, [], (2, mkRel 1)) tl
      in
      let sigma, last, subst = List.fold_right2
        (fun (pred,p1,p2) (decl,_) (sigma, prev, subst) ->
          let t = RelDecl.get_type decl in
          let proj1 = applist (p1, [t; pred; prev]) in
          let proj2 = applist (p2, [t; pred; prev]) in
            (sigma, lift 1 proj2, RelDecl.(LocalDef (get_annot decl, proj1, t) :: subst)))
        (List.rev tys) tl (sigma, mkRel 1, [])
      in sigma, ty, (LocalDef (n, last, t) :: subst), constr

  | (LocalDef (n, b, t), _) :: tl ->
    let sigma, ty, subst, term = telescope sigma tl in
    sigma, ty, (LocalDef (n, b, t) :: subst), lift 1 term

type telescope = {
  telescope_type : EConstr.types;
  telescope_value : EConstr.constr;
}

let telescope env sigma ctx =
  let ctx, _ = List.fold_right_map (fun d env ->
      let s = Retyping.get_sort_family_of env sigma (RelDecl.get_type d) in
      let env = EConstr.push_rel d env in
      (d, family_of_sort_family s), env) ctx env
  in
  let sigma, telescope_type, letcontext, telescope_value = telescope sigma ctx in
  sigma, letcontext, { telescope_type; telescope_value }

(****************************************************)
(** Closure of a term according to its dependencies *)

(* [make_tuple env sigma (rterm,rty) lind] assumes [lind] is the lesser
   index bound in [rty]

   Then it builds the term

     [(existT A P (mkRel lind) rterm)] of type [(sigT A P)]

   where [A] is the type of [mkRel lind] and [P] is [fun na:A => rty{1/lind}]
 *)

let make_tuple env sigma (rterm,rty) lind =
  assert (not (Vars.noccurn sigma lind rty));
  let sigdata = build_sigma_type () in
  let sigma, a = type_of ~refresh:true env sigma (mkRel lind) in
  let a = Tacred.simpl env sigma a in
  let na = Context.Rel.Declaration.get_annot (lookup_rel lind env) in
  (* We move [lind] to [1] and lift other rels > [lind] by 1 *)
  let rty = Vars.lift (1-lind) (Vars.liftn lind (lind+1) rty) in
  (* Now [lind] is [mkRel 1] and we abstract on (na:a) *)
  let p = mkLambda (na, a, rty) in
  let sigma, exist_term = Evd.fresh_global env sigma sigdata.intro in
  let sigma, sig_term = Evd.fresh_global env sigma sigdata.typ in
    sigma,
    (applist(exist_term,[a;p;(mkRel lind);rterm]),
     applist(sig_term,[a;p]))

(* check that the free-references of the type of [c] are contained in
   the free-references of the normal-form of that type. Strictly
   computing the exact set of free rels would require full
   normalization but this is not reasonable (e.g. in presence of
   records that contains proofs). We restrict ourself to a "simpl"
   normalization *)

let minimal_free_rels env sigma (c,cty) =
  let cty_rels = free_rels sigma cty in
  let cty' = Tacred.simpl env sigma cty in
  let rels' = free_rels sigma cty' in
  if Int.Set.subset cty_rels rels' then
    (cty,cty_rels)
  else
    (cty',rels')

(* Like the above, but recurse over all the rels found until there are
   no more rels to be found *)

let minimal_free_rels_rec env sigma =
  let rec minimalrec_free_rels_rec prev_rels (c,cty) =
    let (cty,direct_rels) = minimal_free_rels env sigma (c,cty) in
    let combined_rels = Int.Set.union prev_rels direct_rels in
    let folder rels i = snd (minimalrec_free_rels_rec rels (c, get_type_of env sigma (mkRel i)))
    in (cty, List.fold_left folder combined_rels (Int.Set.elements (Int.Set.diff direct_rels prev_rels)))
  in minimalrec_free_rels_rec Int.Set.empty

(** [sig_clausal_form siglen ty]

   Will explode [siglen] [sigT ]'s on [ty] (depending on the
   type of ty), and return:

   (1) a pattern, with meta-variables in it for various arguments,
       which, when the metavariables are replaced with appropriate
       terms, will have type [ty]

   (2) an integer, which is the last argument - the one which we just
       returned.

   (3) a pattern, for the type of that last meta

   (4) a typing for each patvar

   WARNING: No checking is done to make sure that the
            sigT's are actually there.
          - Only homogeneous pairs are built i.e. pairs where all the
   dependencies are of the same sort

   [sig_clausal_form] proceeds as follows: the default tuple is
   constructed by taking the tuple-type, exploding the first [tuplen]
   [sigT]'s, and replacing at each step the binder in the
   right-hand-type by a fresh metavariable. In addition, on the way
   back out, we will construct the pattern for the tuple which uses
   these meta-vars.

   This gives us a pattern, which we use to match against the type of
   [dflt]; if that fails, then against the S(TRONG)NF of that type.  If
   both fail, then we just cannot construct our tuple.  If one of
   those succeed, then we can construct our value easily - we just use
   the tuple-pattern.
 *)

let sig_clausal_form env sigma sort_of_ty siglen ty dflt =
  let sigdata = build_sigma_type () in
  let rec sigrec_clausal_form sigma siglen p_i =
    if Int.equal siglen 0 then
      (* is the default value typable with the expected type *)
      let dflt_typ = Retyping.get_type_of env sigma dflt in
      try
        let sigma = Evarconv.unify_leq_delay env sigma dflt_typ p_i in
        let sigma = Evarconv.solve_unif_constraints_with_heuristics env sigma in
        sigma, dflt
      with Evarconv.UnableToUnify _ ->
        user_err Pp.(str "Cannot solve a unification problem.")
    else
      let (a,p_i_minus_1) = match Reductionops.whd_beta_stack env sigma p_i with
        | (_sigT,[a;p]) -> (a, p)
        | _ -> anomaly ~label:"sig_clausal_form" (Pp.str "should be a sigma type.") in
      let sigma, ev = Evarutil.new_evar env sigma a in
      let rty = Reductionops.beta_applist sigma (p_i_minus_1,[ev]) in
      let sigma, tuple_tail = sigrec_clausal_form sigma (siglen-1) rty in
      if EConstr.isEvar sigma ev then
        (* This at least happens if what has been detected as a
           dependency is not one; use an evasive error message;
           even if the problem is upwards: unification should be
           tried in the first place in make_iterated_tuple instead
           of approximatively computing the free rels; then
           unsolved evars would mean not binding rel *)
        user_err Pp.(str "Cannot solve a unification problem.")
      else
        let sigma, exist_term = Evd.fresh_global env sigma sigdata.intro in
        sigma, applist(exist_term,[a;p_i_minus_1;ev;tuple_tail])
  in
  let sigma, scf = sigrec_clausal_form sigma siglen ty in
  sigma, Evarutil.nf_evar sigma scf

(** [make_iterated_tuple env sigma default c ctype] retruns

   To do this, we find the free (relative) references of the strong NF
   of [c]'s type, gather them together in left-to-right order
   (i.e. highest-numbered is farthest-left), and construct a big
   iterated pair out of it. This only works when the references are
   all themselves to members of [Set]s, because we use [sigT] to
   construct the tuple.

   Suppose now that our constructed tuple is of length [tuplen]. We
   need also to construct a default value for the other branches of
   the destructor. As default value, we take a tuple of the form

    [existT [xn]Pn ?n (... existT [x2]P2 ?2 (existT [x1]P1 ?1 term))]

   but for this we have to solve the following unification problem:

     typ = cty[i1/?1;...;in/?n]

   This is done by [sig_clausal_form].
 *)

let make_iterated_tuple env sigma ~default c cty =
  let (cty,rels) = minimal_free_rels_rec env sigma (c,cty) in
  let sort_of_cty = get_sort_of env sigma cty in
  let sorted_rels = Int.Set.elements rels in
  let sigma, (telescope_value, telescope_type) =
    List.fold_left (fun (sigma, t) -> make_tuple env sigma t) (sigma, (c,cty)) sorted_rels
  in
  assert (Vars.closed0 sigma telescope_type);
  let n = List.length sorted_rels in
  let sigma, dfltval = sig_clausal_form env sigma sort_of_cty n telescope_type default in
  sigma, { telescope_value; telescope_type }, dfltval

(** [make_selector env sigma dirn c ind special default]]
   constructs a case-split on [c] of type [ind], with the [dirn]-th
   branch giving [special], and all the rest giving [default]. *)

let make_selector env sigma ~pos ~special ~default c ctype =
  let IndType(indf,_) as indt =
    try find_rectype env sigma ctype
    with Not_found ->
       (* one can find Rel(k) in case of dependent constructors
          like T := c : (A:Set)A->T and a discrimination
          on (c bool true) = (c bool false)
          CP : changed assert false in a more informative error
       *)
      user_err
        Pp.(str "Cannot discriminate on inductive constructors with \
                 dependent types.") in
  let (ind, _),_ = dest_ind_family indf in
  let () = Tacred.check_privacy env ind in
  let typ = Retyping.get_type_of env sigma default in
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let deparsign = make_arity_signature env sigma true indf in
  let p = it_mkLambda_or_LetIn typ deparsign in
  let cstrs = get_constructors env indf in
  let build_branch i =
    let endpt = if Int.equal i pos then special else default in
    let args = cstrs.(i-1).cs_args in
    it_mkLambda_or_LetIn endpt args in
  let brl =
    List.map build_branch(List.interval 1 (Array.length mip.mind_consnames)) in
  let rci = ERelevance.relevant in (* TODO relevance *)
  let ci = make_case_info env ind RegularStyle in
  Inductiveops.make_case_or_project env sigma indt ci (p, rci) c (Array.of_list brl)
