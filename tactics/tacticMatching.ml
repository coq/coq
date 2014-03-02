(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file extends Matching with the main logic for Ltac's
    (lazy)match and (lazy)match goal. *)

open Names
open Tacexpr

(** [t] is the type of matching successes. It ultimately contains a
    {!Tacexpr.glob_tactic_expr} representing the left-hand side of the
    corresponding matching rule, a matching substitution to be
    applied, a context substitution mapping identifier to context like
    those of {!Matching.matching_result}), and a {!Term.constr}
    substitution mapping corresponding to matched hypotheses. *)
type 'a t = {
  subst : ConstrMatching.bound_ident_map * Pattern.extended_patvar_map ;
  context : Term.constr Id.Map.t;
  terms : Term.constr Id.Map.t;
  lhs : 'a;
}



(** {6 Utilities} *)


(** Some of the functions of {!Matching} return the substitution with a
    [patvar_map] instead of an [extended_patvar_map]. [adjust] coerces
    substitution of the former type to the latter. *)
let adjust : ConstrMatching.bound_ident_map * Pattern.patvar_map ->
             ConstrMatching.bound_ident_map * Pattern.extended_patvar_map =
  fun (l, lc) -> (l, Id.Map.map (fun c -> [], c) lc)


(** Adds a binding to a {!Id.Map.t} if the identifier is [Some id] *)
let id_map_try_add id x m =
  match id with
  | Some id -> Id.Map.add id x m
  | None -> m

(** Adds a binding to a {!Id.Map.t} if the name is [Name id] *)
let id_map_try_add_name id x m =
  match id with
  | Name id -> Id.Map.add id x m
  | Anonymous -> m

(** Takes the union of two {!Id.Map.t}. If there is conflict,
    the binding of the right-hand argument shadows that of the left-hand
    argument. *)
let id_map_right_biased_union m1 m2 =
  if Id.Map.is_empty m1 then m2 (** Don't reconstruct the whole map *)
  else Id.Map.fold Id.Map.add m2 m1

(** Tests whether the substitution [s] is empty. *)
let is_empty_subst (ln,lm) =
  Id.Map.(is_empty ln && is_empty lm)

(** {6 Non-linear patterns} *)


(** The patterns of Ltac are not necessarily linear. Non-linear
    pattern are partially handled by the {!Matching} module, however
    goal patterns are not primitive to {!Matching}, hence we must deal
    with non-linearity between hypotheses and conclusion. Subterms are
    considered equal up to the equality implemented in
    [equal_instances]. *)
(* spiwack: it doesn't seem to be quite the same rule for non-linear
   term patterns and non-linearity between hypotheses and/or
   conclusion. Indeed, in [Matching], matching is made modulo
   syntactic equality, and here we merge modulo conversion. It may be
   a good idea to have an entry point of [Matching] with a partial
   substitution as argument instead of merging substitution here. That
   would ensure consistency. *)
let equal_instances env sigma (ctx',c') (ctx,c) =
  (* How to compare instances? Do we want the terms to be convertible?
     unifiable? Do we want the universe levels to be relevant? 
     (historically, conv_x is used) *)
  CList.equal Id.equal ctx ctx' && Reductionops.is_conv env sigma c' c


(** Merges two substitutions. Raises [Not_coherent_metas] when
    encountering two instances of the same metavariable which are not
    equal according to {!equal_instances}. *)
exception Not_coherent_metas
let verify_metas_coherence env sigma (ln1,lcm) (ln,lm) =
  let merge id oc1 oc2 = match oc1, oc2 with
    | None, None -> None
    | None, Some c | Some c, None -> Some c
    | Some c1, Some c2 ->
        if equal_instances env sigma c1 c2 then Some c1
        else raise Not_coherent_metas
  in
  let (+++) lfun1 lfun2 = Id.Map.fold Id.Map.add lfun1 lfun2 in
  (** ppedrot: Is that even correct? *)
  let merged = ln +++ ln1 in
  (merged, Id.Map.merge merge lcm lm)


(** A functor is introduced to share the environment and the
    evar_map. They do not change and it would be a pity to introduce
    closures everywhere just for the occasional calls to
    {!equal_instances}. *)
module type StaticEnvironment = sig
  val env : Environ.env
  val sigma : Evd.evar_map
end
module PatternMatching (E:StaticEnvironment) = struct


  (** {6 The pattern-matching monad } *)


  (** To focus on the algorithmic portion of pattern-matching, the
      bookkeeping is relegated to a monad: the composition of the
      bactracking monad of {!IStream.t} with a "writer" effect. *)
  (* spiwack: as we don't benefit from the various stream optimisations
     of Haskell, it may be costly to give the monad in direct style such as
     here. We may want to use some continuation passing style. *)
  type 'a m = 'a t IStream.t


  (** The empty substitution. *)
  let empty_subst = Id.Map.empty , Id.Map.empty

  (** Composes two substitutions using {!verify_metas_coherence}. It
      must be a monoid with neutral element {!empty_subst}. Raises
      [Not_coherent_metas] when composition cannot be achieved. *)
  let subst_prod s1 s2 =
    if is_empty_subst s1 then s2
    else if is_empty_subst s2 then s1
    else verify_metas_coherence E.env E.sigma s1 s2

  (** The empty context substitution. *)
  let empty_context_subst = Id.Map.empty

  (** Compose two context substitutions, in case of conflict the
      right hand substitution shadows the left hand one. *)
  let context_subst_prod = id_map_right_biased_union

  (** The empty term substitution. *)
  let empty_term_subst = Id.Map.empty

  (** Compose two terms substitutions, in case of conflict the
      right hand substitution shadows the left hand one. *)
  let term_subst_prod = id_map_right_biased_union


  (** Monadic [return]: returns a single success with empty substitutions. *)
  let return (type a) (lhs:a) : a m =
    let success = {
      subst = empty_subst ;
      context = empty_context_subst ;
      terms = empty_term_subst ;
      lhs = lhs ; }
    in
    IStream.(cons success empty)

  (** Monadic bind: each success of [x] is replaced by the successes
      of [f x]. The substitutions of [x] and [f x] are composed,
      dropping the apparent successes when the substitutions are not
      coherent. *)
  let (>>=) (type a) (type b) (x:a m) (f:a -> b m) : b m =
    let open IStream in
    concat_map begin fun { subst=substx; context=contextx; terms=termsx; lhs=lhsx } ->
      map_filter begin fun { subst=substf; context=contextf; terms=termsf; lhs=lhsf } ->
        try
          Some {
            subst = subst_prod substx substf ;
            context = context_subst_prod contextx contextf ;
            terms = term_subst_prod termsx termsf ;
            lhs = lhsf
          }
        with Not_coherent_metas -> None
      end (f lhsx)
    end x

  (** A variant of [(>>=)] when the first argument returns [unit]. *)
  let (<*>) (type a) (x:unit m) (y:a m) : a m =
    let open IStream in
    concat_map begin fun { subst=substx; context=contextx; terms=termsx; lhs=() } ->
      map_filter begin fun { subst=substy; context=contexty; terms=termsy; lhs=lhsy } ->
        try
          Some {
            subst = subst_prod substx substy ;
            context = context_subst_prod contextx contexty ;
            terms = term_subst_prod termsx termsy ;
            lhs = lhsy
          }
        with Not_coherent_metas -> None
      end y
    end x

  (** Failure of the pattern-matching monad: no success. *)
  let fail (type a) : a m = IStream.empty

  (** Chooses in a list, in the same order as the list *)
  let pick (type a) (l:a list) : a m =
    IStream.map begin fun x ->
      { subst = empty_subst ;
        context = empty_context_subst ;
        terms = empty_term_subst ;
        lhs = x }
    end (IStream.of_list l)

  (** Declares a subsitution, a context substitution and a term substitution. *)
  let put subst context terms : unit m =
    IStream.(cons { subst ; context ; terms ; lhs = () } empty)

  (** Declares a substitution. *)
  let put_subst subst : unit m = put subst empty_context_subst empty_term_subst

  (** Declares a context substitution. *)
  let put_context context : unit m = put empty_subst context empty_term_subst

  (** Declares a term substitution. *)
  let put_terms terms : unit m = put empty_subst empty_context_subst terms



  (** {6 Pattern-matching} *)


  (** [wildcard_match_term lhs] matches a term against a wildcard
      pattern ([_ => lhs]). It has a single success with an empty
      substitution. *)
  let wildcard_match_term = return

  (** [pattern_match_term refresh pat term lhs] returns the possible
      matchings of [term] with the pattern [pat => lhs]. If refresh is
      true, refreshes the universes of [term]. *)
  let pattern_match_term refresh pat term lhs = 
    let term = if refresh then Termops.refresh_universes_strict term else term in
    match pat with
    | Term p ->
        begin 
          try
            put_subst (ConstrMatching.extended_matches p term) <*>
            return lhs
          with ConstrMatching.PatternMatchingFailure -> fail
        end
    | Subterm (with_app_context,id_ctxt,p) ->
        (* spiwack: this branch is easier in direct style, would need to be
           changed if the implementation of the monad changes. *)
        IStream.map begin fun { ConstrMatching.m_sub ; m_ctx } ->
          let subst = adjust m_sub in
          let context = id_map_try_add id_ctxt m_ctx Id.Map.empty in
          let terms = empty_term_subst in
          { subst ; context ; terms ; lhs }
        end (ConstrMatching.match_subterm_gen with_app_context p term)


  (** [rule_match_term term rule] matches the term [term] with the
      matching rule [rule]. *)
  let rule_match_term term = function
    | All lhs -> wildcard_match_term lhs
    | Pat ([],pat,lhs) -> pattern_match_term false pat term lhs
    | Pat _ ->
        (** Rules with hypotheses, only work in match goal. *)
        fail

  (** [match_term term rules] matches the term [term] with the set of
      matching rules [rules].*)
  let match_term term rules =
    IStream.(concat (map (fun r -> rule_match_term term r) (of_list rules)))




  (** [hyp_match_type hypname pat hyps] matches a single
      hypothesis pattern [hypname:pat] against the hypotheses in
      [hyps]. Tries the hypotheses in order. For each success returns
      the name of the matched hypothesis. *)
  let hyp_match_type hypname pat hyps =
    pick hyps >>= fun (id,b,hyp) ->
    let refresh = not (Option.is_empty b) in
    pattern_match_term refresh pat hyp () <*>
    put_terms (id_map_try_add_name hypname (Term.mkVar id) empty_term_subst) <*>
    return id

  (** [hyp_match_type hypname bodypat typepat hyps] matches a single
      hypothesis pattern [hypname := bodypat : typepat] against the
      hypotheses in [hyps].Tries the hypotheses in order. For each
      success returns the name of the matched hypothesis. *)
  let hyp_match_body_and_type hypname bodypat typepat hyps =
    pick hyps >>= function
      | (id,Some body,hyp) ->
          pattern_match_term false bodypat body () <*>
          pattern_match_term true typepat hyp () <*>
          put_terms (id_map_try_add_name hypname (Term.mkVar id) empty_term_subst) <*>
          return id
      | (id,None,hyp) -> fail

  (** [hyp_match pat hyps] dispatches to
      {!hyp_match_type} or {!hyp_match_body_and_type} depending on whether
      [pat] is [Hyp _] or [Def _]. *)
  let hyp_match pat hyps =
    match pat with
    | Hyp ((_,hypname),typepat) ->
        hyp_match_type hypname typepat hyps
    | Def ((_,hypname),bodypat,typepat) ->
        hyp_match_body_and_type hypname bodypat typepat hyps

  (** [hyp_pattern_list_match pats hyps lhs], matches the list of
      patterns [pats] against the hypotheses in [hyps], and eventually
      returns [lhs]. *)
  let rec hyp_pattern_list_match pats hyps lhs =
    match pats with
    | pat::pats ->
        hyp_match pat hyps >>= fun matched_hyp ->
        (* spiwack: alternatively it is possible to return the list
           with the matched hypothesis removed directly in
           [hyp_match]. *)
        let select_matched_hyp (id,_,_) = Id.equal id matched_hyp in
        let hyps = CList.remove_first select_matched_hyp hyps in
        hyp_pattern_list_match pats hyps lhs
    | [] -> return lhs

  (** [rule_match_goal hyps concl rule] matches the rule [rule]
      against the goal [hyps|-concl]. *)
  let rule_match_goal hyps concl = function
    | All lhs -> wildcard_match_term lhs
    | Pat (hyppats,conclpat,lhs) ->
        (* the rules are applied from the topmost one (in the concrete
           syntax) to the bottommost. *)
        let hyppats = List.rev hyppats in
        pattern_match_term false conclpat concl () <*>
        hyp_pattern_list_match hyppats hyps lhs

  (** [match_goal hyps concl rules] matches the goal [hyps|-concl]
      with the set of matching rules [rules]. *)
  let match_goal hyps concl rules =
    IStream.(concat (map (fun r -> rule_match_goal hyps concl r) (of_list rules)))

end

(** [match_term env sigma term rules] matches the term [term] with the
    set of matching rules [rules]. The environment [env] and the
    evar_map [sigma] are not currently used, but avoid code
    duplication. *)
let match_term env sigma term rules =
  let module E = struct
    let env = env
    let sigma = sigma
  end in
  let module M = PatternMatching(E) in
  M.match_term term rules


(** [match_goal env sigma hyps concl rules] matches the goal
    [hyps|-concl] with the set of matching rules [rules]. The
    environment [env] and the evar_map [sigma] are used to check
    convertibility for pattern variables shared between hypothesis
    patterns or the conclusion pattern. *)
let match_goal env sigma hyps concl rules =
  let module E = struct
    let env = env
    let sigma = sigma
  end in
  let module M = PatternMatching(E) in
  M.match_goal hyps concl rules
