(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file extends Matching with the main logic for Ltac's
    (lazy)match and (lazy)match goal. *)

open Names
open Tacexpr
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

(** [t] is the type of matching successes. It ultimately contains a
    {!Tacexpr.glob_tactic_expr} representing the left-hand side of the
    corresponding matching rule, a matching substitution to be
    applied, a context substitution mapping identifier to context like
    those of {!Matching.matching_result}), and a {!Term.constr}
    substitution mapping corresponding to matched hypotheses. *)
type 'a t = {
  subst : Constr_matching.bound_ident_map * Ltac_pretype.extended_patvar_map ;
  context : EConstr.constr Id.Map.t;
  terms : EConstr.constr Id.Map.t;
  lhs : 'a;
}



(** {6 Utilities} *)


(** Some of the functions of {!Matching} return the substitution with a
    [patvar_map] instead of an [extended_patvar_map]. [adjust] coerces
    substitution of the former type to the latter. *)
let adjust : Constr_matching.bound_ident_map * Ltac_pretype.patvar_map ->
             Constr_matching.bound_ident_map * Ltac_pretype.extended_patvar_map =
  fun (l, lc) -> (l, Id.Map.map (fun c -> [], c) lc)


(** Adds a binding to a {!Id.Map.t} if the identifier is [Some id] *)
let id_map_try_add id x m =
  match id with
  | Some id -> Id.Map.add id (Lazy.force x) m
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

let matching_error =
  CErrors.UserError (Some "tactic matching" , Pp.str "No matching clauses for match.")

let imatching_error = (matching_error, Exninfo.null)

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
  type 'a tac = 'a Proofview.tactic
  type 'a m = { stream : 'r. ('a -> unit t -> 'r tac) -> unit t -> 'r tac }

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

  (** Merge two writers (and ignore the first value component). *)
  let merge m1 m2 =
    try Some {
      subst = subst_prod m1.subst m2.subst;
      context = context_subst_prod m1.context m2.context;
      terms = term_subst_prod m1.terms m2.terms;
      lhs = m2.lhs;
    }
    with Not_coherent_metas -> None

  (** Monadic [return]: returns a single success with empty substitutions. *)
  let return (type a) (lhs:a) : a m =
    { stream = fun k ctx -> k lhs ctx }

  (** Monadic bind: each success of [x] is replaced by the successes
      of [f x]. The substitutions of [x] and [f x] are composed,
      dropping the apparent successes when the substitutions are not
      coherent. *)
  let (>>=) (type a) (type b) (m:a m) (f:a -> b m) : b m =
    { stream = fun k ctx -> m.stream (fun x ctx -> (f x).stream k ctx) ctx }

  (** A variant of [(>>=)] when the first argument returns [unit]. *)
  let (<*>) (type a) (m:unit m) (y:a m) : a m =
    { stream = fun k ctx -> m.stream (fun () ctx -> y.stream k ctx) ctx }

  (** Failure of the pattern-matching monad: no success. *)
  let fail (type a) : a m = { stream = fun _ _ -> Proofview.tclZERO matching_error }

  let run (m : 'a m) =
    let ctx = {
      subst = empty_subst ;
      context = empty_context_subst ;
      terms = empty_term_subst ;
      lhs = ();
    } in
    let eval lhs ctx = Proofview.tclUNIT { ctx with lhs } in
    m.stream eval ctx

  (** Chooses in a list, in the same order as the list *)
  let rec pick (l:'a list) (e, info) : 'a m = match l with
  | [] -> { stream = fun _ _ -> Proofview.tclZERO ~info e }
  | x :: l ->
    { stream = fun k ctx -> Proofview.tclOR (k x ctx) (fun e -> (pick l e).stream k ctx) }

  let pick l = pick l imatching_error

  (** Declares a substitution, a context substitution and a term substitution. *)
  let put subst context terms : unit m =
    let s = { subst ; context ; terms ; lhs = () } in
    { stream = fun k ctx -> match merge s ctx with None -> Proofview.tclZERO matching_error | Some s -> k () s }

  (** Declares a substitution. *)
  let put_subst subst : unit m = put subst empty_context_subst empty_term_subst

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
(*     let term = if refresh then Termops.refresh_universes_strict term else term in *)
    match pat with
    | Term p ->
        begin 
          try
            put_subst (Constr_matching.extended_matches E.env E.sigma p term) <*>
            return lhs
          with Constr_matching.PatternMatchingFailure -> fail
        end
    | Subterm (id_ctxt,p) ->

      let rec map s (e, info) =
        { stream = fun k ctx -> match IStream.peek s with
          | IStream.Nil -> Proofview.tclZERO ~info e
          | IStream.Cons ({ Constr_matching.m_sub ; m_ctx }, s) ->
            let subst = adjust m_sub in
            let context = id_map_try_add id_ctxt m_ctx Id.Map.empty in
            let terms = empty_term_subst in
            let nctx = { subst ; context ; terms ; lhs = () } in
            match merge ctx nctx with
            | None -> (map s (e, info)).stream k ctx
            | Some nctx -> Proofview.tclOR (k lhs nctx) (fun e -> (map s e).stream k ctx)
        }
      in
      map (Constr_matching.match_subterm E.env E.sigma p term) imatching_error


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
  let rec match_term (e, info) term rules = match rules with
  | [] -> { stream = fun _ _ -> Proofview.tclZERO ~info e }
  | r :: rules ->
    { stream = fun k ctx ->
      let head = rule_match_term term r in
      let tail e = match_term e term rules in
      Proofview.tclOR (head.stream k ctx) (fun e -> (tail e).stream k ctx)
    }


  (** [hyp_match_type hypname pat hyps] matches a single
      hypothesis pattern [hypname:pat] against the hypotheses in
      [hyps]. Tries the hypotheses in order. For each success returns
      the name of the matched hypothesis. *)
  let hyp_match_type hypname pat hyps =
    pick hyps >>= fun decl ->
    let id = NamedDecl.get_id decl in
    let refresh = is_local_def decl in
    pattern_match_term refresh pat (NamedDecl.get_type decl) () <*>
    put_terms (id_map_try_add_name hypname (EConstr.mkVar id) empty_term_subst) <*>
    return id

  (** [hyp_match_type hypname bodypat typepat hyps] matches a single
      hypothesis pattern [hypname := bodypat : typepat] against the
      hypotheses in [hyps].Tries the hypotheses in order. For each
      success returns the name of the matched hypothesis. *)
  let hyp_match_body_and_type hypname bodypat typepat hyps =
    pick hyps >>= function
      | LocalDef (id,body,hyp) ->
          pattern_match_term false bodypat body () <*>
          pattern_match_term true typepat hyp () <*>
          put_terms (id_map_try_add_name hypname (EConstr.mkVar id) empty_term_subst) <*>
          return id
      | LocalAssum (id,hyp) -> fail

  (** [hyp_match pat hyps] dispatches to
      {!hyp_match_type} or {!hyp_match_body_and_type} depending on whether
      [pat] is [Hyp _] or [Def _]. *)
  let hyp_match pat hyps =
    match pat with
    | Hyp ({CAst.v=hypname},typepat) ->
        hyp_match_type hypname typepat hyps
    | Def ({CAst.v=hypname},bodypat,typepat) ->
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
        let select_matched_hyp decl = Id.equal (NamedDecl.get_id decl) matched_hyp in
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
  let rec match_goal (e, info) hyps concl rules = match rules with
  | [] -> { stream = fun _ _ -> Proofview.tclZERO ~info e }
  | r :: rules ->
    { stream = fun k ctx ->
      let head = rule_match_goal hyps concl r in
      let tail e = match_goal e hyps concl rules in
      Proofview.tclOR (head.stream k ctx) (fun e -> (tail e).stream k ctx)
    }

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
  M.run (M.match_term imatching_error term rules)


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
  M.run (M.match_goal imatching_error hyps concl rules)
