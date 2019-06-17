(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

type context = EConstr.t

type result = {
  subst : Ltac_pretype.patvar_map ;
}

type match_pattern =
| MatchPattern of Pattern.constr_pattern
| MatchContext of Pattern.constr_pattern

(** TODO: handle definitions *)
type match_context_hyps = match_pattern

type match_rule = match_context_hyps list * match_pattern

(** {6 Utilities} *)

(** Tests whether the substitution [s] is empty. *)
let is_empty_subst = Id.Map.is_empty

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
let equal_instances env sigma c1 c2 =
  (* How to compare instances? Do we want the terms to be convertible?
     unifiable? Do we want the universe levels to be relevant?
     (historically, conv_x is used) *)
  Reductionops.is_conv env sigma c1 c2

(** Merges two substitutions. Raises [Not_coherent_metas] when
    encountering two instances of the same metavariable which are not
    equal according to {!equal_instances}. *)
exception Not_coherent_metas
let verify_metas_coherence env sigma s1 s2 =
  let merge id oc1 oc2 = match oc1, oc2 with
    | None, None -> None
    | None, Some c | Some c, None -> Some c
    | Some c1, Some c2 ->
        if equal_instances env sigma c1 c2 then Some c1
        else raise Not_coherent_metas
  in
  Id.Map.merge merge s1 s2

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
      backtracking monad of {!IStream.t} with a "writer" effect. *)
  (* spiwack: as we don't benefit from the various stream optimisations
     of Haskell, it may be costly to give the monad in direct style such as
     here. We may want to use some continuation passing style. *)
  type 'a tac = 'a Proofview.tactic
  type 'a m = { stream : 'r. ('a -> result -> 'r tac) -> result -> 'r tac }

  (** The empty substitution. *)
  let empty_subst = Id.Map.empty

  (** Composes two substitutions using {!verify_metas_coherence}. It
      must be a monoid with neutral element {!empty_subst}. Raises
      [Not_coherent_metas] when composition cannot be achieved. *)
  let subst_prod s1 s2 =
    if is_empty_subst s1 then s2
    else if is_empty_subst s2 then s1
    else verify_metas_coherence E.env E.sigma s1 s2

  (** Merge two writers (and ignore the first value component). *)
  let merge m1 m2 =
    try Some {
      subst = subst_prod m1.subst m2.subst;
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
    } in
    let eval x ctx = Proofview.tclUNIT (x, ctx) in
    m.stream eval ctx

  (** Chooses in a list, in the same order as the list *)
  let rec pick (l:'a list) (e, info) : 'a m = match l with
  | [] -> { stream = fun _ _ -> Proofview.tclZERO ~info e }
  | x :: l ->
    { stream = fun k ctx -> Proofview.tclOR (k x ctx) (fun e -> (pick l e).stream k ctx) }

  let pick l = pick l imatching_error

  let put_subst subst : unit m =
    let s = { subst } in
    { stream = fun k ctx -> match merge s ctx with None -> Proofview.tclZERO matching_error | Some s -> k () s }

  (** {6 Pattern-matching} *)

  let pattern_match_term pat term =
    match pat with
    | MatchPattern p ->
        begin
          try
            put_subst (Constr_matching.matches E.env E.sigma p term) <*>
            return None
          with Constr_matching.PatternMatchingFailure -> fail
        end
    | MatchContext p ->

      let rec map s (e, info) =
        { stream = fun k ctx -> match IStream.peek s with
          | IStream.Nil -> Proofview.tclZERO ~info e
          | IStream.Cons ({ Constr_matching.m_sub = (_, subst); m_ctx }, s) ->
            let nctx = { subst } in
            match merge ctx nctx with
            | None -> (map s (e, info)).stream k ctx
            | Some nctx -> Proofview.tclOR (k (Some (Lazy.force m_ctx)) nctx) (fun e -> (map s e).stream k ctx)
        }
      in
      map (Constr_matching.match_subterm E.env E.sigma (Id.Set.empty,p) term) imatching_error

  let hyp_match_type pat hyps =
    pick hyps >>= fun decl ->
    let id = NamedDecl.get_id decl in
    pattern_match_term pat (NamedDecl.get_type decl) >>= fun ctx ->
    return (id, ctx)

  let _hyp_match_body_and_type bodypat typepat hyps =
    pick hyps >>= function
      | LocalDef (id,body,hyp) ->
          pattern_match_term bodypat body >>= fun ctx_body ->
          pattern_match_term typepat hyp >>= fun ctx_typ ->
          return (id, ctx_body, ctx_typ)
      | LocalAssum (id,hyp) -> fail

  let hyp_match pat hyps =
    match pat with
    | typepat ->
        hyp_match_type typepat hyps
(*     | Def ((_,hypname),bodypat,typepat) -> *)
(*         hyp_match_body_and_type hypname bodypat typepat hyps *)

  (** [hyp_pattern_list_match pats hyps lhs], matches the list of
      patterns [pats] against the hypotheses in [hyps], and eventually
      returns [lhs]. *)
  let rec hyp_pattern_list_match pats hyps accu =
    match pats with
    | pat::pats ->
        hyp_match pat hyps >>= fun (matched_hyp, hyp_ctx) ->
        let select_matched_hyp decl = Id.equal (NamedDecl.get_id decl) matched_hyp in
        let hyps = CList.remove_first select_matched_hyp hyps in
        hyp_pattern_list_match pats hyps ((matched_hyp, hyp_ctx) :: accu)
    | [] -> return accu

  let rule_match_goal hyps concl = function
    | (hyppats,conclpat) ->
        (* the rules are applied from the topmost one (in the concrete
           syntax) to the bottommost. *)
        let hyppats = List.rev hyppats in
        pattern_match_term conclpat concl >>= fun ctx_concl ->
        hyp_pattern_list_match hyppats hyps [] >>= fun hyps ->
        return (hyps, ctx_concl)

end

let match_goal env sigma concl ~rev rule =
  let open Proofview.Notations in
  let hyps = EConstr.named_context env in
  let hyps = if rev then List.rev hyps else hyps in
  let module E = struct
    let env = env
    let sigma = sigma
  end in
  let module M = PatternMatching(E) in
  M.run (M.rule_match_goal hyps concl rule) >>= fun ((hyps, ctx_concl), subst) ->
  Proofview.tclUNIT (hyps, ctx_concl, subst.subst)
