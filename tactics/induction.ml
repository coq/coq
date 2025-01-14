(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open Pp
open CErrors
open Util
open Names
open Nameops
open Constr
open Context
open Termops
open Environ
open EConstr
open Vars
open Namegen
open Declarations
open Reductionops
open Tacred
open Genredexpr
open Tacmach
open Logic
open Clenv
open Tacticals
open Rocqlib
open Evarutil
open Indrec
open Unification
open Locus
open Locusops
open Tactypes
open Proofview.Notations
open Tactics

module NamedDecl = Context.Named.Declaration

let tclEVARS = Proofview.Unsafe.tclEVARS

let inj_with_occurrences e = (AllOccurrences,e)

let typ_of env sigma c =
  let open Retyping in
  try get_type_of ~lax:true env sigma c
  with RetypeError e ->
    user_err (print_retype_error e)

(*********************************************)
(*                 Errors                    *)
(*********************************************)

exception AlreadyUsed of Id.t
exception SchemeDontApply
exception NeedFullyAppliedArgument
exception NotAnInductionScheme of string
exception NotAnInductionSchemeLetIn
exception CannotFindInductiveArgument
exception MentionConclusionDependentOn of Id.t
exception DontKnowWhatToDoWith of intro_pattern_naming_expr
exception UnsupportedWithClause
exception UnsupportedEqnClause
exception UnsupportedInClause of bool
exception DontKnowWhereToFindArgument
exception MultipleAsAndUsingClauseOnlyList

let error ?loc e =
  Loc.raise ?loc e

exception Unhandled

let wrap_unhandled f e =
  try Some (f e)
  with Unhandled -> None

let tactic_interp_error_handler = function
  | AlreadyUsed id ->
      Id.print id ++ str " is already used."
  | SchemeDontApply ->
      str "Scheme cannot be applied."
  | NeedFullyAppliedArgument ->
      str "Need a fully applied argument."
  | NotAnInductionScheme s ->
      let s = if not (String.is_empty s) then s^" " else s in
      str "Cannot recognize " ++ str s ++ str "an induction scheme."
  | NotAnInductionSchemeLetIn ->
      str "Strange letin, cannot recognize an induction scheme."
  | CannotFindInductiveArgument ->
      str "Cannot find inductive argument of elimination scheme."
  | MentionConclusionDependentOn id ->
      str "Conclusion must be mentioned: it depends on " ++ Id.print id ++ str "."
  | DontKnowWhatToDoWith id ->
      str "Do not know what to do with " ++ Miscprint.pr_intro_pattern_naming id
  | UnsupportedEqnClause ->
      str "'eqn' clause not supported here."
  | UnsupportedWithClause ->
      str "'with' clause not supported here."
  | UnsupportedInClause b ->
      str (if b then "'in' clause not supported here."
           else "'eqn' clause not supported here.")
  | DontKnowWhereToFindArgument ->
      str "Don't know where to find some argument."
  | MultipleAsAndUsingClauseOnlyList ->
      str "'as' clause with multiple arguments and 'using' clause can only occur last."
  | _ -> raise Unhandled

let _ = CErrors.register_handler (wrap_unhandled tactic_interp_error_handler)

let fresh_id_in_env avoid id env =
  let avoid' = ids_of_named_context_val (named_context_val env) in
  let avoid = if Id.Set.is_empty avoid then avoid' else Id.Set.union avoid' avoid in
  next_ident_away_in_goal (Global.env ()) id avoid

let new_fresh_id avoid id gl =
  fresh_id_in_env avoid id (Proofview.Goal.env gl)

let intros_until_n n =
  Tactics.try_intros_until (fun _ -> tclIDTAC) (AnonHyp n)

let try_intros_until_id_check id =
  Tactics.try_intros_until (fun _ -> tclIDTAC) (NamedHyp (CAst.make id))

(* Apply a tactic on a quantified hypothesis, an hypothesis in context
   or a term with bindings *)

let tactic_infer_flags with_evar = Pretyping.{
  use_coercions = true;
  use_typeclasses = UseTC;
  solve_unification_constraints = true;
  fail_evar = not with_evar;
  expand_evars = true;
  program_mode = false;
  polymorphic = false;
  undeclared_evars_patvars = false;
  patvars_abstract = false;
  unconstrained_sorts = false;
}

let onOpenInductionArg env sigma tac = function
  | clear_flag,ElimOnConstr f ->
      let (sigma', cbl) = f env sigma in
      Tacticals.tclTHEN
        (Proofview.Unsafe.tclEVARS sigma')
        (tac clear_flag (Some sigma,cbl))
  | clear_flag,ElimOnAnonHyp n ->
      Tacticals.tclTHEN
        (intros_until_n n)
        (Tacticals.onLastHyp
           (fun c ->
             Proofview.Goal.enter begin fun gl ->
             let sigma = Tacmach.project gl in
             tac clear_flag (Some sigma,(c,NoBindings))
             end))
  | clear_flag,ElimOnIdent {CAst.v=id} ->
      (* A quantified hypothesis *)
      Tacticals.tclTHEN
        (try_intros_until_id_check id)
        (Proofview.Goal.enter begin fun gl ->
         let sigma = Tacmach.project gl in
         tac clear_flag (Some sigma,(mkVar id,NoBindings))
        end)

let with_no_bindings (c, lbind) =
  if lbind != NoBindings then error UnsupportedWithClause;
  c

(********************************************)
(*       Elimination tactics                *)
(********************************************)

let index_of_ind_arg sigma t =
  let rec aux i j t = match EConstr.kind sigma t with
  | LetIn (_, _, _, t) -> aux i j t
  | Prod (_,t,u) ->
      (* heuristic *)
      if isInd sigma (fst (decompose_app sigma t)) then aux (Some j) (j+1) u
      else aux i (j+1) u
  | _ -> match i with
      | Some i -> i
      | None -> error CannotFindInductiveArgument
  in aux None 0 t

(*
 * Elimination tactic with bindings and using an arbitrary
 * elimination constant called elimc. This constant should end
 * with a clause (x:I)(P .. ), where P is a bound variable.
 * The term c is of type t, which is a product ending with a type
 * matching I, lbindc are the expected terms for c arguments
 *)

type eliminator =
| ElimConstant of (Constant.t * EInstance.t)
  (* Constant generated by a scheme function *)
| ElimClause of EConstr.constr with_bindings
  (* Arbitrary expression provided by the user *)

let is_nonrec env mind = (Environ.lookup_mind (fst mind) env).mind_finite == Declarations.BiFinite

let find_ind_eliminator env sigma ind s =
  let c = lookup_eliminator env ind s in
  let sigma, c = EConstr.fresh_global env sigma c in
  sigma, destConst sigma c

let clear_wildcards = Tactics.Internal.clear_wildcards

(*****************************)
(* Decomposing introductions *)
(*****************************)

let insert_before decls lasthyp env =
  match lasthyp with
  | None -> push_named_context decls env
  | Some id ->
  Environ.fold_named_context
    (fun _ d env ->
      let d = EConstr.of_named_decl d in
      let env = if Id.equal id (NamedDecl.get_id d) then push_named_context decls env else env in
      push_named d env)
    ~init:(reset_context env) env

let mk_eq_name env id {CAst.loc;v=ido} =
  match ido with
  | IntroAnonymous -> fresh_id_in_env (Id.Set.singleton id) (add_prefix "Heq" id) env
  | IntroFresh heq_base -> fresh_id_in_env (Id.Set.singleton id) heq_base env
  | IntroIdentifier id ->
    if List.mem id (ids_of_named_context (named_context env)) then
      error (AlreadyUsed id);
    id

(* unsafe *)

let mkletin_goal env sigma with_eq dep (id,lastlhyp,ccl,c) ty =
  let open Context.Named.Declaration in
  let t = match ty with Some t -> t | _ -> typ_of env sigma c in
  let r = Retyping.relevance_of_type env sigma t in
  let decl = if dep then LocalDef (make_annot id r,c,t)
             else LocalAssum (make_annot id r,t)
  in
  match with_eq with
  | Some (lr,heq) ->
      let eqdata = build_rocq_eq_data () in
      let args = if lr then [mkVar id;c] else [c;mkVar id]in
      let (sigma, eq) = Evd.fresh_global env sigma eqdata.eq in
      let refl = mkRef (eqdata.refl, snd (destRef sigma eq)) in
      (* NB we are not in the right env for [id] so we only check the partial application.
         This is enough to produce the desired univ constraint between univ of eq and univ of t *)
      let sigma, eq = Typing.checked_applist env sigma eq [t] in
      let eq = applist (eq,args) in
      let refl = applist (refl, [t;mkVar id]) in
      let newenv = insert_before [LocalAssum (make_annot heq ERelevance.relevant,eq); decl] lastlhyp env in
      let (sigma, x) = new_evar newenv sigma ccl in
      (sigma, mkNamedLetIn sigma (make_annot id r) c t
         (mkNamedLetIn sigma (make_annot heq ERelevance.relevant) refl eq x),
      Some (fst @@ destEvar sigma x))
  | None ->
      let newenv = insert_before [decl] lastlhyp env in
      let (sigma, x) = new_evar newenv sigma ccl in
      (sigma, mkNamedLetIn sigma (make_annot id r) c t x, Some (fst @@ destEvar sigma x))

let warn_cannot_remove_as_expected =
  CWarnings.create ~name:"cannot-remove-as-expected" ~category:CWarnings.CoreCategories.tactics
         (fun (id,inglobal) ->
           let pp = match inglobal with
             | None -> mt ()
             | Some ref -> str ", it is used implicitly in " ++ Printer.pr_global ref in
           str "Cannot remove " ++ Id.print id ++ pp ++ str ".")

let clear_for_destruct ids =
  Proofview.tclORELSE
    (Tactics.Internal.clear_gen (fun env sigma id err inglobal -> raise (ClearDependencyError (id,err,inglobal))) ids)
    (function
     | ClearDependencyError (id,err,inglobal),_ -> warn_cannot_remove_as_expected (id,inglobal); Proofview.tclUNIT ()
     | e -> Exninfo.iraise e)

(* Either unfold and clear if defined or simply clear if not a definition *)
let expand_hyp id =
  Tacticals.tclTRY (Tactics.unfold_body id) <*> clear_for_destruct [id]

(*****************************)
(* High-level induction      *)
(*****************************)

(*
 * A "natural" induction tactic
 *
  - [H0:T0, ..., Hi:Ti, hyp0:P->I(args), Hi+1:Ti+1, ..., Hn:Tn |-G] is the goal
  - [hyp0] is the induction hypothesis
  - we extract from [args] the variables which are not rigid parameters
    of the inductive type, this is [indvars] (other terms are forgotten);
  - we look for all hyps depending of [hyp0] or one of [indvars]:
    this is [dephyps] of types [deptyps] respectively
  - [statuslist] tells for each hyps in [dephyps] after which other hyp
    fixed in the context they must be moved (when induction is done)
  - [hyp0succ] is the name of the hyp fixed in the context after which to
    move the subterms of [hyp0succ] in the i-th branch where it is supposed
    to be the i-th constructor of the inductive type.

  Strategy: (cf in [induction_with_atomization_of_ind_arg])
  - requantify and clear all [dephyps]
  - apply induction on [hyp0]
  - clear those of [indvars] that are variables and [hyp0]
  - in the i-th subgoal, intro the arguments of the i-th constructor
    of the inductive type after [hyp0succ] (done in
    [induct_discharge]) let the induction hypotheses on top of the
    hyps because they may depend on variables between [hyp0] and the
    top. A counterpart is that the dep hyps programmed to be intro-ed
    on top must now be intro-ed after the induction hypotheses
  - move each of [dephyps] at the right place following the
    [statuslist]

 *)

let warn_unused_intro_pattern =
  CWarnings.create ~name:"unused-intro-pattern" ~category:CWarnings.CoreCategories.tactics
    (fun (env,sigma,names) ->
       strbrk"Unused introduction " ++ str (String.plural (List.length names) "pattern") ++
       str": " ++ prlist_with_sep spc
         (Miscprint.pr_intro_pattern
            (fun c -> Printer.pr_econstr_env env sigma (snd (c env sigma)))) names)

let check_unused_names env sigma names =
  if not (List.is_empty names) then
    warn_unused_intro_pattern (env, sigma, names)

let intropattern_of_name gl avoid = function
  | Anonymous -> IntroNaming IntroAnonymous
  | Name id -> IntroNaming (IntroIdentifier (new_fresh_id avoid id gl))

let rec consume_pattern avoid na isdep gl = let open CAst in function
  | [] -> ((CAst.make @@ intropattern_of_name gl avoid na), [])
  | {loc;v=IntroForthcoming true}::names when not isdep ->
      consume_pattern avoid na isdep gl names
  | {loc;v=IntroForthcoming _}::names as fullpat ->
      (CAst.make ?loc @@ intropattern_of_name gl avoid na, fullpat)
  | {loc;v=IntroNaming IntroAnonymous}::names ->
      (CAst.make ?loc @@ intropattern_of_name gl avoid na, names)
  | {loc;v=IntroNaming (IntroFresh id')}::names ->
      (CAst.make ?loc @@ IntroNaming (IntroIdentifier (new_fresh_id avoid id' gl)), names)
  | pat::names -> (pat,names)

let re_intro_dependent_hypotheses (lstatus,rstatus) (_,tophyp) =
  let tophyp = match tophyp with None -> MoveLast | Some hyp -> MoveAfter hyp in
  let newlstatus = (* if some IH has taken place at the top of hyps *)
    List.map (function (hyp,MoveLast) -> (hyp,tophyp) | x -> x) lstatus
  in
  Tacticals.tclTHEN
    (Tactics.intros_move rstatus)
    (Tactics.intros_move newlstatus)

let dest_intro_patterns = Tactics.Internal.dest_intro_patterns

let safe_dest_intro_patterns with_evars avoid thin dest pat tac =
  Proofview.tclORELSE
    (dest_intro_patterns with_evars avoid thin dest pat tac)
    begin function (e, info) -> match e with
      | CannotMoveHyp _ ->
       (* May happen e.g. with "destruct x using s" with an hypothesis
          which is morally an induction hypothesis to be "MoveLast" if
          known as such but which is considered instead as a subterm of
          a constructor to be move at the place of x. *)
          dest_intro_patterns with_evars avoid thin MoveLast pat tac
      | e -> Proofview.tclZERO ~info e
    end

type elim_arg_kind = RecArg | IndArg | OtherArg

type branch_argument = {
  ba_kind : elim_arg_kind;
  ba_assum : bool;
  ba_dep : bool;
  ba_name : Id.t;
}

type recarg_position =
  | AfterFixedPosition of Id.t option (* None = top of context *)

let update_dest (recargdests,tophyp as dests) = function
  | [] -> dests
  | hyp::_ ->
      (match recargdests with
        | AfterFixedPosition None -> AfterFixedPosition (Some hyp)
        | x -> x),
       (match tophyp with None -> Some hyp | x -> x)

let get_recarg_dest (recargdests,tophyp) =
  match recargdests with
  | AfterFixedPosition None -> MoveLast
  | AfterFixedPosition (Some id) -> MoveAfter id

(* Current policy re-introduces recursive arguments of destructed
   variable at the place of the original variable while induction
   hypothesese are introduced at the top of the context. Since in the
   general case of an inductive scheme, the induction hypotheses can
   arrive just after the recursive arguments (e.g. as in "forall
   t1:tree, P t1 -> forall t2:tree, P t2 -> P (node t1 t2)", we need
   to update the position for t2 after "P t1" is introduced if ever t2
   had to be introduced at the top of the context).
*)

let induct_discharge with_evars dests avoid' tac (avoid,ra) names =
  let avoid = Id.Set.union avoid' (Id.Set.union avoid (Tactics.Internal.explicit_intro_names names)) in
  let rec peel_tac ra dests names thin =
    match ra with
    | ({ ba_kind = RecArg } as rarg) :: ({ ba_kind = IndArg } as iarg) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        let (recpat,names) = match names with
          | [{CAst.loc;v=IntroNaming (IntroIdentifier id)} as pat] ->
              let id' = new_fresh_id avoid (add_prefix "IH" id) gl in
              (pat, [CAst.make @@ IntroNaming (IntroIdentifier id')])
          | _ -> consume_pattern avoid (Name rarg.ba_name) rarg.ba_dep gl names in
        let dest = get_recarg_dest dests in
        dest_intro_patterns with_evars avoid thin dest [recpat] (fun ids thin ->
        Proofview.Goal.enter begin fun gl ->
          let (hyprec,names) =
            consume_pattern avoid (Name iarg.ba_name) iarg.ba_dep gl names
          in
          dest_intro_patterns with_evars avoid thin MoveLast [hyprec] (fun ids' thin ->
            peel_tac ra' (update_dest dests ids') names thin)
                             end)
        end
    | ({ ba_kind = IndArg } as iarg) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        (* Rem: does not happen in Rocq schemes, only in user-defined schemes *)
        let pat,names =
          consume_pattern avoid (Name iarg.ba_name) iarg.ba_dep gl names in
        dest_intro_patterns with_evars avoid thin MoveLast [pat] (fun ids thin ->
        peel_tac ra' (update_dest dests ids) names thin)
        end
    | ({ ba_kind = RecArg } as rarg) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        let (pat,names) =
          consume_pattern avoid (Name rarg.ba_name) rarg.ba_dep gl names in
        let dest = get_recarg_dest dests in
        dest_intro_patterns with_evars avoid thin dest [pat] (fun ids thin ->
        peel_tac ra' dests names thin)
        end
    | ({ ba_kind = OtherArg } as oarg) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        let (pat,names) = consume_pattern avoid Anonymous oarg.ba_dep gl names in
        let dest = get_recarg_dest dests in
        safe_dest_intro_patterns with_evars avoid thin dest [pat] (fun ids thin ->
        peel_tac ra' dests names thin)
        end
    | [] ->
        Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        check_unused_names env sigma names;
        Tacticals.tclTHEN (clear_wildcards thin) (tac dests)
        end
  in
  peel_tac ra (dests, None) names []

(* - le recalcul de indtyp à chaque itération de atomize_one est pour ne pas
     s'embêter à regarder si un letin_tac ne fait pas des
     substitutions aussi sur l'argument voisin *)

let expand_projections env sigma c =
  let rec aux env c =
    match EConstr.kind sigma c with
    | Proj (p, _, c) -> Retyping.expand_projection env sigma p (aux env c) []
    | _ -> map_constr_with_full_binders env sigma push_rel aux env c
  in
  aux env c


(* Marche pas... faut prendre en compte l'occurrence précise... *)

let atomize_param_of_ind env sigma (hd, params, indices) =
  let params' = List.map (expand_projections env sigma) params in
  (* le gl est important pour ne pas préévaluer *)
  let rec atomize_one accu args args' avoid = function
  | [] ->
      let t = applist (hd, params@args) in
      (List.rev accu, avoid, t)
  | c :: rem ->
      match EConstr.kind sigma c with
        | Var id when not (List.exists (fun c -> occur_var env sigma id c) args') &&
                      not (List.exists (fun c -> occur_var env sigma id c) params') ->
            (* Based on the knowledge given by the user, all
               constraints on the variable are generalizable in the
               current environment so that it is clearable after destruction *)
            atomize_one accu (c::args) (c::args') (Id.Set.add id avoid) rem
        | _ ->
           let c' = expand_projections env sigma c in
            let dependent t = dependent sigma c t in
            if List.exists dependent params' ||
               List.exists dependent args'
            then
              (* This is a case where the argument is constrained in a
                 way which would require some kind of inversion; we
                 follow the (old) discipline of not generalizing over
                 this term, since we don't try to invert the
                 constraint anyway. *)
              atomize_one accu (c::args) (c'::args') avoid rem
            else
            (* We reason blindly on the term and do as if it were
               generalizable, ignoring the constraints coming from
               its structure *)
            let id = match EConstr.kind sigma c with
            | Var id -> id
            | _ ->
              let ty = Retyping.get_type_of env sigma c in
              id_of_name_using_hdchar env sigma ty Anonymous
            in
            let x = fresh_id_in_env avoid id env in
            let accu = (x, c) :: accu in
            atomize_one accu (mkVar x::args) (mkVar x::args') (Id.Set.add x avoid) rem
  in
  atomize_one [] [] [] Id.Set.empty (List.rev indices)

(* [cook_sign] builds the lists [beforetoclear] (preceding the
   ind. var.) and [aftertoclear] (coming after the ind. var.)  of hyps
   that must be erased, the lists of hyps to be generalize [decldeps] on the
   goal together with the places [(lstatus,rstatus)] where to re-intro
   them after induction. To know where to re-intro the dep hyp, we
   remember the name of the hypothesis [lhyp] after which (if the dep
   hyp is more recent than [hyp0]) or [rhyp] before which (if older
   than [hyp0]) its equivalent must be moved when the induction has
   been applied. Since computation of dependencies and [rhyp] is from
   more ancient (on the right) to more recent hyp (on the left) but
   the computation of [lhyp] progresses from the other way, [cook_hyp]
   is in two passes (an alternative would have been to write an
   higher-order algorithm). We use references to reduce
   the accumulation of arguments.

   To summarize, the situation looks like this

   Goal(n,x) -| H6:(Q n); x:A; H5:True; H4:(le O n); H3:(P n); H2:True; n:nat
                Left                                                    Right

   Induction hypothesis is H4 ([hyp0])
   Variable parameters of (le O n) is the singleton list with "n" ([indvars])
   The dependent hyps are H3 and H6 ([dephyps])
   For H3 the memorized places are H5 ([lhyp]) and H2 ([rhyp])
    because these names are among the hyp which are fixed through the induction
   For H6 the neighbours are None ([lhyp]) and H5 ([rhyp])
   For H3, because on the right of H4, we remember rhyp (here H2)
   For H6, because on the left of H4, we remember lhyp (here None)
   For H4, we remember lhyp (here H5)

   The right neighbour is then translated into the left neighbour
   because move_hyp tactic needs the name of the hyp _after_ which we
   move the hyp to move.

   But, say in the 2nd subgoal of the hypotheses, the goal will be

   (m:nat)((P m)->(Q m)->(Goal m)) -> (P Sm)->   (Q Sm)->   (Goal Sm)
     ^^^^^^^^^^^^^^^^^^^^^^^^^^^       ^^^^
         both go where H4 was       goes where  goes where
                                      H3 was      H6 was

   We have to intro and move m and the recursive hyp first, but then
   where to move H3 ??? Only the hyp on its right is relevant, but we
   have to translate it into the name of the hyp on the left

   Note: this case where some hyp(s) in [dephyps] has(have) the same
   left neighbour as [hyp0] is the only problematic case with right
   neighbours. For the other cases (e.g. an hyp H1:(R n) between n and H2
   would have posed no problem. But for uniformity, we decided to use
   the right hyp for all hyps on the right of H4.

   Other solutions are welcome

   PC 9 fev 06: Adapted to accept multi argument principle with no
   main arg hyp. hyp0 is now optional, meaning that it is possible
   that there is no main induction hypotheses. In this case, we
   consider the last "parameter" (in [indvars]) as the limit between
   "left" and "right", BUT it must be included in indhyps.

   Other solutions are still welcome

*)

exception Shunt of Id.t move_location

let cook_sign hyp0_opt inhyps indvars env sigma =
  (* First phase from L to R: get [toclear], [decldep] and [statuslist]
     for the hypotheses before (= more ancient than) hyp0 (see above) *)
  let toclear = ref [] in
  let avoid = ref Id.Set.empty in
  let decldeps = ref [] in
  let ldeps = ref [] in
  let rstatus = ref [] in
  let lstatus = ref [] in
  let before = ref true in
  let maindep = ref false in
  let seek_deps env decl rhyp =
    let decl = EConstr.of_named_decl decl in
    let hyp = NamedDecl.get_id decl in
    if (match hyp0_opt with Some hyp0 -> Id.equal hyp hyp0 | _ -> false)
    then begin
      before:=false;
      (* Note that if there was no main induction hypotheses, then hyp
         is one of indvars too *)
      toclear := hyp::!toclear;
      MoveFirst (* fake value *)
    end else if Id.Set.mem hyp indvars then begin
      (* The variables in indvars are such that they don't occur any
         more after generalization, so declare them to clear. *)
      toclear := hyp::!toclear;
      rhyp
    end else
      let dephyp0 = not !before && List.is_empty inhyps &&
        (Option.cata (fun id -> occur_var_in_decl env sigma id decl) false hyp0_opt)
      in
      let depother = List.is_empty inhyps &&
        (Id.Set.exists (fun id -> occur_var_in_decl env sigma id decl) indvars ||
         List.exists (fun decl' -> occur_var_in_decl env sigma (NamedDecl.get_id decl') decl) !decldeps)
      in
      if not (List.is_empty inhyps) && Id.List.mem hyp inhyps
         || dephyp0 || depother
      then begin
        decldeps := decl::!decldeps;
        avoid := Id.Set.add hyp !avoid;
        maindep := dephyp0 || !maindep;
        if !before then begin
          toclear := hyp::!toclear;
          rstatus := (hyp,rhyp)::!rstatus
        end
        else begin
          toclear := hyp::!toclear;
          ldeps := hyp::!ldeps (* status computed in 2nd phase *)
        end;
        MoveBefore hyp end
      else
        MoveBefore hyp
  in
  let _ = fold_named_context seek_deps env ~init:MoveFirst in
  (* 2nd phase from R to L: get left hyp of [hyp0] and [lhyps] *)
  let compute_lstatus lhyp decl =
    let hyp = NamedDecl.get_id decl in
    if (match hyp0_opt with Some hyp0 -> Id.equal hyp hyp0 | _ -> false) then
      raise (Shunt lhyp);
    if Id.List.mem hyp !ldeps then begin
      lstatus := (hyp,lhyp)::!lstatus;
      lhyp
    end else
      if Id.List.mem hyp !toclear then lhyp else MoveAfter hyp
  in
  try
    let _ =
      fold_named_context_reverse compute_lstatus ~init:MoveLast env in
    raise (Shunt MoveLast) (* ?? FIXME *)
  with Shunt lhyp0 ->
    let lhyp0 = match lhyp0 with
      | MoveLast -> None
      | MoveAfter hyp -> Some hyp
      | _ -> assert false in
    let statuslists = (!lstatus,List.rev !rstatus) in
    let recargdests = AfterFixedPosition (if Option.is_empty hyp0_opt then None else lhyp0) in
    (statuslists, recargdests, !toclear, !decldeps, !avoid, !maindep)

(*
   The general form of an induction principle is the following:

   forall prm1 prm2 ... prmp,                          (induction parameters)
   forall Q1...,(Qi:Ti_1 -> Ti_2 ->...-> Ti_ni),...Qq, (predicates)
   branch1, branch2, ... , branchr,                    (branches of the principle)
   forall (x1:Ti_1) (x2:Ti_2) ... (xni:Ti_ni),         (induction arguments)
   (HI: I prm1..prmp x1...xni)                         (optional main induction arg)
   -> (Qi x1...xni HI        (f prm1...prmp x1...xni)).(conclusion)
                   ^^        ^^^^^^^^^^^^^^^^^^^^^^^^
               optional        optional argument added if
               even if HI    principle generated by functional
             present above   induction, only if HI does not exist
             [indarg]                  [farg]

  HI is not present when the induction principle does not come directly from an
  inductive type (like when it is generated by functional induction for
  example). HI is present otherwise BUT may not appear in the conclusion
  (dependent principle). HI and (f...) cannot be both present.

  Principles taken from functional induction have the final (f...).*)

(* [rel_contexts] and [rel_declaration] actually contain triples, and
   lists are actually in reverse order to fit [compose_prod]. *)
type elim_scheme = {
  elimt: types;
  indref: GlobRef.t option;
  params: rel_context;      (* (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *)
  nparams: int;               (* number of parameters *)
  predicates: rel_context;  (* (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *)
  npredicates: int;           (* Number of predicates *)
  branches: rel_context;    (* branchr,...,branch1 *)
  nbranches: int;             (* Number of branches *)
  args: rel_context;        (* (xni, Ti_ni) ... (x1, Ti_1) *)
  nargs: int;                 (* number of arguments *)
  indarg: rel_declaration option; (* Some (H,I prm1..prmp x1...xni)
                                               if HI is in premisses, None otherwise *)
  concl: types;               (* Qi x1...xni HI (f...), HI and (f...)
                                 are optional and mutually exclusive *)
  indarg_in_concl: bool;      (* true if HI appears at the end of conclusion *)
  farg_in_concl: bool;        (* true if (f...) appears at the end of conclusion *)
}

let empty_scheme =
  {
    elimt = mkProp;
    indref = None;
    params = [];
    nparams = 0;
    predicates = [];
    npredicates = 0;
    branches = [];
    nbranches = 0;
    args = [];
    nargs = 0;
    indarg = None;
    concl = mkProp;
    indarg_in_concl = false;
    farg_in_concl = false;
  }

let make_base n id =
  if Int.equal n 0 || Int.equal n 1 then id
  else
    (* This extends the name to accept new digits if it already ends with *)
    (* digits *)
    Id.of_string (atompart_of_id (make_ident (Id.to_string id) (Some 0)))

(* Builds two different names from an optional inductive type and a
   number, also deals with a list of names to avoid. If the inductive
   type is None, then hyprecname is IHi where i is a number. *)
let make_up_names n ind_opt cname =
  let is_hyp = String.equal (atompart_of_id cname) "H" in
  let base = Id.to_string (make_base n cname) in
  let ind_prefix = "IH" in
  let base_ind =
    if is_hyp then
      match ind_opt with
        | None -> Id.of_string ind_prefix
        | Some ind_id -> add_prefix ind_prefix (Nametab.basename_of_global ind_id)
    else add_prefix ind_prefix cname in
  let hyprecname = make_base n base_ind in
  let avoid =
    if Int.equal n 1 (* Only one recursive argument *) || Int.equal n 0 then Id.Set.empty
    else
      (* Forbid to use cname, cname0, hyprecname and hyprecname0 *)
      (* in order to get names such as f1, f2, ... *)
      let avoid =
        Id.Set.add (make_ident (Id.to_string hyprecname) None)
        (Id.Set.singleton (make_ident (Id.to_string hyprecname) (Some 0))) in
      if not (String.equal (atompart_of_id cname) "H") then
        Id.Set.add (make_ident base (Some 0)) (Id.Set.add (make_ident base None) avoid)
      else avoid in
  Id.of_string base, hyprecname, avoid

let error_ind_scheme s = error (NotAnInductionScheme s)

let occur_rel sigma n c =
  let res = not (noccurn sigma n c) in
  res

(* This function splits the products of the induction scheme [elimt] into four
   parts:
   - branches, easily detectable (they are not referred by rels in the subterm)
   - what was found before branches (acc1) that is: parameters and predicates
   - what was found after branches (acc3) that is: args and indarg if any
   if there is no branch, we try to fill in acc3 with args/indargs.
   We also return the conclusion.
*)
let decompose_paramspred_branch_args sigma elimt =
  let open Context.Rel.Declaration in
  let rec cut_noccur elimt acc2 =
    match EConstr.kind sigma elimt with
      | Prod(nme,tpe,elimt') ->
          let hd_tpe,_ = decompose_app sigma (snd (decompose_prod_decls sigma tpe)) in
          if not (occur_rel sigma 1 elimt') && isRel sigma hd_tpe
          then cut_noccur elimt' (LocalAssum (nme,tpe)::acc2)
          else let acc3,ccl = decompose_prod_decls sigma elimt in acc2 , acc3 , ccl
      | App(_, _) | Rel _ -> acc2 , [] , elimt
      | _ -> error_ind_scheme "" in
  let rec cut_occur elimt acc1 =
    match EConstr.kind sigma elimt with
      | Prod(nme,tpe,c) when occur_rel sigma 1 c -> cut_occur c (LocalAssum (nme,tpe)::acc1)
      | Prod(nme,tpe,c) -> let acc2,acc3,ccl = cut_noccur elimt [] in acc1,acc2,acc3,ccl
      | App(_, _) | Rel _ -> acc1,[],[],elimt
      | _ -> error_ind_scheme "" in
  let acc1, acc2 , acc3, ccl = cut_occur elimt [] in
  (* Particular treatment when dealing with a dependent empty type elim scheme:
     if there is no branch, then acc1 contains all hyps which is wrong (acc1
     should contain parameters and predicate only). This happens for an empty
     type (See for example Empty_set_ind, as False would actually be ok). Then
     we must find the predicate of the conclusion to separate params_pred from
     args. We suppose there is only one predicate here. *)
  match acc2 with
  | [] ->
    let hyps,ccl = decompose_prod_decls sigma elimt in
    let hd_ccl_pred,_ = decompose_app sigma ccl in
    begin match EConstr.kind sigma hd_ccl_pred with
      | Rel i  -> let acc3,acc1 = List.chop (i-1) hyps in acc1 , [] , acc3 , ccl
      | _ -> error_ind_scheme ""
    end
  | _ -> acc1, acc2 , acc3, ccl


let exchange_hd_app sigma subst_hd t =
  let hd,args= decompose_app sigma t in mkApp (subst_hd, args)

(* Builds an elim_scheme from its type and calling form (const+binding). We
   first separate branches.  We obtain branches, hyps before (params + preds),
   hyps after (args <+ indarg if present>) and conclusion.  Then we proceed as
   follows:

   - separate parameters and predicates in params_preds. For that we build:
 forall (x1:Ti_1)(xni:Ti_ni) (HI:I prm1..prmp x1...xni), DUMMY x1...xni HI/farg
                             ^^^^^^^^^^^^^^^^^^^^^^^^^                  ^^^^^^^
                                       optional                           opt
     Free rels appearing in this term are parameters (branches should not
     appear, and the only predicate would have been Qi but we replaced it by
     DUMMY). We guess this heuristic catches all params.  TODO: generalize to
     the case where args are merged with branches (?) and/or where several
     predicates are cited in the conclusion.

   - finish to fill in the elim_scheme: indarg/farg/args and finally indref. *)
let compute_elim_sig sigma elimt =
  let open Context.Rel.Declaration in
  let params_preds,branches,args_indargs,conclusion =
    decompose_paramspred_branch_args sigma elimt in

  let ccl = exchange_hd_app sigma (mkVar (Id.of_string "__QI_DUMMY__")) conclusion in
  let concl_with_args = it_mkProd_or_LetIn ccl args_indargs in
  let nparams = Int.Set.cardinal (free_rels sigma concl_with_args) in
  let preds,params = List.chop (List.length params_preds - nparams) params_preds in

  (* A first approximation, further analysis will tweak it *)
  let res = ref { empty_scheme with
    (* This fields are ok: *)
    elimt = elimt; concl = conclusion;
    predicates = preds; npredicates = List.length preds;
    branches = branches; nbranches = List.length branches;
    farg_in_concl = isApp sigma ccl && isApp sigma (last_arg sigma ccl);
    params = params; nparams = nparams;
    (* all other fields are unsure at this point. Including these:*)
    args = args_indargs; nargs = List.length args_indargs; } in
  try
    (* Order of tests below is important. Each of them exits if successful. *)
    (* 1- First see if (f x...) is in the conclusion. *)
    if !res.farg_in_concl
    then begin
      res := { !res with
        indarg = None;
        indarg_in_concl = false; farg_in_concl = true };
      raise_notrace Exit
    end;
    (* 2- If no args_indargs (=!res.nargs at this point) then no indarg *)
    if Int.equal !res.nargs 0 then raise_notrace Exit;
    (* 3- Look at last arg: is it the indarg? *)
    ignore (
      match List.hd args_indargs with
        | LocalDef (hiname,_,hi) -> error_ind_scheme ""
        | LocalAssum (hiname,hi) ->
            let hi_ind, hi_args = decompose_app sigma hi in
            let hi_is_ind = (* hi est d'un type globalisable *)
              match EConstr.kind sigma hi_ind with
                | Ind (mind,_)  -> true
                | Var _ -> true
                | Const _ -> true
                | Construct _ -> true
                | _ -> false in
            let hi_args_enough = (* hi a le bon nbre d'arguments *)
              Int.equal (Array.length hi_args) (List.length params + !res.nargs -1) in
            (* FIXME: Ces deux tests ne sont pas suffisants. *)
            if not (hi_is_ind && hi_args_enough) then raise_notrace Exit (* No indarg *)
            else (* Last arg is the indarg *)
              res := {!res with
                indarg = Some (List.hd !res.args);
                indarg_in_concl = occur_rel sigma 1 ccl;
                args = List.tl !res.args; nargs = !res.nargs - 1;
              };
            raise_notrace Exit);
    raise_notrace Exit(* exit anyway *)
  with Exit -> (* Ending by computing indref: *)
    match !res.indarg with
      | None -> !res (* No indref *)
      | Some (LocalDef _) -> error_ind_scheme ""
      | Some (LocalAssum (_,ind)) ->
          let indhd,indargs = decompose_app sigma ind in
          try {!res with indref = Some (fst (destRef sigma indhd)) }
          with DestKO ->
            error CannotFindInductiveArgument

let compute_scheme_signature evd scheme names_info ind_type_guess =
  let open Context.Rel.Declaration in
  let f,l = decompose_app evd scheme.concl in
  (* Vérifier que les arguments de Qi sont bien les xi. *)
  let cond, check_concl =
    match scheme.indarg with
      | Some (LocalDef _) -> error NotAnInductionSchemeLetIn
      | None -> (* Non standard scheme *)
          let cond hd = EConstr.eq_constr evd hd ind_type_guess && not scheme.farg_in_concl
          in (cond, fun _ _ -> ())
      | Some (LocalAssum (_,ind)) -> (* Standard scheme from an inductive type *)
          let indhd,indargs = decompose_app_list evd ind in
          let cond hd = EConstr.eq_constr evd hd indhd in
          let check_concl is_pred p =
            (* Check again conclusion *)
            let ccl_arg_ok = is_pred (p + scheme.nargs + 1) f == IndArg in
            let ind_is_ok =
              List.equal (fun c1 c2 -> EConstr.eq_constr evd c1 c2)
                (List.lastn scheme.nargs indargs)
                (Context.Rel.instance_list mkRel 0 scheme.args) in
            if not (ccl_arg_ok && ind_is_ok) then
              error_ind_scheme "the conclusion of"
          in (cond, check_concl)
  in
  let is_pred n c =
    let hd = fst (decompose_app evd c) in
    match EConstr.kind evd hd with
      | Rel q when n < q && q <= n+scheme.npredicates -> IndArg
      | _ when cond hd -> RecArg
      | _ -> OtherArg
  in
  let rec check_branch p c =
    match EConstr.kind evd c with
      | Prod (_,t,c) ->
        (is_pred p t, true, not (Vars.noccurn evd 1 c)) :: check_branch (p+1) c
      | LetIn (_,_,_,c) ->
        (OtherArg, false, not (Vars.noccurn evd 1 c)) :: check_branch (p+1) c
      | _ when is_pred p c == IndArg -> []
      | _ -> raise_notrace Exit
  in
  let rec find_branches p lbrch =
    match lbrch with
      | LocalAssum (_,t) :: brs ->
        begin match check_branch p t with
        | lchck_brch ->
          let n = List.count (fun (b, _, _) -> b == RecArg) lchck_brch in
          let recvarname, hyprecname, avoid = make_up_names n scheme.indref names_info in
          let map (b, is_assum, dep) = {
            ba_kind = b;
            ba_assum = is_assum;
            ba_dep = dep;
            ba_name = if b == IndArg then hyprecname else recvarname;
          } in
          let namesign = List.map map lchck_brch in
          (avoid, namesign) :: find_branches (p+1) brs
        | exception Exit -> error_ind_scheme "the branches of"
        end
      | LocalDef _ :: _ -> error_ind_scheme "the branches of"
      | [] -> check_concl is_pred p; []
  in
  Array.of_list (find_branches 0 (List.rev scheme.branches))

let compute_case_signature env mind dep names_info =
  let indref = GlobRef.IndRef mind in
  let rec check_branch c = match Constr.kind c with
  | Prod (_,t,c) ->
    let hd, _ = Constr.decompose_app t in
    (* no recursive call in case analysis *)
    let arg = if Constr.isRefX indref hd then RecArg else OtherArg in
    (arg, true, not (CVars.noccurn 1 c)) :: check_branch c
  | LetIn (_,_,_,c) ->
    (OtherArg, false, not (CVars.noccurn 1 c)) :: check_branch c
  | _ -> []
  in
  let (mib, mip) = Inductive.lookup_mind_specif env mind in
  let find_branches k =
    let (ctx, typ) = mip.mind_nf_lc.(k) in
    let argctx = List.firstn mip.mind_consnrealdecls.(k) ctx in
    let _, args = Constr.decompose_app typ in
    let _, indices = Array.chop mib.mind_nparams args in
    let base =
      if dep then Array.append indices (Context.Rel.instance Constr.mkRel 0 argctx)
      else indices
    in
    let base = Constr.mkApp (Constr.mkProp, base) in (* only used for noccurn *)
    let lchck_brch = check_branch (Term.it_mkProd_or_LetIn base argctx) in
    let n = List.count (fun (b, _, _) -> b == RecArg) lchck_brch in
    let recvarname, hyprecname, avoid = make_up_names n (Some indref) names_info in
    let map (b, is_assum, dep) = {
      ba_kind = b;
      ba_assum = is_assum;
      ba_dep = dep;
      ba_name = recvarname;
    } in
    let namesign = List.map map lchck_brch in
    (avoid, namesign)
  in
  Array.init (Array.length mip.mind_consnames) find_branches

let error_cannot_recognize ind =
  user_err
    Pp.(str "Cannot recognize a statement based on " ++
        Nametab.pr_global_env Id.Set.empty (IndRef ind) ++ str".")

let guess_elim_shape env sigma isrec s hyp0 =
  let tmptyp0 = Typing.type_of_variable env hyp0 in
  let (mind, u), typ = Tacred.reduce_to_atomic_ind env sigma tmptyp0 in
  let is_elim = isrec && not (is_nonrec env mind) in
  let nparams =
    if is_elim then
      let gr = lookup_eliminator env mind s in
      let sigma, ind = Evd.fresh_global env sigma gr in
      let elimt = Retyping.get_type_of env sigma ind in
      let scheme = compute_elim_sig sigma elimt in
      let () = match scheme.indref with
      | None -> error_cannot_recognize mind
      | Some ref ->
        if QGlobRef.equal env ref (IndRef mind) then ()
        else error_cannot_recognize mind
      in
      scheme.nparams
    else
      let mib = Environ.lookup_mind (fst mind) env in
      mib.mind_nparams
  in
  let hd, args = decompose_app_list sigma typ in
  let (params, indices) = List.chop nparams args in
  is_elim, (mind, u), (hd, params, indices)

let given_elim env sigma hyp0 (elimc,lbind as e) =
  let tmptyp0 = Typing.type_of_variable env hyp0 in
  let ind_type_guess,_ = decompose_app sigma (snd (decompose_prod sigma tmptyp0)) in
  let sigma, elimt = Typing.type_of env sigma elimc in
  sigma, (e, elimt), ind_type_guess

type scheme_signature = (Id.Set.t * branch_argument list) array

type eliminator_source =
  | CaseOver of Id.t * (inductive * EInstance.t)
  | ElimOver of Id.t * (inductive * EInstance.t)
  | ElimUsing of Id.t * (Evd.econstr with_bindings * EConstr.types * scheme_signature)
  | ElimUsingList of (Evd.econstr with_bindings * EConstr.types * scheme_signature) * Id.t list * Id.t list * EConstr.t list

let find_induction_type env sigma isrec elim hyp0 sort = match elim with
| None ->
  let is_elim, ind, typ = guess_elim_shape env sigma isrec sort hyp0 in
  (* We drop the scheme and elimc/elimt waiting to know if it is dependent, this
    needs no update to sigma at this point. *)
  let elim = if is_elim then ElimOver (hyp0, ind) else CaseOver (hyp0, ind) in
  sigma, typ, elim
| Some (elimc, lbind as e) ->
  let sigma, elimt = Typing.type_of env sigma elimc in
  let scheme = compute_elim_sig sigma elimt in
  let () = if Option.is_empty scheme.indarg then error CannotFindInductiveArgument in
  let ref = match scheme.indref with
  | None -> error_ind_scheme ""
  | Some ref -> ref
  in
  let tmptyp0 = Typing.type_of_variable env hyp0 in
  let indtyp = reduce_to_atomic_ref env sigma ref tmptyp0 in
  let hd, args = decompose_app_list sigma indtyp in
  let indsign = compute_scheme_signature sigma scheme hyp0 hd in
  let (params, indices) = List.chop scheme.nparams args in
  sigma, (hd, params, indices), ElimUsing (hyp0, (e, elimt, indsign))

let is_functional_induction elimc gl =
  let sigma = Tacmach.project gl in
  let scheme = compute_elim_sig sigma (Tacmach.pf_get_type_of gl (fst elimc)) in
  (* The test is not safe: with non-functional induction on non-standard
     induction scheme, this may fail *)
  Option.is_empty scheme.indarg

(* Instantiate all meta variables of elimclause using lid, some elts
   of lid are parameters (first ones), the other are
   arguments. Returns the clause obtained.  *)
let recolle_clenv i params args elimclause gl =
  let lindmv = Array.of_list (clenv_arguments elimclause) in
  let k = match i with None -> Array.length lindmv - List.length args | Some i -> i in
  (* parameters correspond to first elts of lid. *)
  let clauses_params = List.mapi (fun i id -> id, lindmv.(i)) params in
  let clauses_args = List.mapi (fun i id -> id, lindmv.(k+i)) args in
  let clauses = clauses_params@clauses_args in
  (* iteration of clenv_instantiate with all infos we have. *)
  List.fold_right
    (fun e acc ->
      let x, i = e in
      let y = pf_get_hyp_typ x gl in
      let elimclause' = clenv_instantiate i acc (mkVar x, y) in
      elimclause')
    (List.rev clauses)
    elimclause

(* Unification of the goal and the principle applied to meta variables:
   (elimc ?i ?j ?k...?l). This solves partly meta variables (and may
    produce new ones). Then refine with the resulting term with holes.
*)
let induction_tac with_evars params indvars (elim, elimt) =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let clause, bindings, index = match elim with
  | ElimConstant c ->
    let i = index_of_ind_arg sigma elimt in
    (mkConstU c, elimt), NoBindings, Some i
  | ElimClause (elimc, lbindelimc) ->
    (elimc, elimt), lbindelimc, None
  in
  (* elimclause contains this: (elimc ?i ?j ?k...?l) *)
  let elimclause = make_clenv_binding env sigma clause bindings in
  (* elimclause' is built from elimclause by instantiating all args and params. *)
  let elimclause = recolle_clenv index params indvars elimclause gl in
  Clenv.res_pf ~with_evars ~flags:(elim_flags ()) elimclause
  end

let destruct_tac with_evars indvar dep =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let ty = Typing.type_of_variable env indvar in
  Clenv.case_pf ~with_evars ~dep (mkVar indvar, ty)
  end

(* Apply induction "in place" taking into account dependent
   hypotheses from the context, replacing the main hypothesis on which
   induction applies with the induction hypotheses *)

let apply_induction_in_context with_evars inhyps elim indvars names =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let concl = Tacmach.pf_concl gl in
    let hyp0 = match elim with
    | ElimUsing (hyp0, _) | ElimOver (hyp0, _) | CaseOver (hyp0, _) -> Some hyp0
    | ElimUsingList _ -> None
    in
    let statuslists,lhyp0,toclear,deps,avoid,dep_in_hyps = cook_sign hyp0 inhyps indvars env sigma in
    let tmpcl = it_mkNamedProd_or_LetIn sigma concl deps in
    let s = Retyping.get_sort_family_of env sigma tmpcl in
    let deps_cstr =
      List.fold_left
        (fun a decl -> if NamedDecl.is_local_assum decl then (mkVar (NamedDecl.get_id decl))::a else a) [] deps in
    (* Wait the last moment to guess the eliminator so as to know if we
      need a dependent one or not *)
    let (sigma, isrec, induct_tac, indsign) = match elim with
    | CaseOver (id, (mind, u)) ->
      let dep_in_concl = occur_var env sigma id concl in
      let dep = dep_in_hyps || dep_in_concl in
      let dep = dep || default_case_analysis_dependence env mind in
      let indsign = compute_case_signature env mind dep id in
      let tac = destruct_tac with_evars id dep in
      sigma, false, tac, indsign
    | ElimOver (id, (mind, u)) ->
      let sigma, ind = find_ind_eliminator env sigma mind s in
      (* FIXME: we should store this instead of recomputing it *)
      let elimt = Retyping.get_type_of env sigma (mkConstU ind) in
      let scheme = compute_elim_sig sigma elimt in
      let indsign = compute_scheme_signature sigma scheme id (mkIndU (mind, u)) in
      let tac = induction_tac with_evars [] [id] (ElimConstant ind, elimt) in
      sigma, true, tac, indsign
    | ElimUsing (hyp0, (elim, elimt, indsign)) ->
      let tac = induction_tac with_evars [] [hyp0] (ElimClause elim, elimt) in
      sigma, (* bugged, should be computed *) true, tac, indsign
    | ElimUsingList ((elim, elimt, indsign), params, realindvars, patts) ->
      let tac = Tacticals.tclTHENLIST [
        (* pattern to make the predicate appear. *)
        Tactics.reduce (Pattern (List.map inj_with_occurrences patts)) onConcl;
        (* Induction by "refine (indscheme ?i ?j ?k...)" + resolution of all
          possible holes using arguments given by the user (but the
          functional one). *)
        (* FIXME: Tester ca avec un principe dependant et non-dependant *)
        induction_tac with_evars params realindvars (ElimClause elim, elimt);
      ] in
      sigma, (* bugged, should be computed *) true, tac, indsign
    in
    let branchletsigns =
      let f ba = ba.ba_assum in
      Array.map (fun (_,l) -> List.map f l) indsign in
    let names = compute_induction_names true branchletsigns names in
    let () = Array.iter (Tactics.Internal.check_name_unicity env toclear []) names in
    let tac =
    (if isrec then Tacticals.tclTHENFIRSTn else Tacticals.tclTHENLASTn)
      (Tacticals.tclTHENLIST [
        (* Generalize dependent hyps (but not args) *)
        if deps = [] then Proofview.tclUNIT () else Tactics.apply_type ~typecheck:false tmpcl deps_cstr;
        (* side-conditions in elim (resp case) schemes come last (resp first) *)
        induct_tac;
        Tacticals.tclMAP expand_hyp toclear;
      ])
      (Array.map2
         (induct_discharge with_evars lhyp0 avoid
            (re_intro_dependent_hypotheses statuslists))
         indsign names)
    in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) tac
  end

let induction_with_atomization_of_ind_arg isrec with_evars elim names hyp0 inhyps =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let sort = Tacticals.elimination_sort_of_goal gl in
  let sigma, ty, elim_info = find_induction_type env sigma isrec elim hyp0 sort in
  let letins, avoid, t = atomize_param_of_ind env sigma ty in
  let letins = tclMAP (fun (na, c) -> Tactics.letin_tac None (Name na) c None allHypsAndConcl) letins in
  Tacticals.tclTHENLIST [
    Proofview.Unsafe.tclEVARS sigma;
    letins;
    Tactics.change_in_hyp ~check:false None (Tactics.make_change_arg t) (hyp0, InHypTypeOnly);
    apply_induction_in_context with_evars inhyps elim_info avoid names
  ]
  end

let msg_not_right_number_induction_arguments scheme =
  str"Not the right number of induction arguments (expected " ++
  pr_enum (fun x -> x) [
    if scheme.farg_in_concl then str "the function name" else mt();
    if scheme.nparams != 0 then int scheme.nparams ++ str (String.plural scheme.nparams " parameter") else mt ();
    if scheme.nargs != 0 then int scheme.nargs ++ str (String.plural scheme.nargs " argument") else mt ()] ++ str ")."

(* Induction on a list of induction arguments. Analyze the elim
   scheme (which is mandatory for multiple ind args), check that all
   parameters and arguments are given (mandatory too).
   Main differences with induction_from_context is that there is no
   main induction argument. On the other hand, all args and params
   must be given, so we help a bit the unifier by making the "pattern"
   by hand before calling induction_tac *)
let induction_without_atomization isrec with_evars elim names lid =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let hyp0 = List.hd lid in
  (* Check that the elimination scheme has a form similar to the
    elimination schemes built by Rocq. Schemes may have the standard
    form computed from an inductive type OR (feb. 2006) a non standard
    form. That is: with no main induction argument and with an optional
    extra final argument of the form (f x y ...) in the conclusion. In
    the non standard case, naming of generated hypos is slightly
    different. *)
  let (sigma, (elimc, elimt), ind_type_guess) = given_elim env sigma hyp0 elim in
  let scheme = compute_elim_sig sigma elimt in
  let indsign = compute_scheme_signature sigma scheme hyp0 ind_type_guess in
  let nargs_indarg_farg =
    scheme.nargs + (if scheme.farg_in_concl then 1 else 0) in
  if not (Int.equal (List.length lid) (scheme.nparams + nargs_indarg_farg))
  then
    let info = Exninfo.reify () in
    Tacticals.tclZEROMSG ~info (msg_not_right_number_induction_arguments scheme)
  else
  let indvars,lid_params = List.chop nargs_indarg_farg lid in
  (* terms to patternify we must patternify indarg or farg if present in concl *)
  let realindvars = List.rev (if scheme.farg_in_concl then List.tl indvars else indvars) in
  let lidcstr = List.map mkVar (List.rev indvars) in
  let params = List.rev lid_params in
  let indvars =
    (* Temporary hack for compatibility, while waiting for better
       analysis of the form of induction schemes: a scheme like
       gt_wf_rec was taken as a functional scheme with no parameters,
       but by chance, because of the addition of at least hyp0 for
       cook_sign, it behaved as if there was a real induction arg. *)
    if List.is_empty indvars then Id.Set.singleton (List.hd lid_params) else Id.Set.of_list indvars in
  let elim = ElimUsingList ((elimc, scheme.elimt, indsign), params, realindvars, lidcstr) in
  apply_induction_in_context with_evars [] elim indvars names
  end

(* assume that no occurrences are selected *)
let clear_unselected_context id inhyps cls =
  Proofview.Goal.enter begin fun gl ->
  if occur_var (Tacmach.pf_env gl) (Tacmach.project gl) id (Tacmach.pf_concl gl) &&
    cls.concl_occs == NoOccurrences
  then error (MentionConclusionDependentOn id);
  match cls.onhyps with
  | Some hyps ->
      let to_erase d =
        let id' = NamedDecl.get_id d in
        if Id.List.mem id' inhyps then (* if selected, do not erase *) None
        else
          (* erase if not selected and dependent on id or selected hyps *)
          let test id = occur_var_in_decl (Tacmach.pf_env gl) (Tacmach.project gl) id d in
          if List.exists test (id::inhyps) then Some id' else None in
      let ids = List.map_filter to_erase (Proofview.Goal.hyps gl) in
      clear ids
  | None -> Proofview.tclUNIT ()
  end

let use_bindings env sigma elim must_be_closed (c,lbind) typ =
  let typ =
    (* Normalize [typ] until the induction reference becomes plainly visible *)
    match elim with
    | None ->
      (* w/o an scheme, the term has to be applied at least until
         obtaining an inductive type (even though the arity might be
         known only by pattern-matching, as in the case of a term of
         the form "nat_rect ?A ?o ?s n", with ?A to be inferred by
         matching. *)
      let sign,t = whd_decompose_prod env sigma typ in it_mkProd t sign
    | Some (elimc, _) ->
      (* Otherwise, we compute the induction reference of the scheme
         and go looking for that. *)
      let sigma, elimt = Typing.type_of env sigma elimc in
      let scheme = compute_elim_sig sigma elimt in
      match scheme.indref with
      | None -> error CannotFindInductiveArgument
      | Some indref ->
        Tacred.reduce_to_quantified_ref ~allow_failure:true env sigma indref typ
  in
  let rec find_clause typ =
    try
      let indclause = make_clenv_binding env sigma (c,typ) lbind in
      if must_be_closed && occur_meta (clenv_evd indclause) (clenv_value indclause) then
        error NeedFullyAppliedArgument;
      (* We lose the possibility of coercions in with-bindings *)
      let metas = Clenv.clenv_meta_list indclause in
      let sigma, metas, term = pose_all_metas_as_evars ~metas env (clenv_evd indclause) (clenv_value indclause) in
      let sigma, metas, typ = pose_all_metas_as_evars ~metas env sigma (clenv_type indclause) in
      sigma, term, typ
    with e when noncritical e ->
    match red_product env sigma typ with
    | None -> raise e
    | Some typ -> find_clause typ
  in
  find_clause typ

let check_expected_type env sigma (elimc,bl) elimt =
  (* Compute the expected template type of the term in case a using
     clause is given *)
  let sign,_ = whd_decompose_prod env sigma elimt in
  let n = List.length sign in
  if n == 0 then error SchemeDontApply;
  let sigma,cl = EClause.make_evar_clause env sigma ~len:(n - 1) elimt in
  let sigma = EClause.solve_evar_clause env sigma true cl bl in
  let (_,u,_) = destProd sigma (whd_all env sigma cl.cl_concl) in
  fun t -> match Evarconv.unify_leq_delay env sigma t u with
    | _sigma -> true
    | exception Evarconv.UnableToUnify _ -> false

let check_enough_applied env sigma elim =
  (* A heuristic to decide whether the induction arg is enough applied *)
  match elim with
  | None ->
      (* No eliminator given *)
      fun u ->
      let t,_ = decompose_app sigma (whd_all env sigma u) in isInd sigma t
  | Some elimc ->
      let elimt = Retyping.get_type_of env sigma (fst elimc) in
      let scheme = compute_elim_sig sigma elimt in
      match scheme.indref with
      | None ->
         (* in the absence of information, do not assume it may be
            partially applied *)
          fun _ -> true
      | Some _ ->
          (* Last argument is supposed to be the induction argument *)
          check_expected_type env sigma elimc elimt

let guard_no_unifiable = Proofview.guard_no_unifiable >>= function
  | None -> Proofview.tclUNIT ()
  | Some l ->
    Proofview.tclENV     >>= function env ->
    Proofview.tclEVARMAP >>= function sigma ->
    let info = Exninfo.reify () in
    Proofview.tclZERO ~info (RefinerError (env, sigma, UnresolvedBindings l))

let pose_induction_arg_then isrec with_evars (is_arg_pure_hyp,from_prefix) elim
     id ((pending,(c0,lbind)),(eqname,names)) t0 inhyps cls tac =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let ccl = Proofview.Goal.concl gl in
  let check = check_enough_applied env sigma elim in
  let sigma', c, _ = use_bindings env sigma elim false (c0,lbind) t0 in
  let abs = AbstractPattern (from_prefix,check,Name id,(pending,c),cls) in
  let (id,sign,_,lastlhyp,ccl,res) = make_abstraction env sigma' ccl abs in
  match res with
  | None ->
      (* pattern not found *)
      let with_eq = Option.map (fun eq -> (false,mk_eq_name env id eq)) eqname in
      let inhyps = if List.is_empty inhyps then inhyps else Option.fold_left (fun inhyps (_,heq) -> heq::inhyps) inhyps with_eq in
      (* we restart using bindings after having tried type-class
         resolution etc. on the term given by the user *)
      let flags = tactic_infer_flags (with_evars && (* do not give a success semantics to edestruct on an open term yet *) false) in
      let (sigma, c0) = finish_evar_resolution ~flags env sigma (pending,c0) in
      let tac =
      (if isrec then
          (* Historically, induction has side conditions last *)
          Tacticals.tclTHENFIRST
       else
          (* and destruct has side conditions first *)
          Tacticals.tclTHENLAST)
      (Tacticals.tclTHENLIST [
        Refine.refine_with_principal ~typecheck:false begin fun sigma ->
          let b = not with_evars && with_eq != None in
          let sigma, c, t = use_bindings env sigma elim b (c0,lbind) t0 in
          mkletin_goal env sigma with_eq false (id,lastlhyp,ccl,c) (Some t)
        end;
        if with_evars then Proofview.shelve_unifiable else guard_no_unifiable;
        if is_arg_pure_hyp
        then Proofview.tclEVARMAP >>= fun sigma -> Tacticals.tclTRY (clear [destVar sigma c0])
        else Proofview.tclUNIT ();
        if isrec then Proofview.cycle (-1) else Proofview.tclUNIT ()
      ])
      (tac inhyps)
      in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) tac

  | Some (sigma', c) ->
      (* pattern found *)
      (* TODO: if ind has predicate parameters, use JMeq instead of eq *)
      let env = reset_with_named_context sign env in
      let with_eq = Option.map (fun eq -> (false,mk_eq_name env id eq)) eqname in
      let inhyps = if List.is_empty inhyps then inhyps else Option.fold_left (fun inhyps (_,heq) -> heq::inhyps) inhyps with_eq in
      let tac =
      Tacticals.tclTHENLIST [
        Refine.refine_with_principal ~typecheck:false begin fun sigma ->
          mkletin_goal env sigma with_eq true (id,lastlhyp,ccl,c) None
        end;
        (tac inhyps)
      ]
      in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma') tac
  end

let has_generic_occurrences_but_goal cls id env sigma ccl =
  clause_with_generic_context_selection cls &&
  (* TODO: whd_evar of goal *)
  (cls.concl_occs != NoOccurrences || not (occur_var env sigma id ccl))

let induction_gen clear_flag isrec with_evars elim
    ((_pending,(c,lbind)),(eqname,names) as arg) cls =
  let inhyps = match cls with
  | Some {onhyps=Some hyps} -> List.map (fun ((_,id),_) -> id) hyps
  | _ -> [] in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let evd = Proofview.Goal.sigma gl in
  let ccl = Proofview.Goal.concl gl in
  let cls = Option.default allHypsAndConcl cls in
  let t = typ_of env evd c in
  let is_arg_pure_hyp =
    isVar evd c && not (mem_named_context_val (destVar evd c) (Global.named_context_val ()))
    && lbind == NoBindings && not with_evars && Option.is_empty eqname
    && clear_flag == None
    && has_generic_occurrences_but_goal cls (destVar evd c) env evd ccl in
  let enough_applied = check_enough_applied env evd elim t in
  if is_arg_pure_hyp && enough_applied then
    (* First case: induction on a variable already in an inductive type and
       with maximal abstraction over the variable.
       This is a situation where the induction argument is a
       clearable variable of the goal w/o occurrence selection
       and w/o equality kept: no need to generalize *)
    let id = destVar evd c in
    Tacticals.tclTHEN
      (clear_unselected_context id inhyps cls)
      (induction_with_atomization_of_ind_arg
         isrec with_evars elim names id inhyps)
  else
  (* Otherwise, we look for the pattern, possibly adding missing arguments and
     declaring the induction argument as a new local variable *)
    let id =
    (* Type not the right one if partially applied but anyway for internal use*)
      let avoid = match eqname with
        | Some {CAst.v=IntroIdentifier id} -> Id.Set.singleton id
        | _ -> Id.Set.empty in
      let x = id_of_name_using_hdchar env evd t Anonymous in
      new_fresh_id avoid x gl in
    let info_arg = (is_arg_pure_hyp, not enough_applied) in
    pose_induction_arg_then
      isrec with_evars info_arg elim id arg t inhyps cls
    (induction_with_atomization_of_ind_arg
       isrec with_evars elim names id)
  end

(* Induction on a list of arguments. First make induction arguments
   atomic (using letins), then do induction. The specificity here is
   that all arguments and parameters of the scheme are given
   (mandatory for the moment), so we don't need to deal with
    parameters of the inductive type as in induction_gen. *)
let induction_gen_l isrec with_evars elim names lc =
  let newlc = ref [] in
  let lc = List.map (function
    | (c,None) -> c
    | (c,Some{CAst.loc;v=eqname}) ->
      error ?loc (DontKnowWhatToDoWith eqname)) lc in
  let rec atomize_list l =
    match l with
      | [] -> Proofview.tclUNIT ()
      | c::l' ->
          Proofview.tclEVARMAP >>= fun sigma ->
          match EConstr.kind sigma c with
            | Var id when not (mem_named_context_val id (Global.named_context_val ()))
                && not with_evars ->
                let () = newlc:= id::!newlc in
                atomize_list l'

            | _ ->
                Proofview.Goal.enter begin fun gl ->
                let sigma, t = pf_apply Typing.type_of gl c in
                let x = id_of_name_using_hdchar (Proofview.Goal.env gl) sigma t Anonymous in
                let id = new_fresh_id Id.Set.empty x gl in
                let newl' = List.map (fun r -> replace_term sigma c (mkVar id) r) l' in
                let () = newlc:=id::!newlc in
                Tacticals.tclTHENLIST [
                  tclEVARS sigma;
                  Tactics.letin_tac None (Name id) c None allHypsAndConcl;
                  atomize_list newl';
                ]
                end in
  Tacticals.tclTHENLIST
    [
      (atomize_list lc);
      (Proofview.tclUNIT () >>= fun () -> (* ensure newlc has been computed *)
        induction_without_atomization isrec with_evars elim names !newlc)
    ]

(* Induction either over a term, over a quantified premisse, or over
   several quantified premisses (like with functional induction
   principles).
   TODO: really unify induction with one and induction with several
   args *)
let induction_destruct isrec with_evars (lc,elim) =
  match lc with
  | [] -> assert false (* ensured by syntax, but if called inside caml? *)
  | [c,(eqname,names as allnames),cls] ->
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    match elim with
    | Some elim when is_functional_induction elim gl ->
      (* Standard induction on non-standard induction schemes *)
      (* will be removable when is_functional_induction will be more clever *)
      if not (Option.is_empty cls) then error (UnsupportedInClause true);
      let _,c = force_destruction_arg false env sigma c in
      onInductionArg
        (fun _clear_flag c ->
          induction_gen_l isrec with_evars elim names
            [with_no_bindings c,eqname]) c
    | _ ->
      (* standard induction *)
      onOpenInductionArg env sigma
      (fun clear_flag c -> induction_gen clear_flag isrec with_evars elim (c,allnames) cls) c
    end
  | _ ->
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    match elim with
    | None ->
      (* Several arguments, without "using" clause *)
      (* TODO: Do as if the arguments after the first one were called with *)
      (* "destruct", but selecting occurrences on the initial copy of *)
      (* the goal *)
      let (a,b,cl) = List.hd lc in
      let l = List.tl lc in
      (* TODO *)
      Tacticals.tclTHEN
        (onOpenInductionArg env sigma (fun clear_flag a ->
          induction_gen clear_flag isrec with_evars None (a,b) cl) a)
        (Tacticals.tclMAP (fun (a,b,cl) ->
          Proofview.Goal.enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let sigma = Tacmach.project gl in
          onOpenInductionArg env sigma (fun clear_flag a ->
            induction_gen clear_flag false with_evars None (a,b) cl) a
          end) l)
    | Some elim ->
      (* Several induction hyps with induction scheme *)
      let lc = List.map (on_pi1 (fun c -> snd (force_destruction_arg false env sigma c))) lc in
      let newlc =
        List.map (fun (x,(eqn,names),cls) ->
          if cls != None then error UnsupportedEqnClause;
          match x with (* FIXME: should we deal with ElimOnIdent? *)
          | _clear_flag,ElimOnConstr x ->
              if eqn <> None then error (UnsupportedInClause false);
              (with_no_bindings x,names)
          | _ -> error DontKnowWhereToFindArgument)
          lc in
      (* Check that "as", if any, is given only on the last argument *)
      let names,rest = List.sep_last (List.map snd newlc) in
      if List.exists (fun n -> not (Option.is_empty n)) rest then
        error MultipleAsAndUsingClauseOnlyList;
      let newlc = List.map (fun (x,_) -> (x,None)) newlc in
      induction_gen_l isrec with_evars elim names newlc
    end

let induction ev clr c l e =
  induction_gen clr true ev e
    ((None,(c,NoBindings)),(None,l)) None

let destruct ev clr c l e =
  induction_gen clr false ev e
    ((None,(c,NoBindings)),(None,l)) None
