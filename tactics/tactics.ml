(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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
open Inductiveops
open Reductionops
open Evd
open Tacred
open Genredexpr
open Logic
open Clenv
open Tacticals
open Hipattern
open Rocqlib
open Evarutil
open Indrec
open Pretype_errors
open Unification
open Locus
open Locusops
open Tactypes
open Proofview.Notations
open Context.Named.Declaration

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

let tclEVARS = Proofview.Unsafe.tclEVARS
let tclEVARSTHEN sigma t = Proofview.tclTHEN (tclEVARS sigma) t

let typ_of env sigma c =
  let open Retyping in
  try get_type_of ~lax:true env sigma c
  with RetypeError e ->
    user_err (print_retype_error e)

open Goptions

let clear_hyp_by_default = ref false

let use_clear_hyp_by_default () = !clear_hyp_by_default

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Default";"Clearing";"Used";"Hypotheses"];
      optread  = (fun () -> !clear_hyp_by_default) ;
      optwrite = (fun b -> clear_hyp_by_default := b) }

(*********************************************)
(*                 Errors                    *)
(*********************************************)

exception IntroAlreadyDeclared of Id.t
exception ClearDependency of env * evar_map * Id.t option * Evarutil.clear_dependency_error * GlobRef.t option
exception ReplacingDependency of env * evar_map * Id.t * Evarutil.clear_dependency_error * GlobRef.t option
exception AlreadyUsed of Id.t
exception UsedTwice of Id.t
exception VariableHasNoValue of Id.t
exception ConvertIncompatibleTypes of env * evar_map * constr * constr
exception ConvertNotAType
exception NotConvertible
exception NotUnfoldable
exception NoQuantifiedHypothesis of quantified_hypothesis * bool
exception CannotFindInstance of Id.t
exception NothingToRewrite of Id.t
exception IllFormedEliminationType
exception UnableToApplyLemma of env * evar_map * constr * constr
exception DependsOnBody of Id.t list * Id.Set.t * Id.t option
exception NotRightNumberConstructors of int
exception NotEnoughConstructors
exception ConstructorNumberedFromOne
exception NoConstructors
exception UnexpectedExtraPattern of int option * delayed_open_constr intro_pattern_expr
exception CannotFindInductiveArgument
exception OneIntroPatternExpected
exception KeepAndClearModifierOnlyForHypotheses
exception FixpointOnNonInductiveType
exception NotEnoughProducts
exception AllMethodsInCoinductiveType
exception ReplacementIllTyped of exn
exception NotEnoughPremises
exception NeedDependentProduct

let error ?loc e =
  Loc.raise ?loc e

let clear_in_global_msg = function
  | None -> mt ()
  | Some ref -> str " implicitly in " ++ Printer.pr_global ref

let clear_dependency_msg env sigma id err inglobal =
  let ppidupper = function Some id -> Id.print id | None -> str "This variable" in
  let ppid = function Some id -> Id.print id | None -> str "this variable" in
  let pp = clear_in_global_msg inglobal in
  match err with
  | Evarutil.OccurHypInSimpleClause None ->
      ppidupper id ++ str " is used" ++ pp ++ str " in conclusion."
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      ppidupper id ++ strbrk " is used" ++ pp ++ str " in hypothesis " ++ Id.print id' ++ str"."
  | Evarutil.EvarTypingBreak ev ->
      str "Cannot remove " ++ ppid id ++
      strbrk " without breaking the typing of " ++
      Printer.pr_leconstr_env env sigma (mkEvar ev) ++ str"."
  | Evarutil.NoCandidatesLeft ev ->
      str "Cannot remove " ++ ppid id ++ str " as it would leave the existential " ++
      Printer.pr_existential_key env sigma ev ++ str" without candidates."

let replacing_dependency_msg env sigma id err inglobal =
  let pp = clear_in_global_msg inglobal in
  match err with
  | Evarutil.OccurHypInSimpleClause None ->
      str "Cannot change " ++ Id.print id ++ str ", it is used" ++ pp ++ str " in conclusion."
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      str "Cannot change " ++ Id.print id ++
      strbrk ", it is used" ++ pp ++ str " in hypothesis " ++ Id.print id' ++ str"."
  | Evarutil.EvarTypingBreak ev ->
      str "Cannot change " ++ Id.print id ++
      strbrk " without breaking the typing of " ++
      Printer.pr_leconstr_env env sigma (mkEvar ev) ++ str"."
  | Evarutil.NoCandidatesLeft ev ->
      str "Cannot change " ++ Id.print id ++ str " as it would leave the existential " ++
      Printer.pr_existential_key env sigma ev ++ str" without candidates."

let msg_quantified_hypothesis = function
  | NamedHyp id ->
      str "quantified hypothesis named " ++ Id.print id.CAst.v
  | AnonHyp n ->
      pr_nth n ++
      str " non dependent hypothesis"

let explain_unexpected_extra_pattern bound pat =
  let nb = Option.get bound in
  let s1,s2,s3 = match pat with
  | IntroNaming (IntroIdentifier _) ->
      "name", (String.plural nb " introduction pattern"), "no"
  | _ -> "introduction pattern", "", "none" in
  str "Unexpected " ++ str s1 ++ str " (" ++
  (if Int.equal nb 0 then (str s3 ++ str s2) else
   (str "at most " ++ int nb ++ str s2)) ++ spc () ++
  str (if Int.equal nb 1 then "was" else "were") ++
  strbrk " expected in the branch)."

exception Unhandled

let wrap_unhandled f e =
  try Some (f e)
  with Unhandled -> None

let tactic_interp_error_handler = function
  | IntroAlreadyDeclared id ->
      Id.print id ++ str " is already declared."
  | ClearDependency (env,sigma,id,err,inglobal) ->
      clear_dependency_msg env sigma id err inglobal
  | ReplacingDependency (env,sigma,id,err,inglobal) ->
      replacing_dependency_msg env sigma id err inglobal
  | AlreadyUsed id ->
      Id.print id ++ str " is already used."
  | UsedTwice id ->
      Id.print id ++ str" is used twice."
  | VariableHasNoValue id ->
      Id.print id ++ str" is not a defined hypothesis."
  | ConvertIncompatibleTypes (env,sigma,t1,t2) ->
      str "The first term has type" ++ spc () ++
      quote (Termops.Internal.print_constr_env env sigma t1) ++ spc () ++
      strbrk "while the second term has incompatible type" ++ spc () ++
      quote (Termops.Internal.print_constr_env env sigma t2) ++ str "."
  | ConvertNotAType ->
      str "Not a type."
  | NotConvertible ->
      str "Not convertible."
  | NotUnfoldable ->
     str "Cannot unfold a non-constant."
  | NoQuantifiedHypothesis (id,red) ->
      str "No " ++ msg_quantified_hypothesis id ++
      strbrk " in current goal" ++
      (if red then strbrk " even after head-reduction" else mt ()) ++ str"."
  | CannotFindInstance id ->
      str "Cannot find an instance for " ++ Id.print id ++ str"."
  | NothingToRewrite id ->
      str "Nothing to rewrite in " ++ Id.print id ++ str"."
  | IllFormedEliminationType ->
      str "The type of elimination clause is not well-formed."
  | UnableToApplyLemma (env,sigma,thm,t) ->
      str "Unable to apply lemma of type" ++ brk(1,1) ++
      quote (Printer.pr_leconstr_env env sigma thm) ++ spc() ++
      str "on hypothesis of type" ++ brk(1,1) ++
      quote (Printer.pr_leconstr_env env sigma t) ++
      str "."
  | DependsOnBody (idl,ids,where) ->
     let idl = List.filter (fun id -> Id.Set.mem id ids) idl in
     let on_the_bodies = function
       | [] -> assert false
       | [id] -> str " depends on the body of " ++ Id.print id
       | l -> str " depends on the bodies of " ++ pr_sequence Id.print l
     in
     (match where with
     | None -> str "Conclusion" ++ on_the_bodies idl
     | Some id -> str "Hypothesis " ++ Id.print id ++ on_the_bodies idl)
  | NotRightNumberConstructors n ->
      str "Not an inductive goal with " ++ int n ++ str (String.plural n " constructor") ++ str "."
  | NotEnoughConstructors ->
      str "Not enough constructors."
  | ConstructorNumberedFromOne ->
      str "The constructors are numbered starting from 1."
  | NoConstructors ->
      str "The type has no constructors."
  | UnexpectedExtraPattern (bound,pat) ->
      explain_unexpected_extra_pattern bound pat
  | CannotFindInductiveArgument ->
      str "Cannot find inductive argument of elimination scheme."
  | OneIntroPatternExpected ->
      str "Introduction pattern for one hypothesis expected."
  | KeepAndClearModifierOnlyForHypotheses ->
      str "keep/clear modifiers apply only to hypothesis names."
  | FixpointOnNonInductiveType ->
      str "Cannot do a fixpoint on a non inductive type."
  | NotEnoughProducts ->
      str "Not enough products."
  | AllMethodsInCoinductiveType ->
      str "All methods must construct elements in coinductive types."
  | ReplacementIllTyped e ->
      str "Replacement would lead to an ill-typed term:" ++ spc () ++ CErrors.print e
  | NotEnoughPremises ->
      str "Applied theorem does not have enough premises."
  | NeedDependentProduct ->
      str "Needs a non-dependent product."
  | _ -> raise Unhandled

let _ = CErrors.register_handler (wrap_unhandled tactic_interp_error_handler)

let error_clear_dependency env sigma id err inglobal =
  error (ClearDependency (env,sigma,Some id,err,inglobal))

let error_replacing_dependency env sigma id err inglobal =
  error (ReplacingDependency (env,sigma,id,err,inglobal))

(*********************************************)
(*                 Tactics                   *)
(*********************************************)

(******************************************)
(*           Primitive tactics            *)
(******************************************)

(** This tactic creates a partial proof realizing the introduction rule, but
    does not check anything. *)
let unsafe_intro env decl ~relevance b =
  Refine.refine_with_principal ~typecheck:false begin fun sigma ->
    let ctx = named_context_val env in
    let nctx = push_named_context_val decl ctx in
    let inst = EConstr.identity_subst_val (named_context_val env) in
    let ninst = SList.cons (mkRel 1) inst in
    let nb = subst1 (mkVar (NamedDecl.get_id decl)) b in
    let (sigma, ev) = new_pure_evar nctx sigma ~relevance nb in
    (sigma, mkLambda_or_LetIn (NamedDecl.to_rel_decl decl) (mkEvar (ev, ninst)),
     Some ev)
  end

let introduction id =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let relevance = Proofview.Goal.relevance gl in
    let sigma = Tacmach.project gl in
    let hyps = named_context_val (Proofview.Goal.env gl) in
    let env = Proofview.Goal.env gl in
    let () = if mem_named_context_val id hyps then
      error (IntroAlreadyDeclared id)
    in
    let open Context.Named.Declaration in
    match EConstr.kind sigma concl with
    | Prod (id0, t, b) -> unsafe_intro env (LocalAssum ({id0 with binder_name=id}, t)) ~relevance b
    | LetIn (id0, c, t, b) -> unsafe_intro env (LocalDef ({id0 with binder_name=id}, c, t)) ~relevance b
    | _ -> raise (RefinerError (env, sigma, IntroNeedsProduct))
  end

(* Not sure if being able to disable [cast] is useful. Uses seem picked somewhat randomly. *)
let convert_concl ~cast ~check ty k =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let conclty = Proofview.Goal.concl gl in
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma =
        if check then begin
          let sigma, _ = Typing.type_of env sigma ty in
          match Reductionops.infer_conv env sigma ty conclty with
          | None -> error NotConvertible
          | Some sigma -> sigma
        end else sigma
      in
      let (sigma, x) = Evarutil.new_evar env sigma ty in
      let ans = if not cast then x else mkCast(x,k,conclty) in
      (sigma, ans, Some (fst @@ destEvar sigma x))
    end
  end

let convert_hyp ~check ~reorder d =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let ty = Proofview.Goal.concl gl in
    let sign = convert_hyp ~check ~reorder env sigma d in
    let env = reset_with_named_context sign env in
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma ty in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end
  end

let convert_gen pb x y =
  Proofview.Goal.enter begin fun gl ->
    match Tacmach.pf_apply (Reductionops.infer_conv ~pb) gl x y with
    | Some sigma -> Proofview.Unsafe.tclEVARS sigma
    | None -> error NotConvertible
    | exception e when CErrors.noncritical e ->
      let _, info = Exninfo.capture e in
      (* FIXME: Sometimes an anomaly is raised from conversion *)
      error ?loc:(Loc.get_loc info) NotConvertible
end

let convert x y = convert_gen Conversion.CONV x y
let convert_leq x y = convert_gen Conversion.CUMUL x y

(* This tactic enables users to remove hypotheses from the signature.
 * Some care is taken to prevent them from removing variables that are
 * subsequently used in other hypotheses or in the conclusion of the
 * goal. *)

let clear_gen fail = function
| [] -> Proofview.tclUNIT ()
| ids ->
  Proofview.Goal.enter begin fun gl ->
    let ids = List.fold_right Id.Set.add ids Id.Set.empty in
    (* clear_hyps_in_evi does not require nf terms *)
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let concl = Proofview.Goal.concl gl in
    let (sigma, hyps, concl) =
      try clear_hyps_in_evi env sigma (named_context_val env) concl ids
      with Evarutil.ClearDependencyError (id,err,inglobal) -> fail env sigma id err inglobal
    in
    let env = reset_with_named_context hyps env in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma concl in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end)
  end

let clear ids = clear_gen error_clear_dependency ids
let clear_for_replacing ids = clear_gen error_replacing_dependency ids

let apply_clear_request clear_flag dft c =
  let doclear = match clear_flag with
    | None -> if dft then c else None
    | Some true ->
      begin match c with
      | None -> error KeepAndClearModifierOnlyForHypotheses
      | Some id -> Some id
      end
    | Some false -> None
  in
  match doclear with
  | None -> Proofview.tclUNIT ()
  | Some id -> clear [id]

(* Moving hypotheses *)
let move_hyp id dest =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let ty = Proofview.Goal.concl gl in
    let sign = named_context_val env in
    let sign' = move_hyp_in_named_context env sigma id dest sign in
    let env = reset_with_named_context sign' env in
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma ty in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end
  end

(* Renaming hypotheses *)
let rename_hyp repl =
  let fold accu (src, dst) = match accu with
  | None -> None
  | Some (srcs, dsts) ->
    if Id.Set.mem src srcs then None
    else if Id.Set.mem dst dsts then None
    else
      let srcs = Id.Set.add src srcs in
      let dsts = Id.Set.add dst dsts in
      Some (srcs, dsts)
  in
  let init = Some (Id.Set.empty, Id.Set.empty) in
  let dom = List.fold_left fold init repl in
  match dom with
  | None ->
    let info = Exninfo.reify () in
    Tacticals.tclZEROMSG ~info (str "Not a one-to-one name mapping")
  | Some (src, dst) ->
    Proofview.Goal.enter begin fun gl ->
      let concl = Proofview.Goal.concl gl in
      let env = Proofview.Goal.env gl in
      let sign = named_context_val env in
      let sigma = Proofview.Goal.sigma gl in
      let relevance = Proofview.Goal.relevance gl in
      (* Check that we do not mess variables *)
      let vars = ids_of_named_context_val sign in
      let () =
        if not (Id.Set.subset src vars) then
          let hyp = Id.Set.choose (Id.Set.diff src vars) in
          raise (RefinerError (env, sigma, NoSuchHyp hyp))
      in
      let mods = Id.Set.diff vars src in
      let () =
        try
          let elt = Id.Set.choose (Id.Set.inter dst mods) in
          error (AlreadyUsed elt)
        with Not_found -> ()
      in
      (* All is well *)
      let make_subst (src, dst) = (src, mkVar dst) in
      let subst = List.map make_subst repl in
      let subst c = Vars.replace_vars sigma subst c in
      let replace id = try List.assoc_f Id.equal id repl with Not_found -> id in
      let map decl = decl |> NamedDecl.map_id replace |> NamedDecl.map_constr subst in
      let ohyps = named_context_of_val sign in
      let nhyps = List.map map ohyps in
      let nconcl = subst concl in
      let nctx = val_of_named_context nhyps in
      let fold odecl ndecl accu =
        if Id.equal (NamedDecl.get_id odecl) (NamedDecl.get_id ndecl) then
          SList.default accu
        else
          SList.cons (mkVar @@ NamedDecl.get_id odecl) accu
      in
      let instance = List.fold_right2 fold ohyps nhyps SList.empty in
      Refine.refine_with_principal ~typecheck:false begin fun sigma ->
        let sigma, ev = Evarutil.new_pure_evar nctx sigma ~relevance nconcl in
        sigma, mkEvar (ev, instance), Some ev
      end
    end

(**************************************************************)
(*          Fresh names                                       *)
(**************************************************************)

let fresh_id_in_env avoid id env =
  let avoid' = ids_of_named_context_val (named_context_val env) in
  let avoid = if Id.Set.is_empty avoid then avoid' else Id.Set.union avoid' avoid in
  next_ident_away_in_goal (Global.env ()) id avoid

let new_fresh_id avoid id gl =
  fresh_id_in_env avoid id (Proofview.Goal.env gl)

let id_of_name_with_default id = function
  | Anonymous -> id
  | Name id   -> id

let default_id_of_sort sigma s =
  if ESorts.is_small sigma s then default_small_ident else default_type_ident

let default_id env sigma decl =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (name,t) ->
      let dft = default_id_of_sort sigma (Retyping.get_sort_of env sigma t) in
      id_of_name_with_default dft name.binder_name
  | LocalDef (name,b,_) -> id_of_name_using_hdchar env sigma b name.binder_name

(* Non primitive introduction tactics are treated by intro_then_gen
   There is possibly renaming, with possibly names to avoid and
   possibly a move to do after the introduction *)

type name_flag =
  | NamingAvoid of Id.Set.t
  | NamingBasedOn of Id.t * Id.Set.t
  | NamingMustBe of lident

let naming_of_name = function
  | Anonymous -> NamingAvoid Id.Set.empty
  | Name id -> NamingMustBe (CAst.make id)

let find_name mayrepl decl naming gl = match naming with
  | NamingAvoid idl ->
      (* this case must be compatible with [find_intro_names] below. *)
      let env = Proofview.Goal.env gl in
      let sigma = Tacmach.project gl in
      new_fresh_id idl (default_id env sigma decl) gl
  | NamingBasedOn (id,idl) ->  new_fresh_id idl id gl
  | NamingMustBe {CAst.loc;v=id} ->
     (* When name is given, we allow to hide a global name *)
     let ids_of_hyps = Tacmach.pf_ids_set_of_hyps gl in
     if not mayrepl && Id.Set.mem id ids_of_hyps then
       error ?loc (AlreadyUsed id);
     id

(**************************************************************)
(*   Computing position of hypotheses for replacing           *)
(**************************************************************)

let get_next_hyp_position env sigma id =
  let rec aux = function
  | [] -> error_no_such_hypothesis env sigma id
  | decl :: right ->
    if Id.equal (NamedDecl.get_id decl) id then
      match right with decl::_ -> MoveBefore (NamedDecl.get_id decl) | [] -> MoveFirst
    else
      aux right
  in
  aux

let get_previous_hyp_position env sigma id =
  let rec aux dest = function
  | [] -> error_no_such_hypothesis env sigma id
  | decl :: right ->
      let hyp = NamedDecl.get_id decl in
      if Id.equal hyp id then dest else aux (MoveAfter hyp) right
  in
  aux MoveLast

(**************************************************************)
(*            Cut rule                                        *)
(**************************************************************)

let clear_hyps2 env sigma ids sign t cl =
  try
    Evarutil.clear_hyps2_in_evi env sigma sign t cl ids
  with Evarutil.ClearDependencyError (id,err,inglobal) ->
    error_replacing_dependency env sigma id err inglobal

let internal_cut ?(check=true) replace id t =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let concl = Proofview.Goal.concl gl in
    let sign = named_context_val env in
    let r = Retyping.relevance_of_type env sigma t in
    let env',t,concl,sigma =
      if replace then
        let nexthyp = get_next_hyp_position env sigma id (named_context_of_val sign) in
        let sigma,sign',t,concl = clear_hyps2 env sigma (Id.Set.singleton id) sign t concl in
        let sign' = insert_decl_in_named_context env sigma (LocalAssum (make_annot id r,t)) nexthyp sign' in
        Environ.reset_with_named_context sign' env,t,concl,sigma
      else
        (if check && mem_named_context_val id sign then
           error (IntroAlreadyDeclared id);
         push_named (LocalAssum (make_annot id r,t)) env,t,concl,sigma) in
    let nf_t = nf_betaiota env sigma t in
    Proofview.tclTHEN
      (Proofview.Unsafe.tclEVARS sigma)
      (Refine.refine_with_principal ~typecheck:false begin fun sigma ->
        let (sigma, ev) = Evarutil.new_evar env sigma nf_t in
        let (sigma, ev') = Evarutil.new_evar env' sigma concl in
        let term = mkLetIn (make_annot (Name id) r, ev, t, EConstr.Vars.subst_var sigma id ev') in
        (sigma, term, Some (fst @@ destEvar sigma ev'))
      end)
  end

let assert_before_then_gen b naming t tac =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let id = find_name b (LocalAssum (make_annot Anonymous Sorts.Relevant,t)) naming gl in
    Tacticals.tclTHENLAST
      (internal_cut b id t)
      (tac id)
  end

let assert_before_gen b naming t =
  assert_before_then_gen b naming t (fun _ -> Proofview.tclUNIT ())

let assert_before na = assert_before_gen false (naming_of_name na)
let assert_before_replacing id = assert_before_gen true (NamingMustBe (CAst.make id))

let replace_error_option err tac =
  match err with
    | None -> tac
    | Some (e, info) ->
      Proofview.tclORELSE tac (fun _ -> Proofview.tclZERO ~info e)

let assert_after_then_gen b naming t tac =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let id = find_name b (LocalAssum (make_annot Anonymous Sorts.Relevant,t)) naming gl in
    Tacticals.tclTHENFIRST
      (internal_cut b id t <*> Proofview.cycle 1)
      (tac id)
  end

let assert_after_gen b naming t =
  assert_after_then_gen b naming t (fun _ -> (Proofview.tclUNIT ()))

let assert_after na = assert_after_gen false (naming_of_name na)
let assert_after_replacing id = assert_after_gen true (NamingMustBe (CAst.make id))

(**************************************************************)
(*          Fixpoints and CoFixpoints                         *)
(**************************************************************)

let rec mk_holes env sigma = function
| [] -> (sigma, [])
| arg :: rem ->
  let (sigma, arg) = Evarutil.new_evar env sigma arg in
  let (sigma, rem) = mk_holes env sigma rem in
  (sigma, arg :: rem)

let rec check_mutind env sigma k cl = match EConstr.kind sigma (strip_outer_cast sigma cl) with
| Prod (na, c1, b) ->
  if Int.equal k 1 then
    try ignore (find_inductive env sigma c1)
    with Not_found -> error FixpointOnNonInductiveType
  else
    let open Context.Rel.Declaration in
    check_mutind (push_rel (LocalAssum (na, c1)) env) sigma (pred k) b
| LetIn (na, c1, t, b) ->
    let open Context.Rel.Declaration in
    check_mutind (push_rel (LocalDef (na, c1, t)) env) sigma k b
| _ -> error NotEnoughProducts

(* Refine as a fixpoint *)
let mutual_fix f n rest j = Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let concl = Proofview.Goal.concl gl in
  let () = check_mutind env sigma n concl in
  let firsts, lasts = List.chop j rest in
  let all = firsts @ (f, n, concl) :: lasts in
  let all = List.map (fun (f, n, ar) ->
      let r = Retyping.relevance_of_type env sigma ar in
      (f, r, n, ar))
      all
  in
  let rec mk_sign sign = function
  | [] -> sign
  | (f, r, n, ar) :: oth ->
    let open Context.Named.Declaration in
    let ()  = check_mutind env sigma n ar in
    if mem_named_context_val f sign then
      error (IntroAlreadyDeclared f);
    mk_sign (push_named_context_val (LocalAssum (make_annot f r, ar)) sign) oth
  in
  let nenv = reset_with_named_context (mk_sign (named_context_val env) all) env in
  Refine.refine ~typecheck:false begin fun sigma ->
    let (sigma, evs) = mk_holes nenv sigma (List.map (fun (_,_,_,ar) -> ar) all) in
    let ids, rs, _, ars = List.split4 all in
    let evs = List.map (Vars.subst_vars sigma (List.rev ids)) evs in
    let indxs = Array.of_list (List.map (fun n -> n-1) (List.map (fun (_,_,n,_) -> n) all)) in
    let funnames = Array.of_list (List.map2 (fun i r -> make_annot (Name i) r) ids rs) in
    let bodies = Array.of_list evs in
    let typarray = Array.of_list ars in
    let oterm = mkFix ((indxs,0),(funnames,typarray,bodies)) in
    (sigma, oterm)
  end
end

let fix id n = mutual_fix id n [] 0

let rec check_is_mutcoind env sigma cl =
  let b = whd_all env sigma cl in
  match EConstr.kind sigma b with
  | Prod (na, c1, b) ->
    let open Context.Rel.Declaration in
    check_is_mutcoind (push_rel (LocalAssum (na,c1)) env) sigma b
  | _ ->
    try
      let _ = find_coinductive env sigma b in ()
    with Not_found ->
      error AllMethodsInCoinductiveType

(* Refine as a cofixpoint *)
let mutual_cofix f others j = Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let concl = Proofview.Goal.concl gl in
  let firsts,lasts = List.chop j others in
  let all = firsts @ (f, concl) :: lasts in
  List.iter (fun (_, c) -> check_is_mutcoind env sigma c) all;
  let all = List.map (fun (id,t) -> (id, Retyping.relevance_of_type env sigma t, t)) all in
  let rec mk_sign sign = function
  | [] -> sign
  | (f, r, ar) :: oth ->
    let open Context.Named.Declaration in
    if mem_named_context_val f sign then
      error (AlreadyUsed f);
    mk_sign (push_named_context_val (LocalAssum (make_annot f r, ar)) sign) oth
  in
  let nenv = reset_with_named_context (mk_sign (named_context_val env) all) env in
  Refine.refine ~typecheck:false begin fun sigma ->
    let (ids, rs, types) = List.split3 all in
    let (sigma, evs) = mk_holes nenv sigma types in
    let evs = List.map (Vars.subst_vars sigma (List.rev ids)) evs in
    (* TODO relevance *)
    let funnames = Array.of_list (List.map2 (fun i r -> make_annot (Name i) r) ids rs) in
    let typarray = Array.of_list types in
    let bodies = Array.of_list evs in
    let oterm = mkCoFix (0, (funnames, typarray, bodies)) in
    (sigma, oterm)
  end
end

let cofix id = mutual_cofix id [] 0

(**************************************************************)
(*          Reduction and conversion tactics                  *)
(**************************************************************)

type tactic_reduction = Reductionops.reduction_function
type e_tactic_reduction = Reductionops.e_reduction_function

let[@ocaml.inline] (let*) m f = match m with
| NoChange -> NoChange
| Changed v -> f v

let e_pf_change_decl (redfun : bool -> Tacred.change_function) where env sigma decl =
  let open Context.Named.Declaration in
  match decl with
  | LocalAssum (id,ty) ->
    let () =
      if where == InHypValueOnly then error (VariableHasNoValue id.binder_name)
    in
    let* (sigma, ty') = redfun false env sigma ty in
    Changed (sigma, LocalAssum (id, ty'))
  | LocalDef (id,b,ty) ->
    let (sigma, b') =
      if where != InHypTypeOnly then match redfun true env sigma b with
      | NoChange -> (sigma, NoChange)
      | Changed (sigma, b') -> (sigma, Changed b')
      else (sigma, NoChange)
    in
    let (sigma, ty') =
      if where != InHypValueOnly then match redfun false env sigma ty with
      | NoChange -> (sigma, NoChange)
      | Changed (sigma, ty') -> (sigma, Changed ty')
      else (sigma, NoChange)
    in
    match b', ty' with
    | NoChange, NoChange -> NoChange
    | Changed b', NoChange -> Changed (sigma, LocalDef (id, b', ty))
    | NoChange, Changed ty' -> Changed (sigma, LocalDef (id, b, ty'))
    | Changed b', Changed ty' -> Changed (sigma, LocalDef (id, b', ty'))

let bind_change_occurrences occs = function
  | None -> None
  | Some c -> Some (Redexpr.out_with_occurrences (occs,c))

(* The following two tactics apply an arbitrary
   reduction function either to the conclusion or to a
   certain hypothesis *)

(** Tactic reduction modulo evars (for universes essentially) *)

let e_change_in_concl ~cast ~check (redfun, sty) =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    match redfun (Tacmach.pf_env gl) sigma (Tacmach.pf_concl gl) with
    | NoChange -> Proofview.tclUNIT ()
    | Changed (sigma, c') ->
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
      (convert_concl ~cast ~check c' sty)
  end

let e_change_in_hyp ~check ~reorder redfun (id,where) =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let hyp = Tacmach.pf_get_hyp id gl in
    match e_pf_change_decl redfun where (Proofview.Goal.env gl) sigma hyp with
    | NoChange -> Proofview.tclUNIT ()
    | Changed (sigma, c) ->
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
      (convert_hyp ~check ~reorder c)
  end

let e_change_option ~check ~reorder (redfun, sty) = function
| None ->
  e_change_in_concl ~cast:true ~check (redfun, sty)
| Some id ->
  let redfun _ env sigma c = redfun env sigma c in
  e_change_in_hyp ~check ~reorder redfun id

type hyp_conversion =
| AnyHypConv (** Arbitrary conversion *)
| StableHypConv (** Does not introduce new dependencies on variables *)
| LocalHypConv (** Same as above plus no dependence on the named environment *)

let e_change_in_hyps ~check ~reorder f args = match args with
| [] -> Proofview.tclUNIT ()
| _ :: _ ->
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let (env, sigma) = match reorder with
    | LocalHypConv ->
      (* If the reduction function is known not to depend on the named
          context, then we can perform it in parallel. *)
      let fold accu arg =
        let (id, redfun) = f arg in
        let old = try Id.Map.find id accu with Not_found -> [] in
        Id.Map.add id (redfun :: old) accu
      in
      let reds = List.fold_left fold Id.Map.empty args in
      let evdref = ref sigma in
      let map d =
        let id = NamedDecl.get_id d in
        match Id.Map.find id reds with
        | reds ->
          let d = EConstr.of_named_decl d in
          let fold redfun (sigma, d) = match redfun env sigma d with
          | NoChange -> sigma, d
          | Changed (sigma, d) -> sigma, d
          in
          let (sigma, d) = List.fold_right fold reds (sigma, d) in
          let () = evdref := sigma in
          EConstr.Unsafe.to_named_decl d
        | exception Not_found -> d
      in
      let sign = Environ.map_named_val map (Environ.named_context_val env) in
      let env = reset_with_named_context sign env in
      (env, !evdref)
    | StableHypConv | AnyHypConv ->
      let reorder = reorder == AnyHypConv in
      let fold (env, sigma) arg =
        let (id, redfun) = f arg in
        let hyp =
          try lookup_named id env
          with Not_found ->
            raise (RefinerError (env, sigma, NoSuchHyp id))
        in
        match redfun env sigma hyp with
        | NoChange -> (env, sigma)
        | Changed (sigma, d) ->
          let sign = Logic.convert_hyp ~check ~reorder env sigma d in
          let env = reset_with_named_context sign env in
          (env, sigma)
      in
      List.fold_left fold (env, sigma) args
    in
    let ty = Proofview.Goal.concl gl in
    Proofview.Unsafe.tclEVARS sigma
    <*>
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma ty in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end
  end

let e_reduct_in_concl ~cast ~check (redfun, sty) =
  let redfun env sigma c = Changed (redfun env sigma c) in
  e_change_in_concl ~cast ~check (redfun, sty)

let reduct_in_concl ~cast ~check (redfun, sty) =
  let redfun env sigma c = Changed (sigma, redfun env sigma c) in
  e_change_in_concl ~cast ~check (redfun, sty)

let e_reduct_in_hyp ~check ~reorder redfun (id, where) =
  let redfun _ env sigma c = Changed (redfun env sigma c) in
  e_change_in_hyp ~check ~reorder redfun (id, where)

let reduct_in_hyp ~check ~reorder redfun (id, where) =
  let redfun _ env sigma c = Changed (sigma, redfun env sigma c) in
  e_change_in_hyp ~check ~reorder redfun (id, where)

let e_reduct_option ~check redfun = function
  | Some id -> e_reduct_in_hyp ~check ~reorder:check (fst redfun) id
  | None    -> e_reduct_in_concl ~cast:true ~check redfun

let reduct_option ~check (redfun, sty) where =
  let redfun env sigma c = (sigma, redfun env sigma c) in
  e_reduct_option ~check (redfun, sty) where

type change_arg = Ltac_pretype.patvar_map -> env -> evar_map -> (evar_map * EConstr.constr) Tacred.change

let make_change_arg c pats env sigma =
  Changed (sigma, replace_vars sigma (Id.Map.bindings pats) c) (* TODO: fast-path *)

let is_partial_template_head env sigma c =
  let (hd, args) = decompose_app sigma c in
  match destRef sigma hd with
  | (ConstructRef (ind, _) | IndRef ind), _ ->
    let (mib, _) = Inductive.lookup_mind_specif env ind in
    begin match mib.mind_template with
    | None -> false
    | Some _ -> Array.length args < mib.mind_nparams
    end
  | (VarRef _ | ConstRef _), _ -> false
  | exception DestKO -> false

let check_types env sigma mayneedglobalcheck deep newc origc =
  let t1 = Retyping.get_type_of env sigma newc in
  if deep then begin
    let () =
      (* When changing a partially applied template term in a context, one must
         be careful to resynthetize the constraints as the implicit levels from
         the arguments are not written in the term. *)
      if is_partial_template_head env sigma newc ||
        is_partial_template_head env sigma origc then
        mayneedglobalcheck := true
    in
    let t2 = Retyping.get_type_of env sigma origc in
    let sigma, t2 = Evarsolve.refresh_universes
                      ~onlyalg:true (Some false) env sigma t2 in
    match infer_conv ~pb:Conversion.CUMUL env sigma t1 t2 with
    | None ->
      if
        isSort sigma (whd_all env sigma t1) &&
        isSort sigma (whd_all env sigma t2)
      then (mayneedglobalcheck := true; sigma)
      else
        error (ConvertIncompatibleTypes (env,sigma,t2,t1))
    | Some sigma -> sigma
  end
  else
    if not (isSort sigma (whd_all env sigma t1)) then
      error ConvertNotAType
    else sigma

(* Now we introduce different instances of the previous tacticals *)
let change_and_check cv_pb mayneedglobalcheck deep t env sigma c = match t env sigma with
| NoChange -> NoChange
| Changed (sigma, t') ->
  let sigma = check_types env sigma mayneedglobalcheck deep t' c in
  match infer_conv ~pb:cv_pb env sigma t' c with
  | None -> error NotConvertible
  | Some sigma -> Changed (sigma, t')

(* Use cumulativity only if changing the conclusion not a subterm *)
let change_on_subterm ~check cv_pb deep t where env sigma c =
  let mayneedglobalcheck = ref false in
  let ans = match where with
  | None ->
      if check then
        change_and_check cv_pb mayneedglobalcheck deep (t Id.Map.empty) env sigma c
      else
        t Id.Map.empty env sigma
  | Some occl ->
      e_contextually false occl
        (fun subst ->
          if check then
            change_and_check Conversion.CONV mayneedglobalcheck true (t subst)
          else
            fun env sigma _c -> t subst env sigma) env sigma c in
  match ans with
  | NoChange -> NoChange
  | Changed (sigma, c) ->
    let sigma = if !mayneedglobalcheck then
      begin
        try fst (Typing.type_of env sigma c)
        with e when noncritical e ->
          error (ReplacementIllTyped e)
      end else sigma
    in
    Changed (sigma, c)

let change_in_concl ~check occl t =
  (* No need to check in e_change_in_concl, the check is done in change_on_subterm *)
  e_change_in_concl ~cast:false ~check:false
    ((change_on_subterm ~check Conversion.CUMUL false t occl),DEFAULTcast)

let change_in_hyp ~check occl t id  =
  (* Same as above *)
  e_change_in_hyp ~check:false ~reorder:check (fun x -> change_on_subterm ~check Conversion.CONV x t occl) id

let concrete_clause_of enum_hyps cl = match cl.onhyps with
| None ->
  let f id = (id, AllOccurrences, InHyp) in
  List.map f (enum_hyps ())
| Some l ->
  List.map (fun ((occs, id), w) -> (id, occs, w)) l

let change ~check chg c cls =
  Proofview.Goal.enter begin fun gl ->
    let hyps = concrete_clause_of (fun () -> Tacmach.pf_ids_of_hyps gl) cls in
    begin match cls.concl_occs with
    | NoOccurrences -> Proofview.tclUNIT ()
    | occs -> change_in_concl ~check (bind_change_occurrences occs chg) c
    end
    <*>
    let f (id, occs, where) =
      let occl = bind_change_occurrences occs chg in
      let redfun deep env sigma t = change_on_subterm ~check Conversion.CONV deep c occl env sigma t in
      let redfun env sigma d = e_pf_change_decl redfun where env sigma d in
      (id, redfun)
    in
    let reorder = if check then AnyHypConv else StableHypConv in
    (* Don't check, we do it already in [change_on_subterm] *)
    e_change_in_hyps ~check:false ~reorder f hyps
  end

let change_concl t =
  change_in_concl ~check:true None (make_change_arg t)

let red_product_exn env sigma c = match red_product env sigma c with
| None -> user_err Pp.(str "No head constant to reduce.")
| Some c -> c

(* Pour usage interne (le niveau User est pris en compte par reduce) *)
let red_in_concl        = reduct_in_concl ~cast:true ~check:false (red_product_exn,DEFAULTcast)
let red_in_hyp          = reduct_in_hyp ~check:false ~reorder:false red_product_exn
let red_option          = reduct_option ~check:false (red_product_exn,DEFAULTcast)
let hnf_in_concl        = reduct_in_concl ~cast:true ~check:false (hnf_constr,DEFAULTcast)
let hnf_in_hyp          = reduct_in_hyp ~check:false ~reorder:false hnf_constr
let hnf_option          = reduct_option ~check:false (hnf_constr,DEFAULTcast)
let simpl_in_concl      = reduct_in_concl ~cast:true ~check:false (simpl,DEFAULTcast)
let simpl_in_hyp        = reduct_in_hyp ~check:false ~reorder:false simpl
let simpl_option        = reduct_option ~check:false (simpl,DEFAULTcast)
let normalise_in_concl  = reduct_in_concl ~cast:true ~check:false (compute,DEFAULTcast)
let normalise_in_hyp    = reduct_in_hyp ~check:false ~reorder:false compute
let normalise_option    = reduct_option ~check:false (compute,DEFAULTcast)
let normalise_vm_in_concl = reduct_in_concl ~cast:true ~check:false (Redexpr.cbv_vm,VMcast)
let unfold_in_concl loccname = reduct_in_concl ~cast:true ~check:false (unfoldn loccname,DEFAULTcast)
let unfold_in_hyp   loccname = reduct_in_hyp ~check:false ~reorder:false (unfoldn loccname)
let unfold_option   loccname = reduct_option ~check:false (unfoldn loccname,DEFAULTcast)
let pattern_option l = e_change_option ~check:false ~reorder:false (pattern_occs l,DEFAULTcast)

(* The main reduction function *)

let is_local_flag env flags =
  if flags.rDelta then false
  else
    let check = function
    | Evaluable.EvalVarRef _ -> false
    | Evaluable.EvalConstRef c -> Id.Set.is_empty (Environ.vars_of_global env (GlobRef.ConstRef c))
    | Evaluable.EvalProjectionRef c -> false (* FIXME *)
    in
    List.for_all check flags.rConst

let is_local_unfold env flags =
  let check (_, c) = match c with
  | Evaluable.EvalVarRef _ -> false
  | Evaluable.EvalConstRef c -> Id.Set.is_empty (Environ.vars_of_global env (GlobRef.ConstRef c))
  | Evaluable.EvalProjectionRef c -> false (* FIXME *)
  in
  List.for_all check flags

let change_of_red_expr_val ?occs redexp =
  let (redfun, kind) = Redexpr.reduction_of_red_expr_val ?occs redexp in
  let redfun env sigma c = Changed (redfun env sigma c) in (* TODO: fast-path *)
  (redfun, kind)

let reduce redexp cl =
  let trace env sigma =
    let open Printer in
    let pr = ((fun e -> pr_econstr_env e), (fun e -> pr_leconstr_env e), pr_evaluable_reference, pr_constr_pattern_env, int) in
    Pp.(hov 2 (Ppred.pr_red_expr_env env sigma pr str redexp))
  in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let hyps = concrete_clause_of (fun () -> Tacmach.pf_ids_of_hyps gl) cl in
  let nbcl = (if cl.concl_occs = NoOccurrences then 0 else 1) + List.length hyps in
  let check = match redexp with Fold _ | Pattern _ -> true | _ -> false in
  let reorder = match redexp with
  | Fold _ | Pattern _ -> AnyHypConv
  | Simpl (flags, _) | Cbv flags | Cbn flags | Lazy flags ->
    if is_local_flag env flags then LocalHypConv else StableHypConv
  | Unfold flags ->
    if is_local_unfold env flags then LocalHypConv else StableHypConv
  | Red | Hnf | CbvVm _ | CbvNative _ -> StableHypConv
  | ExtraRedExpr _ -> StableHypConv (* Should we be that lenient ?*)
  in
  let redexp = Redexpr.eval_red_expr env redexp in
  Proofview.Trace.name_tactic (fun () -> trace env sigma) begin
  begin match cl.concl_occs with
  | NoOccurrences -> Proofview.tclUNIT ()
  | occs ->
    let occs = Redexpr.out_occurrences occs in
    let redfun = change_of_red_expr_val ~occs:(occs, nbcl) redexp in
    e_change_in_concl ~cast:true ~check redfun
  end
  <*>
  let f (id, occs, where) =
    let occs = Redexpr.out_occurrences occs in
    let (redfun, _) = change_of_red_expr_val ~occs:(occs, nbcl) redexp in
    let redfun _ env sigma c = redfun env sigma c in
    let redfun env sigma d = e_pf_change_decl redfun where env sigma d in
    (id, redfun)
  in
  e_change_in_hyps ~check ~reorder f hyps
  end
  end

(* Unfolding occurrences of a constant *)

let unfold_constr = function
  | GlobRef.ConstRef sp -> unfold_in_concl [AllOccurrences,EvalConstRef sp]
  | GlobRef.VarRef id -> unfold_in_concl [AllOccurrences,EvalVarRef id]
  | _ -> error NotUnfoldable

(*******************************************)
(*         Introduction tactics            *)
(*******************************************)

(* Returns the names that would be created by intros, without doing
   intros.  This function is supposed to be compatible with an
   iteration of [find_name] above. As [default_id] checks the sort of
   the type to build hyp names, we maintain an environment to be able
   to type dependent hyps. *)
let find_intro_names env0 sigma ctxt =
  let _, res, _ = List.fold_right
    (fun decl acc ->
      let env,idl,avoid = acc in
      let name = fresh_id_in_env avoid (default_id env sigma decl) env0 in
      let newenv = push_rel decl env in
      (newenv, name :: idl, Id.Set.add name avoid))
    ctxt (env0, [], Id.Set.empty) in
  List.rev res

let build_intro_tac id dest tac = match dest with
  | MoveLast -> Tacticals.tclTHEN (introduction id) (tac id)
  | dest -> Tacticals.tclTHENLIST
    [introduction id; move_hyp id dest; tac id]

let rec intro_then_gen name_flag move_flag ~force ~dep tac =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Tacmach.pf_env gl in
    let concl = Proofview.Goal.concl gl in
    match EConstr.kind sigma concl with
    | Prod (name,t,u) when not dep || not (noccurn sigma 1 u) ->
        let name = find_name false (LocalAssum (name,t)) name_flag gl in
        build_intro_tac name move_flag tac
    | LetIn (name,b,t,u) when not dep || not (noccurn sigma 1 u) ->
        let name = find_name false (LocalDef (name,b,t)) name_flag gl in
        build_intro_tac name move_flag tac
    | Evar ev when force ->
        let name = find_name false (LocalAssum (anonR,concl)) name_flag gl in
        let sigma, t = Evardefine.define_evar_as_product env sigma ~name ev in
        Tacticals.tclTHEN
          (Proofview.Unsafe.tclEVARS sigma)
          (intro_then_gen name_flag move_flag ~force ~dep tac)
    | _ ->
        begin if not force
          then
            let info = Exninfo.reify () in
            Proofview.tclZERO ~info (RefinerError (env, sigma, IntroNeedsProduct))
            (* Note: red_in_concl includes betaiotazeta and this was like *)
            (* this since at least V6.3 (a pity *)
            (* that intro do betaiotazeta only when reduction is needed; and *)
            (* probably also a pity that intro does zeta *)
          else Proofview.tclUNIT ()
        end <*>
          Proofview.tclORELSE
          (Tacticals.tclTHEN hnf_in_concl
             (intro_then_gen name_flag move_flag ~force:false ~dep tac))
          begin function (e, info) -> match e with
            | RefinerError (env, sigma, IntroNeedsProduct) ->
              Tacticals.tclZEROMSG ~info (str "No product even after head-reduction.")
            | e -> Proofview.tclZERO ~info e
          end
  end

let drop_intro_name (_ : Id.t) = Proofview.tclUNIT ()

let intro_gen n m ~force ~dep = intro_then_gen n m ~force ~dep drop_intro_name
let intro_mustbe_force id = intro_gen (NamingMustBe (CAst.make id)) MoveLast ~force:true ~dep:false
let intro_using_then id = intro_then_gen (NamingBasedOn (id, Id.Set.empty)) MoveLast ~force:false ~dep:false
let intro_using id = intro_using_then id drop_intro_name

let intro_then = intro_then_gen (NamingAvoid Id.Set.empty) MoveLast ~force:false ~dep:false
let intro = intro_then drop_intro_name
let introf = intro_gen (NamingAvoid Id.Set.empty) MoveLast ~force:true ~dep:false
let intro_avoiding l = intro_gen (NamingAvoid l) MoveLast ~force:false ~dep:false

let intro_move_avoid idopt avoid hto = match idopt with
  | None -> intro_gen (NamingAvoid avoid) hto ~force:true ~dep:false
  | Some id -> intro_gen (NamingMustBe (CAst.make id)) hto ~force:true ~dep:false

let intro_move idopt hto = intro_move_avoid idopt Id.Set.empty hto

(**** Multiple introduction tactics ****)

let rec intros_using = function
  | []     -> Proofview.tclUNIT()
  | str::l -> Tacticals.tclTHEN (intro_using str) (intros_using l)

let rec intros_mustbe_force = function
  | []     -> Proofview.tclUNIT()
  | str::l -> Tacticals.tclTHEN (intro_mustbe_force str) (intros_mustbe_force l)

let rec intros_using_then_helper tac acc = function
  | []     -> tac (List.rev acc)
  | str::l -> intro_using_then str (fun str' -> intros_using_then_helper tac (str'::acc) l)
let intros_using_then l tac = intros_using_then_helper tac [] l

let is_overbound bound n = match bound with None -> false | Some p -> n >= p

let intro_forthcoming_last_then_gen avoid dep_flag bound n tac =
  let open RelDecl in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let relevance = Proofview.Goal.relevance gl in
    let avoid =
      let avoid' = ids_of_named_context_val (named_context_val env) in
      if Id.Set.is_empty avoid then avoid' else Id.Set.union avoid' avoid
    in
    let rec decompose env avoid n concl subst decls ndecls =
      let decl =
        if is_overbound bound n then None
        else match EConstr.kind sigma concl with
        | Prod (na, t, u) when not dep_flag || not (noccurn sigma 1 u) ->
          Some (LocalAssum (na, t), u)
        | LetIn (na, b, t, u) when not dep_flag || not (noccurn sigma 1 u) ->
          Some (LocalDef (na, b, t), u)
        | _ -> None
      in
      match decl with
      | None -> ndecls, decls, Vars.esubst Vars.lift_substituend subst concl
      | Some (decl, concl) ->
        let id = default_id env sigma decl in
        let id = next_ident_away_in_goal (Global.env ()) id avoid in
        let avoid = Id.Set.add id avoid in
        let env = EConstr.push_rel decl env in
        let ndecl = NamedDecl.of_rel_decl (fun _ -> id) decl in
        let ndecl = NamedDecl.map_constr (fun c -> Vars.esubst Vars.lift_substituend subst c) ndecl in
        let subst = Esubst.subs_cons (make_substituend @@ mkVar id) subst in
        decompose env avoid (n + 1) concl subst (decl :: decls) (ndecl :: ndecls)
    in
    let (ndecls, decls, nconcl) = decompose env avoid n concl (Esubst.subs_id 0) [] [] in
    let ids = List.map NamedDecl.get_id ndecls in
    if List.is_empty ids then tac []
    else Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let ctx = named_context_val env in
      let nctx = List.fold_right push_named_context_val ndecls ctx in
      let inst = SList.defaultn (List.length @@ Environ.named_context env) SList.empty in
      let rels = List.init (List.length decls) (fun i -> mkRel (i + 1)) in
      let ninst = List.fold_right (fun c accu -> SList.cons c accu) rels inst in
      let (sigma, ev) = new_pure_evar nctx sigma ~relevance nconcl in
      (sigma, it_mkLambda_or_LetIn (mkEvar (ev, ninst)) decls,
       Some ev)
    end <*> tac ids
  end

let intros =
  intro_forthcoming_last_then_gen Id.Set.empty false None 0 (fun _ -> tclIDTAC)

let intro_forthcoming_then_gen avoid move_flag ~dep bound n tac = match move_flag with
| MoveLast ->
  (* Fast path *)
  intro_forthcoming_last_then_gen avoid dep bound n tac
| MoveFirst | MoveAfter _ | MoveBefore _ ->
  let rec aux n ids =
    (* Note: we always use the bound when there is one for "*" and "**" *)
    if not (is_overbound bound n) then
    Proofview.tclORELSE
      begin
      intro_then_gen (NamingAvoid avoid) move_flag ~force:false ~dep
         (fun id -> aux (n+1) (id::ids))
      end
      begin function (e, info) -> match e with
      | RefinerError (env, sigma, IntroNeedsProduct) ->
          tac ids
      | e -> Proofview.tclZERO ~info e
      end
    else
      tac ids
  in
  aux n []

let intro_replacing id =
  Proofview.Goal.enter begin fun gl ->
  let env, sigma = Proofview.Goal.(env gl, sigma gl) in
  let hyps = Proofview.Goal.hyps gl in
  let next_hyp = get_next_hyp_position env sigma id hyps in
  Tacticals.tclTHENLIST [
    clear_for_replacing [id];
    introduction id;
    move_hyp id next_hyp;
  ]
  end

(* We have e.g. [x, y, y', x', y'' |- forall y y' y'', G] and want to
   reintroduce y, y,' y''. Note that we have to clear y, y' and y''
   before introducing y because y' or y'' can e.g. depend on old y. *)

(* This version assumes that replacement is actually possible *)
(* (ids given in the introduction order) *)
(* We keep a sub-optimality in cleaing for compatibility with *)
(* the behavior of inversion *)
let intros_possibly_replacing ids =
  let suboptimal = true in
  Proofview.Goal.enter begin fun gl ->
    let env, sigma = Proofview.Goal.(env gl, sigma gl) in
    let hyps = Proofview.Goal.hyps gl in
    let posl = List.map (fun id -> (id, get_next_hyp_position env sigma id hyps)) ids in
    Tacticals.tclTHEN
      (Tacticals.tclMAP (fun id ->
        Tacticals.tclTRY (clear_for_replacing [id]))
         (if suboptimal then ids else List.rev ids))
      (Tacticals.tclMAP (fun (id,pos) ->
        Tacticals.tclORELSE (intro_move (Some id) pos) (intro_using id))
         posl)
  end

(* This version assumes that replacement is actually possible *)
let intros_replacing ids =
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let env, sigma = Proofview.Goal.(env gl, sigma gl) in
    let posl = List.map (fun id -> (id, get_next_hyp_position env sigma id hyps)) ids in
    Tacticals.tclTHEN
      (clear_for_replacing ids)
      (Tacticals.tclMAP (fun (id,pos) -> intro_move (Some id) pos) posl)
  end

(* The standard for implementing Automatic Introduction *)
let auto_intros_tac ids =
  let fold used = function
    | Name id -> Id.Set.add id used
    | Anonymous -> used
  in
  let avoid = NamingAvoid (List.fold_left fold Id.Set.empty ids) in
  let naming = function
    | Name id -> NamingMustBe CAst.(make id)
    | Anonymous -> avoid
  in
  Tacticals.tclMAP (fun name -> intro_gen (naming name) MoveLast ~force:true ~dep:false) (List.rev ids)

(* User-level introduction tactics *)

let lookup_hypothesis_as_renamed env sigma ccl = function
  | AnonHyp n -> Detyping.lookup_index_as_renamed env sigma ccl n
  | NamedHyp id -> Detyping.lookup_name_as_displayed env sigma ccl id.CAst.v

let lookup_hypothesis_as_renamed_gen red h gl =
  let env = Proofview.Goal.env gl in
  let rec aux ccl =
    match lookup_hypothesis_as_renamed env (Tacmach.project gl) ccl h with
      | None when red ->
        begin match red_product env (Proofview.Goal.sigma gl) ccl with
        | None -> None
        | Some c -> aux c
        end
      | x -> x
  in
  aux (Proofview.Goal.concl gl)

let is_quantified_hypothesis id gl =
  match lookup_hypothesis_as_renamed_gen false (NamedHyp (CAst.make id)) gl with
    | Some _ -> true
    | None -> false

let warn_deprecated_intros_until_0 =
  CWarnings.create ~name:"deprecated-intros-until-0" ~category:CWarnings.CoreCategories.tactics
    (fun () ->
       strbrk"\"intros until 0\" is deprecated, use \"intros *\"; instead of \"induction 0\" and \"destruct 0\" use explicitly a name.\"")

let depth_of_quantified_hypothesis red h gl =
  if h = AnonHyp 0 then warn_deprecated_intros_until_0 ();
  match lookup_hypothesis_as_renamed_gen red h gl with
    | Some depth -> depth
    | None -> error (NoQuantifiedHypothesis(h,red))

let intros_until_gen red h =
  Proofview.Goal.enter begin fun gl ->
  let n = depth_of_quantified_hypothesis red h gl in
  Tacticals.tclDO n (if red then introf else intro)
  end

let intros_until_id id = intros_until_gen false (NamedHyp (CAst.make id))
let intros_until_n_gen red n = intros_until_gen red (AnonHyp n)

let intros_until = intros_until_gen true
let intros_until_n = intros_until_n_gen true

let tclCHECKVAR id =
  Proofview.Goal.enter begin fun gl ->
    let _ = Tacmach.pf_get_hyp id gl in
    Proofview.tclUNIT ()
  end

let try_intros_until_id_check id =
  Tacticals.tclORELSE (intros_until_id id) (tclCHECKVAR id)

let try_intros_until tac = function
  | NamedHyp {CAst.v=id} -> Tacticals.tclTHEN (try_intros_until_id_check id) (tac id)
  | AnonHyp n -> Tacticals.tclTHEN (intros_until_n n) (Tacticals.onLastHypId tac)

let rec intros_move = function
  | [] -> Proofview.tclUNIT ()
  | (hyp,destopt) :: rest ->
      Tacticals.tclTHEN (intro_gen (NamingMustBe (CAst.make hyp)) destopt ~force:false ~dep:false)
        (intros_move rest)

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

type evars_flag = bool     (* true = pose evars       false = fail on evars *)
type rec_flag = bool       (* true = recursive        false = not recursive *)
type advanced_flag = bool  (* true = advanced         false = basic *)
type clear_flag = bool option (* true = clear hyp, false = keep hyp, None = use default *)

type 'a core_destruction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of lident
  | ElimOnAnonHyp of int

type 'a destruction_arg =
  clear_flag * 'a core_destruction_arg

let onInductionArg tac = function
  | clear_flag,ElimOnConstr cbl ->
      tac clear_flag cbl
  | clear_flag,ElimOnAnonHyp n ->
      Tacticals.tclTHEN
        (intros_until_n n)
        (Tacticals.onLastHyp (fun c -> tac clear_flag (c,NoBindings)))
  | clear_flag,ElimOnIdent {CAst.v=id} ->
      (* A quantified hypothesis *)
      Tacticals.tclTHEN
        (try_intros_until_id_check id)
        (tac clear_flag (mkVar id,NoBindings))

let map_destruction_arg f sigma = function
  | clear_flag,ElimOnConstr g -> let sigma,x = f sigma g in (sigma, (clear_flag,ElimOnConstr x))
  | clear_flag,ElimOnAnonHyp n as x -> (sigma,x)
  | clear_flag,ElimOnIdent id as x -> (sigma,x)


let finish_evar_resolution ?(flags=Pretyping.all_and_fail_flags) env current_sigma (pending,c) =
  let sigma = Pretyping.solve_remaining_evars flags env current_sigma ?initial:pending in
  (sigma, nf_evar sigma c)

let finish_delayed_evar_resolution with_evars env sigma f =
  let (sigma', (c, lbind)) = f env sigma in
  let flags = tactic_infer_flags with_evars in
  let (sigma', c) = finish_evar_resolution ~flags env sigma' (Some sigma,c) in
  (sigma', (c, lbind))

let force_destruction_arg with_evars env sigma c =
  map_destruction_arg (finish_delayed_evar_resolution with_evars env) sigma c

(****************************************)
(* tactic "cut" (actually modus ponens) *)
(****************************************)

let cut c =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let concl = Proofview.Goal.concl gl in
    (* Backward compat: ensure that [c] is well-typed. Plus we need to
       know the relevance *)
    match Typing.sort_of env sigma c with
    | exception e when noncritical e ->
      let _, info = Exninfo.capture e in
      Tacticals.tclZEROMSG ~info (str "Not a proposition or a type.")
    | sigma, s ->
      let r = ESorts.relevance_of_sort s in
      let id = next_name_away_with_default "H" Anonymous (Tacmach.pf_ids_set_of_hyps gl) in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
        (Refine.refine_with_principal ~typecheck:false begin fun h ->
            let (h, f) = Evarutil.new_evar env h (mkArrow c r concl) in
            let ev = fst @@ destEvar h f in
            let (h, x) = Evarutil.new_evar env h c in
            let f = mkLetIn (make_annot (Name id) r, x, c, mkApp (f, [|mkRel 1|])) in
            (h, f, Some ev)
          end)
  end

let check_unresolved_evars_of_metas sigma clenv =
  (* This checks that Metas turned into Evars by *)
  (* Refiner.pose_all_metas_as_evars are resolved *)
  let metas = clenv_meta_list clenv in
  let iter mv () = match Unification.Meta.meta_opt_fvalue metas mv with
  | Some c ->
    begin match Constr.kind (EConstr.Unsafe.to_constr c.rebus) with
    | Evar (evk,_) when Evd.is_undefined (clenv_evd clenv) evk
                     && not (Evd.mem sigma evk) ->
      let na = Unification.Meta.meta_name metas mv in
      let id = match na with Name id -> id | _ -> anomaly (Pp.str "unnamed dependent meta.") in
      error (CannotFindInstance id)
    | _ -> ()
    end
  | None -> ()
  in
  Unification.Meta.fold iter metas ()

let do_replace id = function
  | NamingMustBe {CAst.v=id'} when Option.equal Id.equal id (Some id') -> true
  | _ -> false

(* For a clenv expressing some lemma [C[?1:T1,...,?n:Tn] : P] and some
   goal [G], [clenv_refine_in] returns [n+1] subgoals, the [n] last
   ones (resp [n] first ones if [sidecond_first] is [true]) being the
   [Ti] and the first one (resp last one) being [G] whose hypothesis
   [id] is replaced by P using the proof given by [tac] *)

let clenv_refine_in with_evars targetid replace env sigma0 clenv =
  let clenv = Clenv.clenv_pose_dependent_evars ~with_evars clenv in
  let evd = Typeclasses.resolve_typeclasses ~fail:(not with_evars) env (clenv_evd clenv) in
  let clenv = Clenv.update_clenv_evd clenv evd (Clenv.clenv_meta_list clenv) in
  let new_hyp_typ = clenv_type clenv in
  if not with_evars then check_unresolved_evars_of_metas sigma0 clenv;
  let [@ocaml.warning "-3"] exact_tac = Clenv.Internal.refiner clenv in
  let naming = NamingMustBe (CAst.make targetid) in
  Proofview.Unsafe.tclEVARS evd <*>
  Proofview.Goal.enter begin fun gl ->
    let id = find_name replace (LocalAssum (make_annot Anonymous Sorts.Relevant, new_hyp_typ)) naming gl in
    Tacticals.tclTHENLAST (internal_cut replace id new_hyp_typ <*> Proofview.cycle 1) exact_tac
  end


(********************************************)
(*       Elimination tactics                *)
(********************************************)

let nth_arg i c = match i with
| None -> List.last c
| Some i -> List.nth c i

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

let general_elim_clause0 with_evars flags (submetas, c, ty) elim =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let clause, bindings, index =  match elim with
  | ElimConstant cst ->
    let elimc = mkConstU cst in
    let elimt = Retyping.get_type_of env sigma elimc in
    let i = index_of_ind_arg sigma elimt in
    (elimc, elimt), NoBindings, Some i
  | ElimClause (elimc, lbindelimc) ->
    let elimt = Retyping.get_type_of env sigma elimc in
    (elimc, elimt), lbindelimc, None
  in
  let elimclause = make_clenv_binding env sigma clause bindings in
  let indmv =
    try nth_arg index (clenv_arguments elimclause)
    with Failure _ | Invalid_argument _ -> error IllFormedEliminationType
  in
  let elimclause = clenv_instantiate ~flags ~submetas indmv elimclause (c, ty) in
  Clenv.res_pf elimclause ~with_evars ~with_classes:true ~flags
  end

let general_elim_clause_in0 with_evars flags id (submetas, c, ty) elim =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let elimc = mkConstU elim in
  let elimt = Retyping.get_type_of env sigma elimc in
  let i = index_of_ind_arg sigma elimt in
  let elimclause = mk_clenv_from env sigma (elimc, elimt) in
  let indmv =
    try nth_arg (Some i) (clenv_arguments elimclause)
    with Failure _ | Invalid_argument _ -> error IllFormedEliminationType
  in
  (* Assumes that the metas of [c] are part of [sigma] already *)
  let hypmv =
    match List.remove Int.equal indmv (clenv_independent elimclause) with
    | [a] -> a
    | _ -> error IllFormedEliminationType
  in
  let elimclause = clenv_instantiate ~flags ~submetas indmv elimclause (c, ty) in
  let hyp = mkVar id in
  let hyp_typ = Retyping.get_type_of env sigma hyp in
  let elimclause =
    try clenv_instantiate ~flags hypmv elimclause (hyp, hyp_typ)
    with PretypeError (env,evd,NoOccurrenceFound (op,_)) ->
      (* Set the hypothesis name in the message *)
      raise (PretypeError (env,evd,NoOccurrenceFound (op,Some id)))
  in
  let new_hyp_typ  = clenv_type elimclause in
  if EConstr.eq_constr sigma hyp_typ new_hyp_typ then
    error (NothingToRewrite id);
  clenv_refine_in with_evars id true env sigma elimclause
  end

let general_elim with_evars clear_flag (c, lbindc) elim =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let ct = Retyping.get_type_of env sigma c in
  let id = try Some (destVar sigma c) with DestKO -> None in
  let t = try snd (reduce_to_quantified_ind env sigma ct) with UserError _ -> ct in
  let indclause = make_clenv_binding env sigma (c, t) lbindc in
  let flags = elim_flags () in
  let metas = clenv_meta_list indclause in
  let submetas = (clenv_arguments indclause, metas) in
  Proofview.Unsafe.tclEVARS (clenv_evd indclause) <*>
  Tacticals.tclTHEN
    (general_elim_clause0 with_evars flags (submetas, c, clenv_type indclause) elim)
    (apply_clear_request clear_flag (use_clear_hyp_by_default ()) id)
  end

let general_elim_clause with_evars flags where arg elim =
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  let (sigma, (elim, u)) = Evd.fresh_constant_instance env sigma elim in
  Proofview.Unsafe.tclEVARS sigma <*>
  match where with
  | None -> general_elim_clause0 with_evars flags arg (ElimConstant (elim, EInstance.make u))
  | Some id -> general_elim_clause_in0 with_evars flags id arg (elim, EInstance.make u)

(* Case analysis tactics *)

let general_case_analysis_in_context with_evars clear_flag (c,lbindc) =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let state = Proofview.Goal.state gl in
  let ct = Retyping.get_type_of env sigma c in
  let (mind, _), t = reduce_to_quantified_ind env sigma ct in
  let dep =
    if dependent sigma c concl then true
    else default_case_analysis_dependence env mind
  in
  let id = try Some (destVar sigma c) with DestKO -> None in
  let indclause = make_clenv_binding env sigma (c, t) lbindc in
  let indclause = Clenv.clenv_pose_dependent_evars ~with_evars:true indclause in
  let argtype = clenv_type indclause in (* Guaranteed to be meta-free *)
  let tac =
    Proofview.tclEVARMAP >>= fun sigma ->
    let sigma = Evd.push_future_goals sigma in
    let (sigma, ev) = Evarutil.new_evar env sigma argtype in
    let _, sigma = Evd.pop_future_goals sigma in
    let evk, _ = destEvar sigma ev in
    let indclause = Clenv.update_clenv_evd indclause sigma (Clenv.clenv_meta_list indclause) in
    Proofview.Unsafe.tclEVARS sigma <*>
    Proofview.Unsafe.tclNEWGOALS ~before:true [Proofview.goal_with_state evk state] <*>
    Proofview.tclDISPATCH [Clenv.res_pf ~with_evars:true indclause; tclIDTAC] <*>
    Proofview.tclEXTEND [] tclIDTAC [Clenv.case_pf ~with_evars ~dep (ev, argtype)]
  in
  let sigma = clenv_evd indclause in
  Tacticals.tclTHENLIST [
    Tacticals.tclWITHHOLES with_evars tac sigma;
    apply_clear_request clear_flag (use_clear_hyp_by_default ()) id;
  ]
  end

let general_case_analysis with_evars clear_flag (c,lbindc as cx) =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma c with
    | Var id when lbindc == NoBindings ->
        Tacticals.tclTHEN (try_intros_until_id_check id)
          (general_case_analysis_in_context with_evars clear_flag cx)
    | _ ->
        general_case_analysis_in_context with_evars clear_flag cx

let simplest_case c = general_case_analysis false None (c,NoBindings)
let simplest_ecase c = general_case_analysis true None (c,NoBindings)

(* Elimination tactic with bindings but using the default elimination
 * constant associated with the type. *)

exception IsNonrec

let is_nonrec env mind = (Environ.lookup_mind (fst mind) env).mind_finite == Declarations.BiFinite

let find_ind_eliminator env sigma ind s =
  let c = lookup_eliminator env ind s in
  let sigma, c = EConstr.fresh_global env sigma c in
  sigma, destConst sigma c

let default_elim with_evars clear_flag (c,_ as cx) =
  Proofview.tclORELSE
    (Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let sigma, t = Typing.type_of env sigma c in
      let (ind,u) = eval_to_quantified_ind env sigma t in
      if is_nonrec env ind then raise IsNonrec;
      let sigma, elim = find_ind_eliminator env sigma ind (Retyping.get_sort_family_of env sigma concl) in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
      (general_elim with_evars clear_flag cx (ElimConstant elim))
    end)
    begin function (e, info) -> match e with
      | IsNonrec ->
          (* For records, induction principles aren't there by default
             anymore.  Instead, we do a case analysis. *)
          general_case_analysis with_evars clear_flag cx
      | e -> Proofview.tclZERO ~info e
    end

let elim_in_context with_evars clear_flag c = function
  | Some elim ->
      general_elim with_evars clear_flag c (ElimClause elim)
  | None -> default_elim with_evars clear_flag c

let elim with_evars clear_flag (c,lbindc as cx) elim =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma c with
    | Var id when lbindc == NoBindings ->
        Tacticals.tclTHEN (try_intros_until_id_check id)
          (elim_in_context with_evars clear_flag cx elim)
    | _ ->
        elim_in_context with_evars clear_flag cx elim

(* The simplest elimination tactic, with no substitutions at all. *)

let simplest_elim c = default_elim false None (c,NoBindings)

(* Elimination in hypothesis *)
(* Typically, elimclause := (eq_ind ?x ?P ?H ?y ?Heq : ?P ?y)
              indclause : forall ..., hyps -> a=b    (to take place of ?Heq)
              id : phi(a)                            (to take place of ?H)
      and the result is to overwrite id with the proof of phi(b)

   but this generalizes to any elimination scheme with one constructor
   (e.g. it could replace id:A->B->C by id:C, knowing A/\B)
*)

(* Apply a tactic below the products of the conclusion of a lemma *)

type conjunction_status =
  | DefinedRecord of Constant.t option list
  | NotADefinedRecordUseScheme

let make_projection env sigma params cstr sign elim i n c (ind, u) =
  let open Context.Rel.Declaration in
  let elim = match elim with
  | NotADefinedRecordUseScheme ->
      (* bugs: goes from right to left when i increases! *)
      let cs_args = cstr.cs_args in
      let decl = List.nth cs_args i in
      let t = RelDecl.get_type decl in
      let b = match decl with LocalAssum _ -> mkRel (i+1) | LocalDef (_,b,_) -> b in
      if
        (* excludes dependent projection types *)
        noccur_between sigma 1 (n-i-1) t
        (* to avoid surprising unifications, excludes flexible
        projection types or lambda which will be instantiated by Meta/Evar *)
        && not (isEvar sigma (fst (whd_betaiota_stack env sigma t)))
        && (not (isRel sigma t))
      then
        let (_, mip) as specif = Inductive.lookup_mind_specif env ind in
        let t = lift (i + 1 - n) t in
        let ksort = Retyping.get_sort_family_of (push_rel_context sign env) sigma t in
        if Sorts.family_leq ksort (Inductiveops.elim_sort specif) then
          let arity = List.firstn mip.mind_nrealdecls mip.mind_arity_ctxt in
          let mknas ctx = Array.of_list (List.rev_map get_annot ctx) in
          let ci = Inductiveops.make_case_info env ind RegularStyle in
          let br = [| mknas cs_args, b |] in
          let args = Context.Rel.instance mkRel 0 sign in
          let indr = ERelevance.make @@
            Inductive.relevance_of_ind_body mip (EConstr.Unsafe.to_instance u)
          in
          let pnas = Array.append (mknas (EConstr.of_rel_context arity)) [|make_annot Anonymous indr|] in
          let p = (pnas, lift (Array.length pnas) t) in
          let c = mkCase (ci, u, Array.of_list params, (p, get_relevance decl), NoInvert, mkApp (c, args), br) in
          Some (sigma, it_mkLambda_or_LetIn c sign, it_mkProd_or_LetIn t sign)
        else None
      else
        None
  | DefinedRecord l ->
      (* goes from left to right when i increases! *)
      match List.nth l i with
      | Some proj ->
          let args = Context.Rel.instance mkRel 0 sign in
          let sigma, proj =
            match Structures.PrimitiveProjections.find_opt_with_relevance (proj,u) with
            | Some (proj,r) ->
              sigma, mkProj (Projection.make proj false, r, mkApp (c, args))
            | None ->
              let env = EConstr.push_rel_context sign env in
              let args = Array.append (Array.of_list params) [|mkApp (c, args)|] in
              Typing.checked_appvect env sigma (mkConstU (proj, u)) args
          in
          let app = it_mkLambda_or_LetIn proj sign in
          let t = Retyping.get_type_of env sigma app in
            Some (sigma, app, t)
      | None -> None
  in elim

let descend_in_conjunctions avoid tac (err, info) c =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  try
    let t = Retyping.get_type_of env sigma c in
    let ((ind,u),t) = reduce_to_quantified_ind env sigma t in
    let sign,ccl = EConstr.decompose_prod_decls sigma t in
    match match_with_tuple env sigma ccl with
    | Some (_,_,isrec) ->
        (* At this point, ind is known to be an index-free one-constructor
           inductive type, potentially recursive. *)
        let n = (constructors_nrealargs env ind).(0) in
        let IndType (indf,_) = find_rectype env sigma ccl in
        let (_,inst), params = dest_ind_family indf in
        let cstr = (get_constructors env indf).(0) in
        let elim =
          try DefinedRecord (Structures.Structure.find_projections ind)
          with Not_found -> NotADefinedRecordUseScheme
        in
        let or_tac t1 t2 e = Proofview.tclORELSE (t1 e) t2 in
        List.fold_right or_tac
          (List.init n (fun i (err, info) ->
            Proofview.Goal.enter begin fun gl ->
            let env = Proofview.Goal.env gl in
            let sigma = Tacmach.project gl in
            match make_projection env sigma params cstr sign elim i n c (ind, u) with
            | None ->
              Proofview.tclZERO ~info err
            | Some (sigma, p, pt) ->
              Proofview.Unsafe.tclEVARS sigma <*>
              Tacticals.tclTHENS
                (Proofview.tclORELSE
                  (assert_before_gen false (NamingAvoid avoid) pt)
                  (fun _ -> Proofview.tclZERO ~info err))
                [Proofview.tclORELSE
                  (Refine.refine ~typecheck:false (fun h -> (h, p)))
                   (fun _ -> Proofview.tclZERO ~info err);
                 (* Might be ill-typed due to forbidden elimination. *)
                 Tacticals.onLastHypId (tac (err, info) (not isrec))]
           end))
          (fun (err, info) -> Proofview.tclZERO ~info err)
          (err, info)
    | None -> Proofview.tclZERO ~info err
  with RefinerError _|UserError _ -> Proofview.tclZERO ~info err
  end

(****************************************************)
(*            Resolution tactics                    *)
(****************************************************)

let general_apply ?(with_classes=true) ?(respect_opaque=false) with_delta with_destruct with_evars
    clear_flag {CAst.loc;v=(c,lbind : EConstr.constr with_bindings)} =
  Proofview.Goal.enter begin fun gl ->
  let concl = Proofview.Goal.concl gl in
  let sigma = Tacmach.project gl in
  let id = try Some (destVar sigma c) with DestKO -> None in
  (* The actual type of the theorem. It will be matched against the
  goal. If this fails, then the head constant will be unfolded step by
  step. *)
  let concl_nprod = nb_prod_modulo_zeta sigma concl in
  let rec try_main_apply with_destruct c =
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let ts =
      if respect_opaque then Conv_oracle.get_transp_state (oracle env)
      else TransparentState.full
    in
    let flags =
      if with_delta then default_unify_flags () else default_no_delta_unify_flags ts in
    let thm_ty = nf_betaiota env sigma (Retyping.get_type_of env sigma c) in
    let sigma, thm_ty = Evarsolve.refresh_universes ~onlyalg:true None env sigma thm_ty in
    let try_apply thm_ty nprod =
      try
        let n = nb_prod_modulo_zeta sigma thm_ty - nprod in
        if n<0 then error NotEnoughPremises;
        let clause = make_clenv_binding_apply env sigma (Some n) (c,thm_ty) lbind in
        Clenv.res_pf clause ~with_classes ~with_evars ~flags
      with exn when noncritical exn ->
        let exn, info = Exninfo.capture exn in
        Proofview.tclZERO ~info exn
    in
    let rec try_red_apply thm_ty (exn0, info) = match red_product env sigma thm_ty with
    | Some red_thm ->
        (* Try to head-reduce the conclusion of the theorem *)
        Proofview.tclORELSE
          (try_apply red_thm concl_nprod)
          (fun _ -> try_red_apply red_thm (exn0, info))
    | None ->
        (* Last chance: if the head is a variable, apply may try
            second order unification *)
        let info = Option.cata (fun loc -> Loc.add_loc info loc) info loc in
        let tac =
          if with_destruct then
            Proofview.tclORELSE
              (descend_in_conjunctions Id.Set.empty
                (fun _ b id ->
                  Tacticals.tclTHEN
                    (try_main_apply b (mkVar id))
                    (clear [id]))
                (exn0, info) c)
              (fun _ -> Proofview.tclZERO ~info exn0)
          else
            Proofview.tclZERO ~info exn0 in
        if not (Int.equal concl_nprod 0) then
          Tacticals.tclORELSE0 (try_apply thm_ty 0) tac
        else
          tac
    in
    Proofview.tclORELSE
      (try_apply thm_ty concl_nprod)
      (try_red_apply thm_ty)
    end
  in
    Tacticals.tclTHEN
      (try_main_apply with_destruct c)
      (apply_clear_request clear_flag (use_clear_hyp_by_default ()) id)
  end

let rec apply_with_bindings_gen ?with_classes b e = function
  | [] -> Proofview.tclUNIT ()
  | [k,cb] -> general_apply ?with_classes b b e k cb
  | (k,cb)::cbl ->
      Tacticals.tclTHENLAST
        (general_apply ?with_classes b b e k cb)
        (apply_with_bindings_gen ?with_classes b e cbl)

let apply_with_delayed_bindings_gen b e l =
  let one k {CAst.loc;v=cb} =
    Proofview.Goal.enter begin fun _ ->
      Tacticals.tclRUNWITHHOLES e cb
        (fun cb -> general_apply ~respect_opaque:(not b) b b e k CAst.(make ?loc cb))
    end
  in
  let rec aux = function
    | [] -> Proofview.tclUNIT ()
    | [k,f] -> one k f
    | (k,f)::cbl ->
      Tacticals.tclTHENLAST
        (one k f) (aux cbl)
  in aux l

let apply_with_bindings cb = apply_with_bindings_gen false false [None,(CAst.make cb)]

let eapply_with_bindings ?with_classes cb = apply_with_bindings_gen ?with_classes false true [None,(CAst.make cb)]

let apply c = apply_with_bindings_gen false false [None,(CAst.make (c,NoBindings))]

let eapply ?with_classes c =
  apply_with_bindings_gen ?with_classes false true [None,(CAst.make (c,NoBindings))]

let apply_list = function
  | c::l -> apply_with_bindings (c,ImplicitBindings l)
  | _ -> assert false

(* [apply_in hyp c] replaces

   hyp : forall y1, ti -> t             hyp : rho(u)
   ========================    with     ============  and the =======
   goal                                 goal                  rho(ti)

   assuming that [c] has type [forall x1..xn -> t' -> u] for some [t]
   unifiable with [t'] with unifier [rho]
*)

exception UnableToApply

let progress_with_clause env flags (id, t) clause mvs =
  let innerclause = mk_clenv_from_n env (clenv_evd clause) 0 (mkVar id, t) in
  if List.is_empty mvs then raise UnableToApply;
  let f mv =
    let rec find innerclause =
      let metas = clenv_meta_list innerclause in
      let submetas = (clenv_arguments innerclause, metas) in
      try
        Some (clenv_instantiate mv ~flags ~submetas clause (mkVar id, clenv_type innerclause))
      with e when noncritical e ->
      match clenv_push_prod innerclause with
      | Some (_, _, innerclause) -> find innerclause
      | None -> None
    in
    find innerclause
  in
  match List.find_map f mvs with
  | Some v -> v
  | None -> raise UnableToApply

let apply_in_once_main flags (id, t) env sigma (loc,d,lbind) =
  let thm = nf_betaiota env sigma (Retyping.get_type_of env sigma d) in
  let rec aux clause mvs =
    try progress_with_clause env flags (id, t) clause mvs
    with e when CErrors.noncritical e ->
    let e' = Exninfo.capture e in
    match clenv_push_prod clause with
    | Some (mv, dep, clause) -> aux clause (if dep then [] else [mv])
    | None ->
      match e with
      | UnableToApply -> error ?loc (UnableToApplyLemma (env,sigma,thm,t))
      | _ -> Exninfo.iraise e'
  in
  let clenv = make_clenv_binding env sigma (d,thm) lbind in
  let mvs = List.rev (clenv_independent clenv) in
  aux clenv mvs

let apply_in_once ?(respect_opaque = false) with_delta
    with_destruct with_evars naming id (clear_flag,{ CAst.loc; v= d,lbind}) tac =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
  let t' = Tacmach.pf_get_hyp_typ id gl in
  let targetid = find_name true (LocalAssum (make_annot Anonymous Sorts.Relevant,t')) naming gl in
  let replace = Id.equal id targetid in
  let rec aux ?err idstoclear with_destruct c =
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let idc = try Some (destVar (Tacmach.project gl) c) with DestKO -> None in
    let ts =
      if respect_opaque then Conv_oracle.get_transp_state (oracle env)
      else TransparentState.full
    in
    let flags =
      if with_delta then default_unify_flags () else default_no_delta_unify_flags ts in
    try
      let clause = apply_in_once_main flags (id, t') env sigma (loc,c,lbind) in
      let cleartac = apply_clear_request clear_flag false idc <*> clear idstoclear in
      let refine = Tacticals.tclTHENFIRST (clenv_refine_in with_evars targetid replace env sigma clause) cleartac in
      Tacticals.tclTHENFIRST (replace_error_option err refine) (tac targetid)
    with e when with_destruct && CErrors.noncritical e ->
      let err = Option.default (Exninfo.capture e) err in
        (descend_in_conjunctions (Id.Set.singleton targetid)
           (fun err b id -> aux ~err (id::idstoclear) b (mkVar id))
           err c)
    end
  in
  aux [] with_destruct d
  end

let apply_in_delayed_once ?(respect_opaque = false) with_delta
    with_destruct with_evars naming id (clear_flag,{CAst.loc;v=f}) tac =
  Proofview.Goal.enter begin fun _ ->
    Tacticals.tclRUNWITHHOLES with_evars f
      (fun c -> apply_in_once ~respect_opaque with_delta with_destruct with_evars
          naming id (clear_flag,CAst.(make ?loc c)) tac)
  end

(* A useful resolution tactic which, if c:A->B, transforms |- C into
   |- B -> C and |- A

   -------------------
   Gamma |- c : A -> B      Gamma |- ?2 : A
   ----------------------------------------
           Gamma |- B                        Gamma |- ?1 : B -> C
           -----------------------------------------------------
                             Gamma |- ? : C

 Ltac lapply c :=
  let ty := check c in
  match eval hnf in ty with
    ?A -> ?B => cut B; [ idtac | apply c ]
  end.
*)

let cut_and_apply c =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let sigma, t = Typing.type_of env sigma c in
    match EConstr.kind sigma (hnf_constr env sigma t) with
    | Prod (_,c1,c2) when Vars.noccurn sigma 1 c2 ->
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
        (Refine.refine ~typecheck:false begin fun sigma ->
            let typ = mkProd (make_annot Anonymous ERelevance.relevant, c2, concl) in
            let (sigma, f) = Evarutil.new_evar env sigma typ in
            let (sigma, x) = Evarutil.new_evar env sigma c1 in
            (sigma, mkApp (f, [|mkApp (c, [|x|])|]))
          end)
    | _ -> error NeedDependentProduct
  end

(********************************************************************)
(*               Exact tactics                                      *)
(********************************************************************)

let exact_no_check c =
  Refine.refine ~typecheck:false (fun h -> (h,c))

let exact_check c =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  (* We do not need to normalize the goal because we just check convertibility *)
  let concl = Proofview.Goal.concl gl in
  let env = Proofview.Goal.env gl in
  let sigma, ct = Typing.type_of env sigma c in
  Tacticals.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
  (Tacticals.tclTHEN (convert_leq ct concl) (exact_no_check c))
  end

let cast_no_check cast c =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    exact_no_check (mkCast (c, cast, concl))
  end

let vm_cast_no_check c = cast_no_check VMcast c
let native_cast_no_check c = cast_no_check NATIVEcast c

let exact_proof c =
  let open Tacmach in
  Proofview.Goal.enter begin fun gl ->
  Refine.refine ~typecheck:false begin fun sigma ->
    let (c, ctx) = Constrintern.interp_casted_constr (pf_env gl) sigma c (pf_concl gl) in
    let sigma = Evd.set_universe_context sigma ctx in
    (sigma, c)
  end
  end

let assumption =
  let rec arec gl only_eq = function
  | [] ->
    if only_eq then
      let hyps = Proofview.Goal.hyps gl in
      arec gl false hyps
    else
      let info = Exninfo.reify () in
      Tacticals.tclZEROMSG ~info (str "No such assumption.")
  | decl::rest ->
    let t = NamedDecl.get_type decl in
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.project gl in
    let ans =
      if only_eq then
        if EConstr.eq_constr sigma t concl then Some sigma
        else None
      else
        let env = Proofview.Goal.env gl in
        infer_conv env sigma t concl
    in
    match ans with
    | Some sigma ->
      (Proofview.Unsafe.tclEVARS sigma) <*>
        exact_no_check (mkVar (NamedDecl.get_id decl))
    | None -> arec gl only_eq rest
  in
  let assumption_tac gl =
    let hyps = Proofview.Goal.hyps gl in
    arec gl true hyps
  in
  Proofview.Goal.enter assumption_tac

(*****************************************************************)
(*          Modification of a local context                      *)
(*****************************************************************)

let check_is_type env sigma idl ids ty =
  try
    let sigma, _ = Typing.sort_of env sigma ty in
    sigma
  with e when CErrors.noncritical e ->
    raise (DependsOnBody (idl, ids, None))

let check_decl env sigma idl ids decl =
  let open Context.Named.Declaration in
  let ty = NamedDecl.get_type decl in
  try
    let sigma, _ = Typing.sort_of env sigma ty in
    let sigma = match decl with
    | LocalAssum _ -> sigma
    | LocalDef (_,c,_) -> Typing.check env sigma c ty
    in
    sigma
  with e when CErrors.noncritical e ->
    let id = NamedDecl.get_id decl in
    raise (DependsOnBody (idl, ids, Some id))

let clear_body idl =
  let open Context.Named.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.project gl in
    let ctx = named_context env in
    let ids = Id.Set.of_list idl in
    (* We assume the context to respect dependencies *)
    let rec fold ids ctx =
      if Id.Set.is_empty ids then
        let base_env = reset_context env in
        let env = push_named_context ctx base_env in
        env, sigma, Id.Set.empty
      else
        match ctx with
        | [] -> assert false
        | decl :: ctx ->
          let decl, ids, found =
            match decl with
            | LocalAssum (id,t) ->
              let () =
                if Id.Set.mem id.binder_name ids then
                  error (VariableHasNoValue id.binder_name)
              in
              decl, ids, false
            | LocalDef (id,_,t) as decl ->
               if Id.Set.mem id.binder_name ids
               then LocalAssum (id, t), Id.Set.remove id.binder_name ids, true
               else decl, ids, false
          in
          let env, sigma, ids = fold ids ctx in
          if Id.Set.exists (fun id -> occur_var_in_decl env sigma id decl) ids then
            let sigma = check_decl env sigma idl ids decl in (* can sigma really change? *)
            let ids = Id.Set.add (get_id decl) ids in
            push_named decl env, sigma, Id.Set.add (get_id decl) ids
          else
            push_named decl env, sigma, if found then Id.Set.add (get_id decl) ids else ids
    in
    try
      let env, sigma, ids = fold ids ctx in
      let sigma =
        if Id.Set.exists (fun id -> occur_var env sigma id concl) ids then
          check_is_type env sigma idl ids concl
        else sigma
      in
      Proofview.Unsafe.tclEVARS sigma <*>
    Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let sigma, ev = Evarutil.new_evar env sigma concl in
      sigma, ev, Some (fst @@ destEvar sigma ev)
    end
    with DependsOnBody _ as exn ->
      let _, info = Exninfo.capture exn in
      Proofview.tclZERO ~info exn
    end

let clear_wildcards ids =
  let clear_wildcards_msg ?loc env sigma _id err inglobal =
    user_err ?loc (clear_dependency_msg env sigma None err inglobal) in
  Tacticals.tclMAP (fun {CAst.loc;v=id} -> clear_gen (clear_wildcards_msg ?loc) [id]) ids

(*   Takes a list of booleans, and introduces all the variables
 *  quantified in the goal which are associated with a value
 *  true  in the boolean list. *)

let rec intros_clearing = function
  | []          -> Proofview.tclUNIT ()
  | (false::tl) -> Tacticals.tclTHEN intro (intros_clearing tl)
  | (true::tl)  ->
      Tacticals.tclTHENLIST
        [ intro; Tacticals.onLastHypId (fun id -> clear [id]); intros_clearing tl]

(* Keeping only a few hypotheses *)

let keep hyps =
  Proofview.Goal.enter begin fun gl ->
  Proofview.tclENV >>= fun env ->
  let ccl = Proofview.Goal.concl gl in
  let sigma = Tacmach.project gl in
  let cl,_ =
    fold_named_context_reverse (fun (clear,keep) decl ->
      let decl = EConstr.of_named_decl decl in
      let hyp = NamedDecl.get_id decl in
      if Id.List.mem hyp hyps
        || List.exists (occur_var_in_decl env sigma hyp) keep
        || occur_var env sigma hyp ccl
      then (clear,decl::keep)
      else (hyp::clear,keep))
      ~init:([],[]) (Proofview.Goal.env gl)
  in
  clear cl
  end

(*********************************)
(*  Basic generalization tactics *)
(*********************************)

(* Given a type [T] convertible to [forall x1..xn:A1..An(x1..xn-1), G(x1..xn)]
   and [a1..an:A1..An(a1..an-1)] such that the goal is [G(a1..an)],
   this generalizes [hyps |- goal] into [hyps |- T] *)

let apply_type ~typecheck newcl args =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    Refine.refine_with_principal ~typecheck begin fun sigma ->
      let newcl = nf_betaiota env sigma newcl (* As in former Logic.refine *) in
      let (sigma, ev) = Evarutil.new_evar env sigma newcl in
      (sigma, applist (ev, args), Some (fst @@ destEvar sigma ev))
    end
  end

(************************)
(* Introduction tactics *)
(************************)

let check_number_of_constructors expctdnumopt i nconstr =
  if Int.equal i 0 then error ConstructorNumberedFromOne;
  begin match expctdnumopt with
    | Some n when not (Int.equal n nconstr) ->
        error (NotRightNumberConstructors n)
    | _ -> ()
  end;
  if i > nconstr then error NotEnoughConstructors

let constructor_core with_evars cstr lbind =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let (sigma, (cons, u)) = Evd.fresh_constructor_instance env sigma cstr in
    let cons = mkConstructU (cons, EInstance.make u) in
    let apply_tac = general_apply true false with_evars None (CAst.make (cons,lbind)) in
    Tacticals.tclTHEN (Proofview.Unsafe.tclEVARS sigma) apply_tac
  end

let constructor_tac with_evars expctdnumopt i lbind =
  Proofview.Goal.enter begin fun gl ->
    let cl = Tacmach.pf_concl gl in
    let env = Proofview.Goal.env gl in
    let ((ind,_),redcl) = Tacmach.pf_apply Tacred.reduce_to_quantified_ind gl cl in
    let nconstr = Array.length (snd (Inductive.lookup_mind_specif env ind)).mind_consnames in
    check_number_of_constructors expctdnumopt i nconstr;
    Tacticals.tclTHENLIST [
      convert_concl ~cast:false ~check:false redcl DEFAULTcast;
      intros;
      constructor_core with_evars (ind, i) lbind
    ]
  end

let one_constructor i lbind = constructor_tac false None i lbind

(* Try to apply the constructor of the inductive definition followed by
   a tactic t given as an argument.
   Should be generalize in Constructor (Fun c : I -> tactic)
 *)

let any_constructor with_evars tacopt =
  let one_constr =
    let tac cstr = constructor_core with_evars cstr NoBindings in
    match tacopt with
    | None -> tac
    | Some t -> fun cstr -> Tacticals.tclTHEN (tac cstr) t in
  let rec any_constr ind n i () =
    if Int.equal i n then one_constr (ind,i)
    else Tacticals.tclORD (one_constr (ind,i)) (any_constr ind n (i + 1)) in
  Proofview.Goal.enter begin fun gl ->
    let cl = Tacmach.pf_concl gl in
    let env = Proofview.Goal.env gl in
    let (ind,_),redcl = Tacmach.pf_apply Tacred.reduce_to_quantified_ind gl cl in
    let nconstr =
      Array.length (snd (Inductive.lookup_mind_specif env ind)).mind_consnames in
    if Int.equal nconstr 0 then error NoConstructors;
    Tacticals.tclTHENLIST [
      convert_concl ~cast:false ~check:false redcl DEFAULTcast;
      intros;
      any_constr ind nconstr 1 ()
    ]
 end

let left_with_bindings  with_evars = constructor_tac with_evars (Some 2) 1
let right_with_bindings with_evars = constructor_tac with_evars (Some 2) 2
let split_with_bindings with_evars l =
  Tacticals.tclMAP (constructor_tac with_evars (Some 1) 1) l
let split_with_delayed_bindings with_evars bl =
  Tacticals.tclMAPDELAYEDWITHHOLES with_evars bl
    (constructor_tac with_evars (Some 1) 1)

let left           = left_with_bindings false
let simplest_left  = left NoBindings

let right          = right_with_bindings false
let simplest_right = right NoBindings

let split          = constructor_tac false (Some 1) 1
let simplest_split = split NoBindings

(*****************************)
(* Decomposing introductions *)
(*****************************)

(* Rewriting function for rewriting one hypothesis at the time *)
let (forward_general_rewrite_clause, general_rewrite_clause) = Hook.make ()

(* Rewriting function for substitution (x=t) everywhere at the same time *)
let (forward_subst_one, subst_one) = Hook.make ()

let intro_decomp_eq_function = ref (fun _ -> failwith "Not implemented")

let declare_intro_decomp_eq f = intro_decomp_eq_function := f

let my_find_eq_data_decompose env sigma t =
  try Some (find_eq_data_decompose env sigma t)
  with e when is_anomaly e
    (* Hack in case equality is not yet defined... one day, maybe,
       known equalities will be dynamically registered *)
      -> None
  | Constr_matching.PatternMatchingFailure -> None

let intro_decomp_eq ?loc l thin tac id =
  Proofview.Goal.enter begin fun gl ->
  let c = mkVar id in
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let {uj_type=t} = Typing.judge_of_variable env id in
  let _,t = reduce_to_atomic_ind env sigma t in
  match my_find_eq_data_decompose env sigma t with
  | Some (eq,u,eq_args) ->
    !intro_decomp_eq_function
      (fun n -> tac ((CAst.make id)::thin) (Some n) l)
      (eq,t,eq_args) (c, t)
  | None ->
    let info = Exninfo.reify () in
    Tacticals.tclZEROMSG ~info (str "Not a primitive equality here.")
  end

let intro_or_and_pattern ?loc with_evars ll thin tac id =
  Proofview.Goal.enter begin fun gl ->
  let c = mkVar id in
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let {uj_type=t} = Typing.judge_of_variable env id in
  let ind = eval_to_quantified_ind env sigma t in
  let branchsigns = compute_constructor_signatures env ~rec_flag:false ind in
  let nv_with_let = Array.map List.length branchsigns in
  let ll = fix_empty_or_and_pattern (Array.length branchsigns) ll in
  let ll = get_and_check_or_and_pattern ?loc ll branchsigns in
  let case = if with_evars then simplest_ecase else simplest_case in
  Tacticals.tclTHENLASTn
    (Tacticals.tclTHEN (case c) (clear [id]))
    (Array.map2 (fun n l -> tac thin (Some n) l)
       nv_with_let ll)
  end

let rewrite_hyp_then with_evars thin l2r id tac =
  let rew_on l2r =
    Hook.get forward_general_rewrite_clause l2r with_evars (mkVar id,NoBindings) in
  let subst_on l2r x rhs =
    Hook.get forward_subst_one true x (id,rhs,l2r) in
  let clear_var_and_eq id' = clear [id';id] in
  let early_clear id' thin =
    List.filter (fun {CAst.v=id} -> not (Id.equal id id')) thin in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let {uj_type=t} = Typing.judge_of_variable env id in
    let t = whd_all env sigma t in
    let eqtac, thin = match match_with_equality_type env sigma t with
    | Some (hdcncl,[_;lhs;rhs]) ->
        if l2r && isVar sigma lhs && not (occur_var env sigma (destVar sigma lhs) rhs) then
          let id' = destVar sigma lhs in
          subst_on l2r id' rhs, early_clear id' thin
        else if not l2r && isVar sigma rhs && not (occur_var env sigma (destVar sigma rhs) lhs) then
          let id' = destVar sigma rhs in
          subst_on l2r id' lhs, early_clear id' thin
        else
          Tacticals.tclTHEN (rew_on l2r onConcl) (clear [id]),
          thin
    | Some (hdcncl,[c]) ->
        let l2r = not l2r in (* equality of the form eq_true *)
        if isVar sigma c then
          let id' = destVar sigma c in
          Tacticals.tclTHEN (rew_on l2r allHypsAndConcl)
            (clear_var_and_eq id'),
          early_clear id' thin
        else
          Tacticals.tclTHEN (rew_on l2r onConcl) (clear [id]),
          thin
    | _ ->
        Tacticals.tclTHEN (rew_on l2r onConcl) (clear [id]),
        thin in
    (* Skip the side conditions of the rewriting step *)
    Tacticals.tclTHENFIRST eqtac (tac thin)
  end

let rec collect_intro_names = let open CAst in function
| {v=IntroForthcoming _} :: l -> collect_intro_names l
| {v=IntroNaming (IntroIdentifier id)} :: l ->
  let ids1, ids2 = collect_intro_names l in Id.Set.add id ids1, ids2
| {v=IntroAction (IntroOrAndPattern l)} :: l' ->
    let ll = match l with IntroAndPattern l -> [l] | IntroOrPattern ll -> ll in
    let fold (ids1',ids2') l =
      let ids1, ids2 = collect_intro_names (l@l') in
      Id.Set.union ids1 ids1', Id.Set.union ids2 ids2' in
    List.fold_left fold (Id.Set.empty,Id.Set.empty) ll
| {v=IntroAction (IntroInjection l)} :: l' ->
    collect_intro_names (l@l')
| {v=IntroAction (IntroApplyOn (c,pat))} :: l' ->
    collect_intro_names (pat::l')
| {v=IntroNaming (IntroFresh id)} :: l ->
    let ids1, ids2 = collect_intro_names l in ids1, Id.Set.add id ids2
| {v=(IntroNaming IntroAnonymous
     | IntroAction (IntroWildcard | IntroRewrite _))} :: l ->
     collect_intro_names l
| [] -> Id.Set.empty, Id.Set.empty

let explicit_intro_names l = fst (collect_intro_names l)

let explicit_all_intro_names l =
  let ids1,ids2 = collect_intro_names l in Id.Set.union ids1 ids2

let rec check_name_unicity env ok seen = let open CAst in function
| {v=IntroForthcoming _} :: l -> check_name_unicity env ok seen l
| {loc;v=IntroNaming (IntroIdentifier id)} :: l ->
   (try
      ignore (if List.mem_f Id.equal id ok then raise Not_found else lookup_named id env);
      error ?loc (AlreadyUsed id)
   with Not_found ->
     if List.mem_f Id.equal id seen then
       error ?loc (UsedTwice id)
     else
       check_name_unicity env ok (id::seen) l)
| {v=IntroAction (IntroOrAndPattern l)} :: l' ->
    let ll = match l with IntroAndPattern l -> [l] | IntroOrPattern ll -> ll in
    List.iter (fun l -> check_name_unicity env ok seen (l@l')) ll
| {v=IntroAction (IntroInjection l)} :: l' ->
    check_name_unicity env ok seen (l@l')
| {v=IntroAction (IntroApplyOn (c,pat))} :: l' ->
    check_name_unicity env ok seen (pat::l')
| {v=(IntroNaming (IntroAnonymous | IntroFresh _)
     | IntroAction (IntroWildcard | IntroRewrite _))} :: l ->
     check_name_unicity env ok seen l
| [] -> ()

let make_naming ?loc avoid l = function
  | IntroIdentifier id -> NamingMustBe (CAst.make ?loc id)
  | IntroAnonymous -> NamingAvoid (Id.Set.union avoid (explicit_intro_names l))
  | IntroFresh id -> NamingBasedOn (id, Id.Set.union avoid (explicit_intro_names l))

let rec make_naming_action avoid l = function
  (* In theory, we could use a tmp id like "wild_id" for all actions
     but we prefer to avoid it to avoid this kind of "ugly" names *)
  | IntroWildcard ->
    NamingBasedOn (Id.of_string "_H", Id.Set.union avoid (explicit_all_intro_names l))
  | IntroApplyOn (_,{CAst.v=pat;loc}) -> make_naming_pattern avoid ?loc l pat
  | (IntroOrAndPattern _ | IntroInjection _ | IntroRewrite _) as pat ->
    NamingAvoid(Id.Set.union avoid (explicit_intro_names ((CAst.make @@ IntroAction pat)::l)))

and make_naming_pattern ?loc avoid l = function
  | IntroNaming pat -> make_naming ?loc avoid l pat
  | IntroAction pat -> make_naming_action avoid l pat
  | IntroForthcoming _ -> NamingAvoid (Id.Set.union avoid (explicit_intro_names l))

let prepare_naming ?loc pat = make_naming ?loc Id.Set.empty [] pat

let fit_bound n = function
  | None -> true
  | Some n' -> n = n'

let exceed_bound n = function
  | None -> false
  | Some n' -> n >= n'

  (* We delay thinning until the completion of the whole intros tactic
     to ensure that dependent hypotheses are cleared in the right
     dependency order (see BZ#1000); we use fresh names, not used in
     the tactic, for the hyps to clear *)
  (* In [intro_patterns_core b avoid ids thin destopt bound n tac patl]:
     [b]: compatibility flag, if false at toplevel, do not complete incomplete
          trailing toplevel or_and patterns (as in "intros []", see
          [bracketing_last_or_and_intro_pattern])
     [avoid]: names to avoid when creating an internal name
     [ids]: collect introduced names for possible use by the [tac] continuation
     [thin]: collect names to erase at the end
     [destopt]: position in the context where to introduce the hypotheses
     [bound]: number of pending intros to do in the current or-and pattern,
              with remembering of [b] flag if at toplevel
     [n]: number of introduction done in the current or-and pattern
     [tac]: continuation tactic
     [patl]: introduction patterns to interpret
  *)

let rec intro_patterns_core with_evars avoid ids thin destopt bound n tac =
  function
  | [] when fit_bound n bound ->
      tac ids thin
  | [] ->
      (* Behave as IntroAnonymous *)
      intro_patterns_core with_evars avoid ids thin destopt bound n tac
        [CAst.make @@ IntroNaming IntroAnonymous]
  | {CAst.loc;v=pat} :: l ->
  if exceed_bound n bound then error ?loc (UnexpectedExtraPattern(bound,pat)) else
  match pat with
  | IntroForthcoming onlydeps ->
      let naming = Id.Set.union avoid (explicit_intro_names l) in
      intro_forthcoming_then_gen naming destopt ~dep:onlydeps bound n
        (fun ids -> intro_patterns_core with_evars avoid ids thin destopt bound
          (n+List.length ids) tac l)
  | IntroAction pat ->
      let naming = make_naming_action avoid l pat in
      intro_then_gen naming destopt ~force:true ~dep:false
        (intro_pattern_action ?loc with_evars pat thin destopt
          (fun thin bound' -> intro_patterns_core with_evars avoid ids thin destopt bound' 0
            (fun ids thin ->
              intro_patterns_core with_evars avoid ids thin destopt bound (n+1) tac l)))
  | IntroNaming pat ->
      let naming = make_naming avoid l pat in
      intro_then_gen naming destopt ~force:true ~dep:false
        (fun id -> intro_patterns_core with_evars avoid (id::ids) thin destopt bound (n+1) tac l)

and intro_pattern_action ?loc with_evars pat thin destopt tac id =
  match pat with
  | IntroWildcard ->
      tac (CAst.(make ?loc id)::thin) None []
  | IntroOrAndPattern ll ->
      intro_or_and_pattern ?loc with_evars ll thin tac id
  | IntroInjection l' ->
      intro_decomp_eq ?loc l' thin tac id
  | IntroRewrite l2r ->
      rewrite_hyp_then with_evars thin l2r id (fun thin -> tac thin None [])
  | IntroApplyOn ({CAst.loc=loc';v=f},{CAst.loc;v=pat}) ->
      let naming = NamingMustBe (CAst.make ?loc id) in
      let tac_ipat = prepare_action ?loc with_evars destopt pat in
      let f =
        tactic_of_delayed f >>= fun c ->
        Proofview.tclUNIT (c, NoBindings)
      in
      apply_in_delayed_once true true with_evars naming id (None,CAst.make ?loc:loc' f)
        (fun id -> Tacticals.tclTHENLIST [tac_ipat id; tac thin None []])

and prepare_action ?loc with_evars destopt = function
  | IntroNaming ipat ->
      (fun _ -> Proofview.tclUNIT ())
  | IntroAction ipat ->
      (let tac thin bound =
        intro_patterns_core with_evars Id.Set.empty [] thin destopt bound 0
          (fun _ l -> clear_wildcards l) in
      fun id ->
        intro_pattern_action ?loc with_evars ipat [] destopt tac id)
  | IntroForthcoming _ -> error ?loc OneIntroPatternExpected

let intro_patterns_head_core with_evars destopt bound pat =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    check_name_unicity env [] [] pat;
    intro_patterns_core with_evars Id.Set.empty [] [] destopt
      bound 0 (fun _ l -> clear_wildcards l) pat
  end

let intro_patterns_bound_to with_evars n destopt =
  intro_patterns_head_core with_evars destopt (Some n)

let intro_patterns_to with_evars destopt =
  intro_patterns_head_core with_evars destopt None

let intro_pattern_to with_evars destopt pat =
  intro_patterns_to with_evars destopt [CAst.make pat]

let intro_patterns with_evars = intro_patterns_to with_evars MoveLast

(* Implements "intros" *)
let intros_patterns with_evars = function
  | [] -> intros
  | l -> intro_patterns_to with_evars MoveLast l

(**************************)
(*   Forward reasoning    *)
(**************************)

let prepare_intros_opt with_evars dft destopt ipat =
  let naming, loc, ipat = match ipat with
  | None ->
    let pat = IntroNaming dft in make_naming_pattern Id.Set.empty [] pat, None, pat
  | Some {CAst.loc;v=(IntroNaming pat as ipat)} ->
    (* "apply ... in H as id" needs to use id and H is kept iff id<>H *)
    prepare_naming ?loc pat, loc, ipat
  | Some {CAst.loc;v=(IntroAction pat as ipat)} ->
    (* "apply ... in H as pat" reuses H so that old H is always cleared *)
    (match dft with IntroIdentifier _ -> prepare_naming ?loc dft | _ -> make_naming_action Id.Set.empty [] pat),
    loc, ipat
  | Some {CAst.loc;v=(IntroForthcoming _)} -> assert false in
  naming, prepare_action ?loc with_evars destopt ipat

let ipat_of_name = function
  | Anonymous -> None
  | Name id -> Some (CAst.make @@ IntroNaming (IntroIdentifier id))

let head_ident sigma c =
   let c = fst (decompose_app sigma (snd (decompose_lambda_decls sigma c))) in
   if isVar sigma c then Some (destVar sigma c) else None

(* apply in as *)

let general_apply_in ?(respect_opaque=false) with_delta
    with_destruct with_evars id lemmas ipat then_tac =
  let tac (naming,lemma) tac id =
    apply_in_delayed_once ~respect_opaque with_delta
      with_destruct with_evars naming id lemma tac in
  Proofview.Goal.enter begin fun gl ->
  let destopt =
    if with_evars then MoveLast (* evars would depend on the whole context *)
    else (
      let env, sigma = Proofview.Goal.(env gl, sigma gl) in
      get_previous_hyp_position env sigma id (Proofview.Goal.hyps gl)
    ) in
  let naming,ipat_tac =
    prepare_intros_opt with_evars (IntroIdentifier id) destopt ipat in
  let lemmas_target, last_lemma_target =
    let last,first = List.sep_last lemmas in
    List.map (fun lem -> (NamingMustBe (CAst.make id),lem)) first, (naming,last)
  in
  (* We chain apply_in_once, ending with an intro pattern *)
  List.fold_right tac lemmas_target
    (tac last_lemma_target (fun id -> Tacticals.tclTHEN (ipat_tac id) then_tac)) id
  end

(*
  if sidecond_first then
    (* Skip the side conditions of the applied lemma *)
    Tacticals.tclTHENLAST (tclMAPLAST tac lemmas_target) (ipat_tac id)
  else
    Tacticals.tclTHENFIRST (tclMAPFIRST tac lemmas_target) (ipat_tac id)
*)

let apply_in simple with_evars id lemmas ipat =
  let lemmas = List.map (fun (k,{CAst.loc;v=l}) -> k, CAst.make ?loc (Proofview.tclUNIT l)) lemmas in
  general_apply_in simple simple with_evars id lemmas ipat Tacticals.tclIDTAC

let apply_delayed_in simple with_evars id lemmas ipat then_tac =
  general_apply_in ~respect_opaque:true simple simple with_evars id lemmas ipat then_tac

(*****************************)
(* Tactics abstracting terms *)
(*****************************)

(* Implementation without generalisation: abbrev will be lost in hyps in *)
(* in the extracted proof *)

let decode_hyp = function
  | None -> MoveLast
  | Some id -> MoveAfter id

(* [letin_tac b (... abstract over c ...) gl] transforms
   [...x1:T1(c),...,x2:T2(c),... |- G(c)] into
   [...x:T;Heqx:(x=c);x1:T1(x),...,x2:T2(x),... |- G(x)] if [b] is false or
   [...x:=c:T;x1:T1(x),...,x2:T2(x),... |- G(x)] if [b] is true
*)

let letin_tac_gen with_eq (id,depdecls,lastlhyp,ccl,c) ty =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let (sigma, t) = match ty with
    | Some t -> (sigma, t)
    | None ->
      let t = typ_of env sigma c in
      Evarsolve.refresh_universes ~onlyalg:true (Some false) env sigma t
    in
    let rel = Retyping.relevance_of_term env sigma c in
    let (sigma, (newcl, eq_tac)) = match with_eq with
      | Some (lr,{CAst.loc;v=ido}) ->
          let heq = match ido with
            | IntroAnonymous -> new_fresh_id (Id.Set.singleton id) (add_prefix "Heq" id) gl
            | IntroFresh heq_base -> new_fresh_id (Id.Set.singleton id) heq_base gl
            | IntroIdentifier id -> id in
          let eqdata = build_rocq_eq_data () in
          let args = if lr then [mkVar id;c] else [c;mkVar id]in
          let (sigma, eq) = Evd.fresh_global env sigma eqdata.eq in
          let refl = mkRef (eqdata.refl, snd @@ destRef sigma eq) in
          let sigma, eq = Typing.checked_applist env sigma eq [t] in
          let eq = applist (eq, args) in
          let refl = applist (refl, [t; mkVar id]) in
          let r = Retyping.relevance_of_term env sigma refl in
          let term = mkNamedLetIn sigma (make_annot id rel) c t
              (mkLetIn (make_annot (Name heq) r, refl, eq, ccl)) in
          let ans = term,
            Tacticals.tclTHENLIST
              [
               intro_gen (NamingMustBe CAst.(make ?loc heq)) (decode_hyp lastlhyp) ~force:true ~dep:false;
              clear_body [heq;id]]
          in
          (sigma, ans)
      | None ->
          (sigma, (mkNamedLetIn sigma (make_annot id rel) c t ccl, Proofview.tclUNIT ()))
    in
      Tacticals.tclTHENLIST
      [ Proofview.Unsafe.tclEVARS sigma;
        convert_concl ~cast:false ~check:false newcl DEFAULTcast;
        intro_gen (NamingMustBe (CAst.make id)) (decode_hyp lastlhyp) ~force:true ~dep:false;
        Tacticals.tclMAP (convert_hyp ~check:false ~reorder:false) depdecls;
        eq_tac ]
  end

let pose_tac na c =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let hyps = named_context_val env in
    let concl = Proofview.Goal.concl gl in
    let relevance = Proofview.Goal.relevance gl in
    let t = typ_of env sigma c in
    let rel = Retyping.relevance_of_term env sigma c in
    let (sigma, t) = Evarsolve.refresh_universes ~onlyalg:true (Some false) env sigma t in
    let id = match na with
    | Name id ->
      let () = if mem_named_context_val id hyps then
        error (IntroAlreadyDeclared id)
      in
      id
    | Anonymous ->
      let id = id_of_name_using_hdchar env sigma t Anonymous in
      next_ident_away_in_goal (Global.env ()) id (ids_of_named_context_val hyps)
    in
    Proofview.Unsafe.tclEVARS sigma <*>
    Refine.refine ~typecheck:false begin fun sigma ->
      let id = make_annot id rel in
      let nhyps = EConstr.push_named_context_val (NamedDecl.LocalDef (id, c, t)) hyps in
      let (sigma, ev) = Evarutil.new_pure_evar nhyps sigma ~relevance concl in
      let inst = EConstr.identity_subst_val hyps in
      let body = mkEvar (ev, SList.cons (mkRel 1) inst) in
      (sigma, mkLetIn (map_annot Name.mk_name id, c, t, body))
    end
  end

let letin_tac with_eq id c ty occs =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let ccl = Proofview.Goal.concl gl in
    let abs = AbstractExact (id,c,ty,occs,true) in
    let (id,_,depdecls,lastlhyp,ccl,res) = make_abstraction env sigma ccl abs in
    (* We keep the original term to match but record the potential side-effects
       of unifying universes. *)
    let (sigma, c) = match res with
      | None -> (sigma, c)
      | Some (sigma, _) -> (sigma, c)
    in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (letin_tac_gen with_eq (id,depdecls,lastlhyp,ccl,c) ty)
  end

let letin_pat_tac with_evars with_eq id c occs =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let ccl = Proofview.Goal.concl gl in
    let check t = true in
    let abs = AbstractPattern (false,check,id,c,occs) in
    let (id,_,depdecls,lastlhyp,ccl,res) = make_abstraction env sigma ccl abs in
    let (sigma, c) = match res with
    | None -> finish_evar_resolution ~flags:(tactic_infer_flags with_evars) env sigma c
    | Some res -> res in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (letin_tac_gen with_eq (id,depdecls,lastlhyp,ccl,c) None)
  end

(* Tactics "pose proof" (usetac=None) and "assert"/"enough" (otherwise) *)
let forward b usetac ipat c =
  match usetac with
  | None ->
      Proofview.Goal.enter begin fun gl ->
      let t = Tacmach.pf_get_type_of gl c in
      let sigma = Tacmach.project gl in
      let hd = head_ident sigma c in
      let assert_as =
        let naming,tac = prepare_intros_opt false IntroAnonymous MoveLast ipat in
        let repl = do_replace hd naming in
        if repl then assert_before_gen true naming t
        else assert_before_then_gen false naming t tac
      in
      Tacticals.tclTHENFIRST assert_as (exact_no_check c)
      end
  | Some tac ->
      let tac = match tac with
        | None -> Tacticals.tclIDTAC
        | Some tac -> Tacticals.tclCOMPLETE tac in
      let naming, assert_tac = prepare_intros_opt false IntroAnonymous MoveLast ipat in
      if b then
        Tacticals.tclTHENFIRST (assert_before_then_gen false naming c assert_tac) tac
      else
        Tacticals.tclTHENS3PARTS
          (assert_after_then_gen false naming c assert_tac) [||] tac [|Tacticals.tclIDTAC|]

let pose_proof na c = forward true None (ipat_of_name na) c
let assert_by na t tac = forward true (Some (Some tac)) (ipat_of_name na) t
let enough_by na t tac = forward false (Some (Some tac)) (ipat_of_name na) t

(* Instantiating some arguments (whatever their position) of an hypothesis
   or any term, leaving other arguments quantified. If operating on an
   hypothesis of the goal, the new hypothesis replaces it.

   (c,lbind) are supposed to be of the form
   ((H t1 t2 ... tm) , someBindings)
   whete t1..tn are user given args, to which someBinding must be combined.

   The goal is to pose a proof with body

   (fun y1...yp => H t1 t2 ... tm u1 ... uq)

   where yi are the remaining arguments of H that lbind could not
   solve, ui are a mix of inferred args and yi. The overall effect
   is to remove from H as much quantification as possible given
   lbind. *)

module Specialize :
sig
  val unify_bindings : evar_map -> (evar_map -> int -> 'a -> evar_map) ->
    types -> 'a bindings -> evar_map
  (* Unfortunate small code duplication with EClause *)
end =
struct

type hole = {
  hole_evar : int;
  hole_deps  : bool;
  hole_name : Name.t;
}

let make_evar_clause sigma t =
  let open EConstr in
  let open Vars in
  let rec clrec holes n t = match EConstr.kind sigma t with
  | Cast (t, _, _) -> clrec holes n t
  | Prod (na, t1, t2) ->
    let dep = not (noccurn sigma 1 t2) in
    let hole = { hole_evar = n; hole_deps = dep; hole_name = na.binder_name; } in
    clrec (hole :: holes) (n + 1) t2
  | LetIn (na, b, _, t) -> clrec holes n (subst1 b t)
  | _ -> holes
  in
  let holes = clrec [] 0 t in
  List.rev holes

let evar_with_name holes ({CAst.v=id} as lid) =
  let map h = match h.hole_name with
  | Anonymous -> None
  | Name id' -> if Id.equal id id' then Some h else None
  in
  let hole = List.map_filter map holes in
  match hole with
  | [] ->
    let fold h accu = match h.hole_name with
      | Anonymous -> accu
      | Name id -> id :: accu
    in
    let mvl = List.fold_right fold holes [] in
    EClause.explain_no_such_bound_variable mvl lid
  | h::_ -> h.hole_evar

let evar_of_binder holes = function
| NamedHyp s -> evar_with_name holes s
| AnonHyp n ->
  try
    let nondeps = List.filter (fun hole -> not hole.hole_deps) holes in
    let h = List.nth nondeps (pred n) in
    h.hole_evar
  with e when CErrors.noncritical e ->
    user_err Pp.(str "No such binder.")

let solve_evar_clause sigma unify holes = function
| NoBindings -> sigma
| ImplicitBindings largs ->
  let map h = if h.hole_deps then Some h.hole_evar else None in
  let evs = List.map_filter map holes in
  let len = List.length evs in
  if Int.equal len (List.length largs) then
    let fold sigma ev arg = unify sigma ev arg in
    let sigma = List.fold_left2 fold sigma evs largs in
    sigma
  else
    EClause.error_not_right_number_missing_arguments len
| ExplicitBindings lbind ->
  let () = EClause.check_bindings lbind in
  let fold sigma {CAst.v=(binder, c)} =
    let ev = evar_of_binder holes binder in
    unify sigma ev c
  in
  let sigma = List.fold_left fold sigma lbind in
  sigma

let unify_bindings sigma unify ty =
  let holes = make_evar_clause sigma ty in
  solve_evar_clause sigma unify holes

end

let specialize (c,lbind) ipat =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let typ_of_c = Retyping.get_type_of env sigma c in
  let sigma, term, typ = match lbind with
  | NoBindings ->
    sigma, c, typ_of_c
  | ExplicitBindings _ | ImplicitBindings _ ->
    let ctx, ty = decompose_prod_decls sigma typ_of_c in
    (* Create a new context where variables mentioned further in the telescope
       are turned into evars that live in the telescope context. This allows
       instantiating each evar with the original variable as a default value.

       For instance, on Γ := [x : A, y : B{x}, z : C{x, y}] it produces evars
       [x : A ⊢ ?X : A]
       [x : A, y : B{?X{x}} ⊢ ?Y : B{?X{x}}]
       [x : A, y : B{?X{x}}, z : C{?X{x}, ?Y{x, y}} ⊢ ?Z : C{?X{x}, ?Y{x, y}}]
       and returns the context
       Δ := [x : A, y : B{?X{x}}, z : C{?X{x}, ?Y{x, y}}]
       together with a substitution [?X, ?Y, ?Z] : Γ ⊢ Δ.
    *)
    let open RelDecl in
    let rec instantiate sigma env subst accu = function
    | [] -> sigma, subst, rel_context env, List.rev accu
    | LocalAssum (na, t) :: decls ->
      let t = Vars.esubst Vars.lift_substituend subst t in
      let env = push_rel (LocalAssum (na, t)) env in
      let sigma, ev = Evarutil.new_evar env sigma (lift 1 t) in
      let subst = Esubst.subs_cons (Vars.make_substituend ev) (Esubst.subs_shft (1, subst)) in
      instantiate sigma env subst ((env, ev) :: accu) decls
    | LocalDef (na, b, t) :: decls ->
      let b = Vars.esubst Vars.lift_substituend subst b in
      let t = Vars.esubst Vars.lift_substituend subst t in
      let env = push_rel (LocalDef (na, b, t)) env in
      let subst = Esubst.subs_lift subst in
      instantiate sigma env subst accu decls
    in
    let sigma, subst, nctx, holes = instantiate sigma env (Esubst.subs_id 0) [] (List.rev ctx) in
    let nty = Vars.esubst Vars.lift_substituend subst ty in
    (* Solve holes with the provided bindings *)
    let unify sigma n c =
      let env, ev = List.nth holes n in
      Evarconv.unify env sigma CONV ev c
    in
    let sigma = Specialize.unify_bindings sigma unify typ_of_c lbind in
    (* Instantiate unsolved holes with their default value *)
    let fold sigma (env, ev) =
      if isEvar sigma ev then Evarconv.unify env sigma CONV ev (mkRel 1)
      else sigma
    in
    let sigma = List.fold_left fold sigma holes in
    (* Requantify the proof term and its type *)
    let args = Context.Rel.instance_list mkRel 0 ctx in
    let nc = applist (c, List.map (fun c -> Vars.esubst Vars.lift_substituend subst c) args) in
    let rec rebuild rels ctx c ty = match ctx with
    | [] -> c, ty
    | decl :: ctx ->
      let lift s = Int.Set.fold (fun n accu -> Int.Set.add (n - 1) accu) s Int.Set.empty in
      let c, ty, rels =
        (* We always keep let bindings *)
        if RelDecl.is_local_def decl || Int.Set.mem 1 rels then
          let rels = lift (Int.Set.remove 1 rels) in
          let rels = RelDecl.fold_constr (fun c accu -> Int.Set.union accu (free_rels sigma c)) decl rels in
          mkLambda_or_LetIn decl c, mkProd_or_LetIn decl ty, rels
        else subst1 mkProp (* dummy *) c, subst1 mkProp ty, lift rels
      in
      rebuild rels ctx c ty
    in
    let rels = Int.Set.union (free_rels sigma nc) (free_rels sigma nty) in
    let nc, nty = rebuild rels nctx nc nty in
    sigma, nc, nty
  in
  let tac =
    match EConstr.kind sigma (fst(EConstr.decompose_app sigma (snd(EConstr.decompose_lambda_decls sigma c)))) with
    | Var id when Id.List.mem id (Tacmach.pf_ids_of_hyps gl) ->
      (* Like assert (id:=id args) but with the concept of specialization *)
      let ipat = match ipat with None -> Some (CAst.make (IntroNaming (IntroIdentifier id))) | _ -> ipat in
      let naming,tac = prepare_intros_opt false IntroAnonymous MoveLast ipat in
      let repl = do_replace (Some id) naming in
      (* "specialize H ... as H", "specialize H ...": do not clear (cleared implicitly at replacing time) *)
      (* "specialize H ... as H'", "specialize H ... as ?H": keep a copy by convention *)
      (* "specialize H ... as any_other_pattern": clear *)
      let doclear = match ipat with
        | Some {CAst.v=IntroNaming (IntroIdentifier _ | IntroFresh _)} -> false
        | _ -> true in
      let tac = if doclear then fun id' -> Tacticals.tclTHEN (clear [id]) (tac id') else tac in
      Tacticals.tclTHENFIRST
        (assert_before_then_gen repl naming typ tac)
        (exact_no_check term)
    | _ ->
      match ipat with
      | None ->
        (* Like generalize with extra support for "with" bindings *)
        (* even though the "with" bindings forces full application *)
        (* TODO: add intro to be more homogeneous. It will break
           scripts but will be easy to fix *)
         (Tacticals.tclTHENLAST (cut typ) (exact_no_check term))
      | Some _ as ipat ->
        (* Like pose proof with extra support for "with" bindings *)
        (* even though the "with" bindings forces full application *)
        let naming, tac = prepare_intros_opt false IntroAnonymous MoveLast ipat in
        Tacticals.tclTHENFIRST
          (assert_before_then_gen false naming typ tac)
          (exact_no_check term)
  in
  Tacticals.tclTHEN (Proofview.Unsafe.tclEVARS sigma) tac
  end

(*****************************)
(* Ad hoc unfold             *)
(*****************************)

(* The two following functions should already exist, but found nowhere *)
(* Unfolds x by its definition everywhere *)
let unfold_body x =
  let open Context.Named.Declaration in
  Proofview.Goal.enter begin fun gl ->
  (* We normalize the given hypothesis immediately. *)
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let xval = match Environ.lookup_named x env with
  | LocalAssum _ -> error (VariableHasNoValue x)
  | LocalDef (_,xval,_) -> xval
  in
  let xval = EConstr.of_constr xval in
  Tacticals.afterHyp x begin fun aft ->
  let hl = List.fold_right (fun decl cl -> (NamedDecl.get_id decl, InHyp) :: cl) aft [] in
  let rfun _ _ c = replace_vars sigma [x, xval] c in
  let reducth h = reduct_in_hyp ~check:false ~reorder:false rfun h in
  let reductc = reduct_in_concl ~cast:false ~check:false (rfun, DEFAULTcast) in
  Tacticals.tclTHENLIST [Tacticals.tclMAP reducth hl; reductc]
  end
  end

let dest_intro_patterns with_evars avoid thin dest pat tac =
  intro_patterns_core with_evars avoid [] thin dest None 0 tac pat

let rocq_heq_ref        = lazy (Rocqlib.lib_ref "core.JMeq.type")

let compare_upto_variables sigma x y =
  let rec compare x y =
    if (isVar sigma x || isRel sigma x) && (isVar sigma y || isRel sigma y) then true
    else compare_constr sigma compare x y
  in
  compare x y

let specialize_eqs id =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let ty = Tacmach.pf_get_hyp_typ id gl in
  let evars = ref (Proofview.Goal.sigma gl) in
  let unif env evars c1 c2 =
    compare_upto_variables !evars c1 c2 &&
    (match Evarconv.unify_delay env !evars c1 c2 with
     | sigma -> evars := sigma; true
     | exception Evarconv.UnableToUnify _ -> false)
  in
  let rec aux in_eqs ctx acc ty =
    match EConstr.kind !evars ty with
    | Prod (na, t, b) ->
        (match EConstr.kind !evars t with
        | App (eq, [| eqty; x; y |]) when is_lib_ref env !evars "core.eq.type" eq ->
            let c = if noccur_between !evars 1 (List.length ctx) x then y else x in
            let pt = mkApp (eq, [| eqty; c; c |]) in
            let ind = destInd !evars eq in
            let p = mkApp (mkConstructUi (ind,0), [| eqty; c |]) in
              if unif (push_rel_context ctx env) evars pt t then
                aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
              else acc, in_eqs, ctx, ty
        | App (heq, [| eqty; x; eqty'; y |]) when isRefX env !evars (Lazy.force rocq_heq_ref) heq ->
            let eqt, c = if noccur_between !evars 1 (List.length ctx) x then eqty', y else eqty, x in
            let pt = mkApp (heq, [| eqt; c; eqt; c |]) in
            let ind = destInd !evars heq in
            let p = mkApp (mkConstructUi (ind,0), [| eqt; c |]) in
              if unif (push_rel_context ctx env) evars pt t then
                aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
              else acc, in_eqs, ctx, ty
        | _ ->
            if in_eqs then acc, in_eqs, ctx, ty
            else
              let sigma, e = Evarutil.new_evar (push_rel_context ctx env) !evars t in
              evars := sigma;
                aux false (LocalDef (na,e,t) :: ctx) (mkApp (lift 1 acc, [| mkRel 1 |])) b)
    | t -> acc, in_eqs, ctx, ty
  in
  let acc, worked, ctx, ty = aux false [] (mkVar id) ty in
  let ctx' = nf_rel_context_evar !evars ctx in
  let ctx'' = List.map (function
    | LocalDef (n,k,t) when isEvar !evars k -> LocalAssum (n,t)
    | decl -> decl) ctx'
  in
  let ty' = it_mkProd_or_LetIn ty ctx'' in
  let acc' = it_mkLambda_or_LetIn acc ctx'' in
  let ty' = Tacred.whd_simpl env !evars ty'
  and acc' = Tacred.whd_simpl env !evars acc' in
  let ty' = Evarutil.nf_evar !evars ty' in
    if worked then
      Tacticals.tclTHENFIRST
        (internal_cut true id ty')
        (exact_no_check ((* refresh_universes_strict *) acc'))
    else
      let info = Exninfo.reify () in
      Tacticals.tclFAIL ~info (str "Nothing to do in hypothesis " ++ Id.print id)
  end

let specialize_eqs id = Proofview.Goal.enter begin fun gl ->
  let msg = str "Specialization not allowed on dependent hypotheses" in
  Proofview.tclOR (clear [id])
    (fun (_,info) -> Tacticals.tclZEROMSG ~info msg) >>= fun () ->
    specialize_eqs id
end

let exfalso =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, f) = Evd.fresh_global env sigma (Rocqlib.lib_ref "core.False.type") in
    let (ind, _) = reduce_to_atomic_ind env sigma f in
    let s = Retyping.get_sort_family_of env sigma (Proofview.Goal.concl gl) in
    let sigma, elimc = find_ind_eliminator env sigma (fst ind) s in
    let elimc = mkConstU elimc in
    let elimt = Retyping.get_type_of env sigma elimc in
    let clause = mk_clenv_from env sigma (elimc, elimt) in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) (Clenv.res_pf clause ~flags:(elim_flags ()) ~with_evars:false)
  end

(************************************************)
(*  Tactics related with logic connectives      *)
(************************************************)

(* Reflexivity tactics *)

let (forward_setoid_reflexivity, setoid_reflexivity) = Hook.make ()

let maybe_betadeltaiota_concl allowred gl =
  let concl = Tacmach.pf_concl gl in
  let sigma = Tacmach.project gl in
  if not allowred then concl
  else
    let env = Proofview.Goal.env gl in
    whd_all env sigma concl

let reflexivity_red allowred =
  Proofview.Goal.enter begin fun gl ->
  (* PL: usual reflexivity don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
    let env = Tacmach.pf_env gl in
    let sigma = Tacmach.project gl in
    let concl = maybe_betadeltaiota_concl allowred gl in
    match match_with_equality_type env sigma concl with
    | None ->
      let info = Exninfo.reify () in
      Proofview.tclZERO ~info NoEquationFound
    | Some _ -> one_constructor 1 NoBindings
  end

let reflexivity =
  Proofview.tclORELSE
    (reflexivity_red false)
    begin function (e, info) -> match e with
      | NoEquationFound -> Hook.get forward_setoid_reflexivity
      | e -> Proofview.tclZERO ~info e
    end

let intros_reflexivity  = (Tacticals.tclTHEN intros reflexivity)

(* Symmetry tactics *)

(* This tactic first tries to apply a constant named sym_eq, where eq
   is the name of the equality predicate. If this constant is not
   defined and the conclusion is a=b, it solves the goal doing (Cut
   b=a;Intro H;Case H;Constructor 1) *)

let (forward_setoid_symmetry, setoid_symmetry) = Hook.make ()

(* This is probably not very useful any longer *)
let prove_symmetry hdcncl eq_kind =
  let symc =
    match eq_kind with
    | MonomorphicLeibnizEq (c1,c2) -> mkApp(hdcncl,[|c2;c1|])
    | PolymorphicLeibnizEq (typ,c1,c2) -> mkApp(hdcncl,[|typ;c2;c1|])
    | HeterogenousEq (t1,c1,t2,c2) -> mkApp(hdcncl,[|t2;c2;t1;c1|]) in
  Tacticals.tclTHENFIRST (cut symc)
    (Tacticals.tclTHENLIST
      [ intro;
        Tacticals.onLastHyp simplest_case;
        one_constructor 1 NoBindings ])

let match_with_equation c =
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.tclENV >>= fun env ->
  try
    let res = match_with_equation env sigma c in
    Proofview.tclUNIT res
  with NoEquationFound as exn ->
    let _, info = Exninfo.capture exn in
    Proofview.tclZERO ~info NoEquationFound

let symmetry_red allowred =
  Proofview.Goal.enter begin fun gl ->
  (* PL: usual symmetry don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
  let concl = maybe_betadeltaiota_concl allowred gl in
  match_with_equation concl >>= fun with_eqn ->
  match with_eqn with
  | Some eq_data,_,_ ->
      Tacticals.tclTHEN
        (convert_concl ~cast:false ~check:false concl DEFAULTcast)
        (Tacticals.pf_constr_of_global eq_data.sym >>= apply)
  | None,eq,eq_kind -> prove_symmetry eq eq_kind
  end

let symmetry =
  Proofview.tclORELSE
    (symmetry_red false)
    begin function (e, info) -> match e with
      | NoEquationFound -> Hook.get forward_setoid_symmetry
      | e -> Proofview.tclZERO ~info e
    end

let (forward_setoid_symmetry_in, setoid_symmetry_in) = Hook.make ()


let symmetry_in id =
  Proofview.Goal.enter begin fun gl ->
    let sigma, ctype = Tacmach.pf_type_of gl (mkVar id) in
    let sign,t = decompose_prod_decls sigma ctype in
    tclEVARSTHEN sigma
      (Proofview.tclORELSE
         begin
           match_with_equation t >>= fun (_,hdcncl,eq) ->
           let symccl =
             match eq with
             | MonomorphicLeibnizEq (c1,c2) -> mkApp (hdcncl, [| c2; c1 |])
             | PolymorphicLeibnizEq (typ,c1,c2) -> mkApp (hdcncl, [| typ; c2; c1 |])
             | HeterogenousEq (t1,c1,t2,c2) -> mkApp (hdcncl, [| t2; c2; t1; c1 |]) in
           Tacticals.tclTHENS (cut (EConstr.it_mkProd_or_LetIn symccl sign))
             [ intro_replacing id;
               Tacticals.tclTHENLIST [ intros; symmetry; apply (mkVar id); assumption ] ]
         end
         begin function (e, info) -> match e with
           | NoEquationFound -> Hook.get forward_setoid_symmetry_in id
           | e -> Proofview.tclZERO ~info e
         end)
  end

let intros_symmetry =
  Tacticals.onClause
    (function
      | None -> Tacticals.tclTHEN intros symmetry
      | Some id -> symmetry_in id)

(* Transitivity tactics *)

(* This tactic first tries to apply a constant named eq_trans, where eq
   is the name of the equality predicate. If this constant is not
   defined and the conclusion is a=b, it solves the goal doing
   Cut x1=x2;
       [Cut x2=x3; [Intros e1 e2; Case e2;Assumption
                    | Idtac]
       | Idtac]
   --Eduardo (19/8/97)
*)

let (forward_setoid_transitivity, setoid_transitivity) = Hook.make ()


(* This is probably not very useful any longer *)
let prove_transitivity hdcncl eq_kind t =
  Proofview.Goal.enter begin fun gl ->
    let eq1, eq2 = match eq_kind with
      | MonomorphicLeibnizEq (c1,c2) ->
        mkApp (hdcncl, [| c1; t|]), mkApp (hdcncl, [| t; c2 |])
      | PolymorphicLeibnizEq (typ,c1,c2) ->
        mkApp (hdcncl, [| typ; c1; t |]), mkApp (hdcncl, [| typ; t; c2 |])
      | HeterogenousEq (typ1,c1,typ2,c2) ->
        let env = Proofview.Goal.env gl in
        let sigma = Tacmach.project gl in
        let typt = Retyping.get_type_of env sigma t in
        mkApp(hdcncl, [| typ1; c1; typt ;t |]),
        mkApp(hdcncl, [| typt; t; typ2; c2 |])
    in
    Tacticals.tclTHENFIRST (cut eq2)
      (Tacticals.tclTHENFIRST (cut eq1)
         (Tacticals.tclTHENLIST
            [ Tacticals.tclDO 2 intro;
              Tacticals.onLastHyp simplest_case;
              assumption ]))
  end

let transitivity_red allowred t =
  Proofview.Goal.enter begin fun gl ->
  (* PL: usual transitivity don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
  let concl = maybe_betadeltaiota_concl allowred gl in
  match_with_equation concl >>= fun with_eqn ->
  match with_eqn with
  | Some eq_data,_,_ ->
      Tacticals.tclTHEN
        (convert_concl ~cast:false ~check:false concl DEFAULTcast)
        (match t with
          | None -> Tacticals.pf_constr_of_global eq_data.trans >>= eapply
          | Some t -> Tacticals.pf_constr_of_global eq_data.trans >>= fun trans -> apply_list [trans; t])
   | None,eq,eq_kind ->
      match t with
      | None ->
        let info = Exninfo.reify () in
        Tacticals.tclZEROMSG ~info (str"etransitivity not supported for this relation.")
      | Some t -> prove_transitivity eq eq_kind t
  end

let transitivity_gen t =
  Proofview.tclORELSE
    (transitivity_red false t)
    begin function (e, info) -> match e with
      | NoEquationFound -> Hook.get forward_setoid_transitivity t
      | e -> Proofview.tclZERO ~info e
    end

let etransitivity = transitivity_gen None
let transitivity t = transitivity_gen (Some t)

let intros_transitivity  n  = Tacticals.tclTHEN intros (transitivity_gen n)

let constr_eq ~strict x y =
  let fail ~info = Tacticals.tclFAIL ~info (str "Not equal") in
  let fail_universes ~info = Tacticals.tclFAIL ~info (str "Not equal (due to universes)") in
  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.pf_env gl in
    let evd = Tacmach.project gl in
      match EConstr.eq_constr_universes env evd x y with
      | Some csts ->
        if strict then
          if UState.check_universe_constraints (Evd.ustate evd) csts
          then Proofview.tclUNIT ()
          else
            let info = Exninfo.reify () in
            fail_universes ~info
        else
        let csts = UnivProblem.Set.force csts in
        begin match Evd.add_universe_constraints evd csts with
           | evd -> Proofview.Unsafe.tclEVARS evd
           | exception (UGraph.UniverseInconsistency _ as e) ->
             let _, info = Exninfo.capture e in
             fail_universes ~info
        end
      | None ->
        let info = Exninfo.reify () in
        fail ~info
  end

let unify ?(state=TransparentState.full) x y =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  try
    let core_flags =
      { (default_unify_flags ()).core_unify_flags with
        modulo_delta = state;
        modulo_conv_on_closed_terms = Some state} in
    (* What to do on merge and subterm flags?? *)
    let flags = { (default_unify_flags ()) with
      core_unify_flags = core_flags;
      merge_unify_flags = core_flags;
      subterm_unify_flags = { core_flags with modulo_delta = TransparentState.empty } }
    in
    let _, sigma = w_unify (Tacmach.pf_env gl) sigma Conversion.CONV ~flags x y in
    Proofview.Unsafe.tclEVARS sigma
  with e when noncritical e ->
    let e, info = Exninfo.capture e in
    Proofview.tclZERO ~info (PretypeError (env, sigma, CannotUnify (x, y, None)))
  end

let evarconv_unify ?(state=TransparentState.full) ?(with_ho=true) x y =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  try
    let flags = Evarconv.default_flags_of state in
    let sigma = Evarconv.unify ~flags ~with_ho env sigma Conversion.CONV x y in
    Proofview.Unsafe.tclEVARS sigma
  with e when noncritical e ->
    let e, info = Exninfo.capture e in
    Proofview.tclZERO ~info (PretypeError (env, sigma, CannotUnify (x, y, None)))
  end

(** [tclWRAPFINALLY before tac finally] runs [before] before each
    entry-point of [tac] and passes the result of [before] to
    [finally], which is then run at each exit-point of [tac],
    regardless of whether it succeeds or fails.  Said another way, if
    [tac] succeeds, then it behaves as [before >>= fun v -> tac >>= fun
    ret -> finally v <*> tclUNIT ret]; otherwise, if [tac] fails with
    [e], it behaves as [before >>= fun v -> finally v <*> tclZERO
    e].  Note that if [tac] succeeds [n] times before finally failing,
    [before] and [finally] are both run [n+1] times (once around each
    succuess, and once more around the final failure). *)
(* We should probably export this somewhere, but it's not clear
   where. As per
   https://github.com/coq/coq/pull/12197#discussion_r418480525 and
   https://gitter.im/coq/coq?at=5ead5c35347bd616304e83ef, we don't
   export it from Proofview, because it seems somehow not primitive
   enough.  We don't export it from this file because it is more of a
   tactical than a tactic.  But we also don't export it from Tacticals
   because all of the non-New tacticals there operate on `tactic`, not
   `Proofview.tactic`, and all of the `New` tacticals that deal with
   multi-success things are focussing, i.e., apply their arguments on
   each goal separately (and it even says so in the comment on `New`),
   whereas it's important that `tclWRAPFINALLY` doesn't introduce
   extra focussing. *)
let rec tclWRAPFINALLY before tac finally =
  let open Proofview in
  let open Proofview.Notations in
  before >>= fun v -> tclCASE tac >>= function
  | Fail (e, info) -> finally v >>= fun () -> tclZERO ~info e
  | Next (ret, tac') -> tclOR
                          (finally v >>= fun () -> tclUNIT ret)
                          (fun e -> tclWRAPFINALLY before (tac' e) finally)

let with_set_strategy lvl_ql k =
  let glob_key r =
    match r with
    | GlobRef.ConstRef sp ->
        begin
          match Structures.PrimitiveProjections.find_opt sp with
          | None -> Evaluable.EvalConstRef sp
          | Some p -> Evaluable.EvalProjectionRef p
        end
    | GlobRef.VarRef id -> Evaluable.EvalVarRef id
    | _ -> user_err Pp.(str
                          "cannot set an inductive type or a constructor as transparent") in
  let kl = List.concat (List.map (fun (lvl, ql) -> List.map (fun q -> (lvl, glob_key q)) ql) lvl_ql) in
  tclWRAPFINALLY
    (Proofview.tclENV >>= fun env ->
     let orig_kl = List.map (fun (_lvl, k) ->
         (Conv_oracle.get_strategy (Environ.oracle env) (Evaluable.to_kevaluable k), k))
         kl in
     (* Because the global env might be desynchronized from the
        proof-local env, we need to update the global env to have this
        tactic play nicely with abstract.
        TODO: When abstract no longer depends on Global, delete this
        let orig_kl_global = ... in *)
     let orig_kl_global = List.map (fun (_lvl, k) ->
         (Conv_oracle.get_strategy (Environ.oracle (Global.env ())) (Evaluable.to_kevaluable k), k))
         kl in
     let env = List.fold_left (fun env (lvl, k) ->
         Environ.set_oracle env
           (Conv_oracle.set_strategy (Environ.oracle env) (Evaluable.to_kevaluable k) lvl)) env kl in
     Proofview.Unsafe.tclSETENV env <*>
     (* TODO: When abstract no longer depends on Global, remove this
        [Proofview.tclLIFT] block *)
     Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
         List.iter (fun (lvl, k) -> Global.set_strategy (Evaluable.to_kevaluable k) lvl) kl)) <*>
     Proofview.tclUNIT (orig_kl, orig_kl_global))
    k
    (fun (orig_kl, orig_kl_global) ->
       (* TODO: When abstract no longer depends on Global, remove this
          [Proofview.tclLIFT] block *)
       Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
           List.iter (fun (lvl, k) -> Global.set_strategy (Evaluable.to_kevaluable k) lvl) orig_kl_global)) <*>
       Proofview.tclENV >>= fun env ->
       let env = List.fold_left (fun env (lvl, k) ->
           Environ.set_oracle env
             (Conv_oracle.set_strategy (Environ.oracle env) (Evaluable.to_kevaluable k) lvl)) env orig_kl in
       Proofview.Unsafe.tclSETENV env)

module Simple = struct
  (** Simplified version of some of the above tactics *)

  let intro x = intro_move (Some x) MoveLast

  let apply c =
    apply_with_bindings_gen false false [None,(CAst.make (c,NoBindings))]
  let eapply c =
    apply_with_bindings_gen false true [None,(CAst.make (c,NoBindings))]
  let elim c   = elim false None (c,NoBindings) None
  let case   c = general_case_analysis false None (c,NoBindings)

  let apply_in id c =
    apply_in false false id [None,(CAst.make (c, NoBindings))] None

end


(** Tacticals defined directly in term of Proofview *)
let reduce_after_refine =
  (* For backward compatibility reasons, we do not contract let-ins, but we unfold them. *)
  let redfun env t =
    let flags = RedFlags.red_add_transparent RedFlags.allnolet TransparentState.empty in
    clos_norm_flags flags env t
  in
  reduct_in_concl ~cast:false ~check:false (redfun,DEFAULTcast)

let refine ~typecheck c =
  Refine.refine ~typecheck c <*>
  reduce_after_refine

module Internal =
struct

let explicit_intro_names = explicit_intro_names
let check_name_unicity = check_name_unicity
let clear_gen = clear_gen
let clear_wildcards = clear_wildcards
let dest_intro_patterns = dest_intro_patterns

end
