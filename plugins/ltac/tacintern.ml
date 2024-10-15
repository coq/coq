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
open CAst
open Genredexpr
open Glob_term
open Util
open Names
open Libnames
open Smartlocate
open Constrexpr
open Termops
open Tacexpr
open Genarg
open Stdarg
open Tacarg
open Namegen
open Tactypes
open Tactics
open Locus

(** Globalization of tactic expressions :
    Conversion from [raw_tactic_expr] to [glob_tactic_expr] *)

let error_tactic_expected ?loc =
  user_err ?loc  (str "Tactic expected.")

(** Generic arguments *)

type glob_sign = Genintern.glob_sign = {
  ltacvars : Id.Set.t;
     (* ltac variables and the subset of vars introduced by Intro/Let/... *)
  genv : Environ.env;
  extra : Genintern.Store.t;
  intern_sign : Genintern.intern_variable_status;
  strict_check : bool;
}

let make_empty_glob_sign ~strict = Genintern.empty_glob_sign ~strict (Global.env ())

(* We have identifier <| global_reference <| constr *)

let find_ident id ist =
  Id.Set.mem id ist.ltacvars ||
  Id.List.mem id (ids_of_named_context (Environ.named_context ist.genv))

(* a "var" is a ltac var or a var introduced by an intro tactic *)
let find_var id ist = Id.Set.mem id ist.ltacvars

let find_hyp id ist =
  Id.List.mem id (ids_of_named_context (Environ.named_context ist.genv))

(* Globalize a name introduced by Intro/LetTac/... ; it is allowed to *)
(* be fresh in which case it is binding later on *)
let intern_ident s ist id =
  (* We use identifier both for variables and new names; thus nothing to do *)
  if not (find_ident id ist) then s := Id.Set.add id !s;
  id

let intern_name l ist = function
  | Anonymous -> Anonymous
  | Name id -> Name (intern_ident l ist id)

(* Globalize a name which must be bound -- actually just check it is bound *)
let intern_hyp ist ({loc;v=id} as locid) =
  if not ist.strict_check then
    locid
  else if find_ident id ist then
    make id
  else
    CErrors.user_err ?loc Pp.(str "Hypothesis" ++ spc () ++ Id.print id ++ spc() ++
                              str "was not found in the current environment.")

let intern_or_var f ist = function
  | ArgVar locid -> ArgVar (intern_hyp ist locid)
  | ArgArg x -> ArgArg (f x)

let intern_int_or_var = intern_or_var (fun (n : int) -> n)
let intern_string_or_var = intern_or_var (fun (s : string) -> s)

let intern_global_reference ist qid =
  if qualid_is_ident qid && find_var (qualid_basename qid) ist then
    ArgVar (make ?loc:qid.CAst.loc @@ qualid_basename qid)
  else if qualid_is_ident qid && find_hyp (qualid_basename qid) ist then
    let id = qualid_basename qid in
    ArgArg (qid.CAst.loc, GlobRef.VarRef id)
  else
    let r =
      try locate_global_with_alias ~head:true qid
      with
      | Not_found as exn ->
        if not ist.strict_check && qualid_is_ident qid then
          let id = qualid_basename qid in
          GlobRef.VarRef id
        else
          let _, info = Exninfo.capture exn in
          Nametab.error_global_not_found ~info qid
    in
    ArgArg (qid.CAst.loc, r)

let intern_ltac_variable ist qid =
  if qualid_is_ident qid && find_var (qualid_basename qid) ist then
    (* A local variable of any type *)
    ArgVar (make ?loc:qid.CAst.loc @@ qualid_basename qid)
  else raise Not_found

let intern_constr_reference strict ist qid =
  let id = qualid_basename qid in
  if qualid_is_ident qid && not strict && find_hyp (qualid_basename qid) ist then
    (DAst.make @@ GVar id), Some (make @@ CRef (qid,None))
  else if qualid_is_ident qid && find_var (qualid_basename qid) ist then
    (DAst.make @@ GVar id), if strict then None else Some (make @@ CRef (qid,None))
  else
    DAst.make @@ GRef (locate_global_with_alias qid,None),
    if strict then None else Some (make @@ CRef (qid,None))

(* Internalize an isolated reference in position of tactic *)

let warn_deprecated_tactic =
  Deprecation.create_warning ~object_name:"Tactic"
    ~warning_name_if_no_since:"deprecated-tactic"
    pr_qualid

let warn_deprecated_alias =
  Deprecation.create_warning ~object_name:"Tactic Notation"
    ~warning_name_if_no_since:"deprecated-tactic-notation"
    Pptactic.pr_alias_key

let intern_isolated_global_tactic_reference qid =
  let loc = qid.CAst.loc in
  let kn = Tacenv.locate_tactic qid in
  Option.iter (fun depr -> warn_deprecated_tactic ?loc (qid,depr)) @@
    Tacenv.tac_deprecation kn;
  TacCall (CAst.make ?loc (ArgArg (loc,kn),[]))

let intern_isolated_tactic_reference strict ist qid =
  (* An ltac reference *)
  try Reference (intern_ltac_variable ist qid)
  with Not_found ->
  (* A global tactic *)
  try intern_isolated_global_tactic_reference qid
  with Not_found ->
  (* Tolerance for compatibility, allow not to use "constr:" *)
  try ConstrMayEval (ConstrTerm (intern_constr_reference strict ist qid))
  with Not_found as exn ->
    (* Reference not found *)
    let _, info = Exninfo.capture exn in
    Nametab.error_global_not_found ~info qid

(* Internalize an applied tactic reference *)

let intern_applied_global_tactic_reference qid =
  let loc = qid.CAst.loc in
  let kn = Tacenv.locate_tactic qid in
  Option.iter (fun depr -> warn_deprecated_tactic ?loc (qid,depr)) @@
    Tacenv.tac_deprecation kn;
  ArgArg (loc,kn)

let intern_applied_tactic_reference ist qid =
  (* An ltac reference *)
  try intern_ltac_variable ist qid
  with Not_found ->
  (* A global tactic *)
  try intern_applied_global_tactic_reference qid
  with Not_found as exn ->
    (* Reference not found *)
    let _, info = Exninfo.capture exn in
    Nametab.error_global_not_found ~info qid

(* Intern a reference parsed in a non-tactic entry *)

let intern_non_tactic_reference strict ist qid =
  (* An ltac reference *)
  try Reference (intern_ltac_variable ist qid)
  with Not_found ->
  (* A constr reference *)
  try ConstrMayEval (ConstrTerm (intern_constr_reference strict ist qid))
  with Not_found ->
  (* Tolerance for compatibility, allow not to use "ltac:" *)
  try intern_isolated_global_tactic_reference qid
  with Not_found as exn ->
  (* By convention, use IntroIdentifier for unbound ident, when not in a def *)
  if qualid_is_ident qid && not strict then
    let id = qualid_basename qid in
    let ipat = in_gen (glbwit wit_intro_pattern) (make ?loc:qid.CAst.loc @@ IntroNaming (IntroIdentifier id)) in
    TacGeneric (None,ipat)
  else
    (* Reference not found *)
    let _, info = Exninfo.capture exn in
    Nametab.error_global_not_found ~info qid

let intern_message_token ist = function
  | (MsgString _ | MsgInt _ as x) -> x
  | MsgIdent id -> MsgIdent (intern_hyp ist id)

let intern_message ist = List.map (intern_message_token ist)

let intern_quantified_hypothesis ist = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      (* Uncomment to disallow "intros until n" in ltac when n is not bound *)
      NamedHyp ((*snd (intern_hyp ist (dloc,*)id(* ))*))

let intern_binding_name ist x =
  (* We use identifier both for variables and binding names *)
  (* Todo: consider the body of the lemma to which the binding refer
     and if a term w/o ltac vars, check the name is indeed quantified *)
  x

let intern_constr_gen pattern_mode isarity {ltacvars=lfun; genv=env; extra; intern_sign; strict_check} c =
  let scope = if isarity then Pretyping.IsType else Pretyping.WithoutTypeConstraint in
  let ltacvars = {
    Constrintern.ltac_vars = lfun;
    ltac_bound = Id.Set.empty;
    ltac_extra = extra;
  } in
  let c' = Constrintern.intern_core scope ~strict_check ~pattern_mode ~ltacvars env Evd.(from_env env) intern_sign c in
  (c',if strict_check then None else Some c)

let intern_constr = intern_constr_gen false false
let intern_type = intern_constr_gen false true

(* Globalize bindings *)
let intern_binding ist = map (fun (b,c) ->
    intern_binding_name ist b,intern_constr ist c)

let intern_bindings ist = function
  | NoBindings -> NoBindings
  | ImplicitBindings l -> ImplicitBindings (List.map (intern_constr ist) l)
  | ExplicitBindings l -> ExplicitBindings (List.map (intern_binding ist) l)

let intern_constr_with_bindings ist (c,bl) =
  (intern_constr ist c, intern_bindings ist bl)

let intern_constr_with_bindings_arg ist (clear,c) =
  (clear,intern_constr_with_bindings ist c)

let rec intern_intro_pattern lf ist = map (function
  | IntroNaming pat ->
    IntroNaming (intern_intro_pattern_naming lf ist pat)
  | IntroAction pat ->
    IntroAction (intern_intro_pattern_action lf ist pat)
  | IntroForthcoming _ as x -> x)

and intern_intro_pattern_naming lf ist = function
  | IntroIdentifier id ->
      IntroIdentifier (intern_ident lf ist id)
  | IntroFresh id ->
      IntroFresh (intern_ident lf ist id)
  | IntroAnonymous as x -> x

and intern_intro_pattern_action lf ist = function
  | IntroOrAndPattern l ->
    IntroOrAndPattern (intern_or_and_intro_pattern lf ist l)
  | IntroInjection l ->
    IntroInjection (List.map (intern_intro_pattern lf ist) l)
  | IntroWildcard | IntroRewrite _ as x -> x
  | IntroApplyOn ({loc;v=c},pat) ->
    IntroApplyOn (make ?loc @@ intern_constr ist c, intern_intro_pattern lf ist pat)

and intern_or_and_intro_pattern lf ist = function
   | IntroAndPattern l ->
      IntroAndPattern (List.map (intern_intro_pattern lf ist) l)
  | IntroOrPattern ll ->
      IntroOrPattern (List.map (List.map (intern_intro_pattern lf ist)) ll)

let intern_or_and_intro_pattern_loc lf ist = function
  | ArgVar {v=id} as x ->
      if find_var id ist then x
      else user_err Pp.(str "Disjunctive/conjunctive introduction pattern expected.")
  | ArgArg ll -> ArgArg (map (fun l -> intern_or_and_intro_pattern lf ist l) ll)

let intern_intro_pattern_naming_loc lf ist = map (fun pat ->
    intern_intro_pattern_naming lf ist pat)

  (* TODO: catch ltac vars *)
let intern_destruction_arg ist = function
  | clear,ElimOnConstr c -> clear,ElimOnConstr (intern_constr_with_bindings ist c)
  | clear,ElimOnAnonHyp n as x -> x
  | clear,ElimOnIdent {loc;v=id} ->
      if ist.strict_check then
        (* If in a defined tactic, no intros-until *)
        let c, p = intern_constr ist (make @@ CRef (qualid_of_ident id, None)) in
        match DAst.get c with
        | GVar id -> clear,ElimOnIdent (make ?loc:c.loc id)
        | _ -> clear,ElimOnConstr ((c, p), NoBindings)
      else
        clear,ElimOnIdent (make ?loc id)

let evalref_of_globref ?loc r =
  let () =
    (* only dump section variables not proof context variables
       (broken if variables got renamed) *)
    let is_proof_variable = match r with
      | GlobRef.VarRef x -> (try ignore (Global.lookup_named x); false with Not_found -> true)
      | _ -> false
    in
    if not is_proof_variable then Dumpglob.add_glob ?loc r
  in
  Tacred.soft_evaluable_of_global_reference ?loc r

let intern_smart_global ist = function
  | {v=AN r} -> intern_global_reference ist r
  | {v=ByNotation (ntn,sc);loc} ->
      ArgArg (loc, (Notation.interp_notation_as_global_reference ?loc ~head:true
        GlobRef.(function ConstRef _ | VarRef _ -> true | _ -> false) ntn sc))

let intern_constr_with_occurrences ist (l,c) = (l,intern_constr ist c)

let intern_constr_pattern ist ~as_type ~ltacvars pc =
  let ltacvars = {
    Constrintern.ltac_vars = ltacvars;
    ltac_bound = Id.Set.empty;
    ltac_extra = ist.extra;
  } in
  let metas,pat = Constrintern.intern_constr_pattern
    ist.genv Evd.(from_env ist.genv) ~as_type ~ltacvars pc
  in
  let (glob,_ as c) = intern_constr_gen true false ist pc in
  let bound_names = Glob_ops.bound_glob_vars glob in
  metas,(bound_names,c,pat)

let intern_typed_pattern ist p =
  (* we cannot ensure in non strict mode that the pattern is closed *)
  (* keeping a constr_expr copy is too complicated and we want anyway to *)
  (* type it, so we remember the pattern as a glob_constr only *)
  let metas =
    if ist.strict_check then
      let ltacvars = {
          Constrintern.ltac_vars = ist.ltacvars;
          ltac_bound = Id.Set.empty;
          ltac_extra = ist.extra;
        } in
      fst @@ Constrintern.intern_constr_pattern ist.genv Evd.(from_env ist.genv) ~ltacvars p
    else
      Id.Set.empty in
  let c = intern_constr_gen true false ist p in
  metas,c

let intern_local_evalref ist qid =
  if qualid_is_ident qid && find_var (qualid_basename qid) ist then
    Some (ArgVar (make ?loc:qid.CAst.loc @@ qualid_basename qid))
  else if qualid_is_ident qid && find_hyp (qualid_basename qid) ist then
    let id = qualid_basename qid in
    let loc = qid.loc in
    let r = GlobRef.VarRef id in
    let r = evalref_of_globref ?loc r in
    let short = if ist.strict_check then None else Some (CAst.make ?loc id) in
    Some (ArgArg (r, short))
  else None

let intern_red_expr ist r =
  let ltac_sign = {
    Constrintern.ltac_vars = ist.ltacvars;
    ltac_bound = Id.Set.empty;
    ltac_extra = ist.extra;
  }
  in
  let ist = {
    Redexpr.Intern.strict_check = ist.strict_check;
    local_ref = intern_local_evalref ist;
    global_ref = (fun ?short r -> ArgArg (r, short));
    intern_constr = intern_constr ist;
    ltac_sign;
    pattern_of_glob = (fun c -> (c, None));
    intern_pattern = (fun c -> snd @@ intern_typed_pattern ist c);
  }
  in
  Redexpr.Intern.intern_red_expr ist r

let intern_hyp_list ist = List.map (intern_hyp ist)

let intern_in_hyp_as ist lf (idl,ipat) =
  (intern_hyp ist idl, Option.map (intern_intro_pattern lf ist) ipat)

let intern_inversion_strength lf ist = function
  | NonDepInversion (k,idl,ids) ->
      NonDepInversion (k,intern_hyp_list ist idl,
      Option.map (intern_or_and_intro_pattern_loc lf ist) ids)
  | DepInversion (k,copt,ids) ->
      DepInversion (k, Option.map (intern_constr ist) copt,
      Option.map (intern_or_and_intro_pattern_loc lf ist) ids)
  | InversionUsing (c,idl) ->
      InversionUsing (intern_constr ist c, intern_hyp_list ist idl)

(* Interprets an hypothesis name *)
let intern_hyp_location ist ((occs,id),hl) =
  ((Locusops.occurrences_map (List.map (intern_int_or_var ist)) occs,
   intern_hyp ist id), hl)

(* Reads a pattern *)
let intern_pattern ist ?(as_type=false) ltacvars = function
  | Subterm (ido,pc) ->
      let (metas,pc) = intern_constr_pattern ist ~as_type:false ~ltacvars pc in
      ido, metas, Subterm (ido,pc)
  | Term pc ->
      let (metas,pc) = intern_constr_pattern ist ~as_type ~ltacvars pc in
      None, metas, Term pc

let intern_constr_may_eval ist = function
  | ConstrEval (r,c) -> ConstrEval (intern_red_expr ist r,intern_constr ist c)
  | ConstrContext (locid,c) ->
    ConstrContext (intern_hyp ist locid,intern_constr ist c)
  | ConstrTypeOf c -> ConstrTypeOf (intern_constr ist c)
  | ConstrTerm c -> ConstrTerm (intern_constr ist c)

let name_cons accu = function
| Anonymous -> accu
| Name id -> Id.Set.add id accu

let opt_cons accu = function
| None -> accu
| Some id -> Id.Set.add id accu

(* Reads the hypotheses of a "match goal" rule *)
let rec intern_match_goal_hyps ist ?(as_type=false) lfun = function
  | (Hyp ({v=na} as locna,mp))::tl ->
      let ido, metas1, pat = intern_pattern ist ~as_type:true lfun mp in
      let lfun, metas2, hyps = intern_match_goal_hyps ist lfun tl in
      let lfun' = name_cons (opt_cons lfun ido) na in
      lfun', Id.Set.union metas1 metas2, Hyp (locna,pat)::hyps
  | (Def ({v=na} as locna,mv,mp))::tl ->
      let ido, metas1, patv = intern_pattern ist ~as_type:false lfun mv in
      let ido', metas2, patt = intern_pattern ist ~as_type:true lfun mp in
      let lfun, metas3, hyps = intern_match_goal_hyps ist ~as_type lfun tl in
      let lfun' = name_cons (opt_cons (opt_cons lfun ido) ido') na in
      lfun', Id.Set.union metas1 (Id.Set.union metas2 metas3), Def (locna,patv,patt)::hyps
  | [] -> lfun, Id.Set.empty, []

(* Utilities *)
let extract_let_names lrc =
  let fold accu ({loc;v=name}, _) =
    Nameops.Name.fold_right (fun id accu ->
        if Id.Set.mem id accu then
          user_err ?loc (str "This variable is bound several times.")
        else Id.Set.add id accu)
      name
      accu
  in
  List.fold_left fold Id.Set.empty lrc

let clause_app f = function
    { onhyps=None; concl_occs=nl } ->
      { onhyps=None; concl_occs=nl }
  | { onhyps=Some l; concl_occs=nl } ->
      { onhyps=Some(List.map f l); concl_occs=nl}

(* Globalizes tactics : raw_tactic_expr -> glob_tactic_expr *)
let rec intern_atomic lf ist x =
  match (x:raw_atomic_tactic_expr) with
  (* Basic tactics *)
  | TacIntroPattern (ev,l) ->
      TacIntroPattern (ev,List.map (intern_intro_pattern lf ist) l)
  | TacApply (a,ev,cb,inhyp) ->
      TacApply (a,ev,List.map (intern_constr_with_bindings_arg ist) cb,
                List.map (intern_in_hyp_as ist lf) inhyp)
  | TacElim (ev,cb,cbo) ->
      TacElim (ev,intern_constr_with_bindings_arg ist cb,
               Option.map (intern_constr_with_bindings ist) cbo)
  | TacCase (ev,cb) -> TacCase (ev,intern_constr_with_bindings_arg ist cb)
  | TacMutualFix (id,n,l) ->
      let f (id,n,c) = (intern_ident lf ist id,n,intern_type ist c) in
      TacMutualFix (intern_ident lf ist id, n, List.map f l)
  | TacMutualCofix (id,l) ->
      let f (id,c) = (intern_ident lf ist id,intern_type ist c) in
      TacMutualCofix (intern_ident lf ist id, List.map f l)
  | TacAssert (ev,b,otac,ipat,c) ->
      TacAssert (ev,b,Option.map (Option.map (intern_pure_tactic ist)) otac,
                 Option.map (intern_intro_pattern lf ist) ipat,
                 intern_constr_gen false (not (Option.is_empty otac)) ist c)
  | TacGeneralize cl ->
      TacGeneralize (List.map (fun (c,na) ->
                       intern_constr_with_occurrences ist c,
                       intern_name lf ist na) cl)
  | TacLetTac (ev,na,c,cls,b,eqpat) ->
      let na = intern_name lf ist na in
      TacLetTac (ev,na,intern_constr ist c,
                 (clause_app (intern_hyp_location ist) cls),b,
                 (Option.map (intern_intro_pattern_naming_loc lf ist) eqpat))

  (* Derived basic tactics *)
  | TacInductionDestruct (ev,isrec,(l,el)) ->
      TacInductionDestruct (ev,isrec,(List.map (fun (c,(ipato,ipats),cls) ->
              (intern_destruction_arg ist c,
               (Option.map (intern_intro_pattern_naming_loc lf ist) ipato,
               Option.map (intern_or_and_intro_pattern_loc lf ist) ipats),
               Option.map (clause_app (intern_hyp_location ist)) cls)) l,
               Option.map (intern_constr_with_bindings ist) el))
  (* Conversion *)
  | TacReduce (r,cl) ->
      TacReduce (intern_red_expr ist r, clause_app (intern_hyp_location ist) cl)
  | TacChange (check,None,c,cl) ->
      let is_onhyps = match cl.onhyps with
      | None | Some [] -> true
      | _ -> false
      in
      let is_onconcl = match cl.concl_occs with
      | AtLeastOneOccurrence | AllOccurrences | NoOccurrences -> true
      | _ -> false
      in
      TacChange (check,None,
        (if is_onhyps && is_onconcl
         then intern_type ist c else intern_constr ist c),
        clause_app (intern_hyp_location ist) cl)
  | TacChange (check,Some p,c,cl) ->
      let metas,pat = intern_typed_pattern ist p in
      let ltacvars = Id.Set.union ist.ltacvars metas in
      let ist' = { ist with ltacvars } in
      TacChange (check,Some pat,intern_constr ist' c,
        clause_app (intern_hyp_location ist) cl)

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) ->
      TacRewrite
        (ev,
        List.map (fun (b,m,c) -> (b,m,intern_constr_with_bindings_arg ist c)) l,
        clause_app (intern_hyp_location ist) cl,
        Option.map (intern_pure_tactic ist) by)
  | TacInversion (inv,hyp) ->
      TacInversion (intern_inversion_strength lf ist inv,
        intern_quantified_hypothesis ist hyp)

and intern_tactic onlytac ist tac = snd (intern_tactic_seq onlytac ist tac)

and intern_tactic_seq onlytac ist tac =
  let (loc, tac) = CAst.(tac.loc, tac.v) in
  match tac with
  | TacAtom t ->
      let lf = ref ist.ltacvars in
      let t = intern_atomic lf ist t in
      !lf, CAst.make ?loc (TacAtom t)
  | TacFun tacfun -> ist.ltacvars, (CAst.make ?loc (TacFun (intern_tactic_fun ist tacfun)))
  | TacLetIn (isrec,l,u) ->
      let ltacvars = Id.Set.union (extract_let_names l) ist.ltacvars in
      let ist' = { ist with ltacvars } in
      let l = List.map (fun (n,b) ->
          (n,intern_tacarg ist.strict_check false (if isrec then ist' else ist) b)) l in
      ist.ltacvars, CAst.make ?loc (TacLetIn (isrec,l,intern_tactic onlytac ist' u))

  | TacMatchGoal (lz,lr,lmr) ->
      ist.ltacvars, CAst.make ?loc (TacMatchGoal (lz,lr, intern_match_rule onlytac ist ~as_type:true lmr))
  | TacMatch (lz,c,lmr) ->
      ist.ltacvars,
       CAst.make ?loc (TacMatch (lz,intern_tactic_or_tacarg ist c,intern_match_rule onlytac ist lmr))
  | TacId l -> ist.ltacvars, CAst.make ?loc (TacId (intern_message ist l))
  | TacFail (g,n,l) ->
      ist.ltacvars, CAst.make ?loc (TacFail (g,intern_int_or_var ist n,intern_message ist l))
  | TacProgress tac -> ist.ltacvars, CAst.make ?loc (TacProgress (intern_pure_tactic ist tac))
  | TacAbstract (tac,s) ->
      ist.ltacvars, CAst.make ?loc (TacAbstract (intern_pure_tactic ist tac,s))
  | TacThen (t1,t2) ->
      let lfun', t1 = intern_tactic_seq onlytac ist t1 in
      let lfun'', t2 = intern_tactic_seq onlytac { ist with ltacvars = lfun' } t2 in
      lfun'', CAst.make ?loc (TacThen (t1,t2))
  | TacDispatch tl ->
      ist.ltacvars , CAst.make ?loc (TacDispatch (List.map (intern_pure_tactic ist) tl))
  | TacExtendTac (tf,t,tl) ->
      ist.ltacvars, CAst.make ?loc (
      TacExtendTac (Array.map (intern_pure_tactic ist) tf,
                    intern_pure_tactic ist t,
                    Array.map (intern_pure_tactic ist) tl))
  | TacThens3parts (t1,tf,t2,tl) ->
      let lfun', t1 = intern_tactic_seq onlytac ist t1 in
      let ist' = { ist with ltacvars = lfun' } in
      (* Que faire en cas de (tac complexe avec Match et Thens; tac2) ?? *)
      lfun', CAst.make ?loc (TacThens3parts
                      (t1,Array.map (intern_pure_tactic ist') tf,intern_pure_tactic ist' t2,
                      Array.map (intern_pure_tactic ist') tl))
  | TacThens (t,tl) ->
      let lfun', t = intern_tactic_seq true ist t in
      let ist' = { ist with ltacvars = lfun' } in
      (* Que faire en cas de (tac complexe avec Match et Thens; tac2) ?? *)
      lfun', CAst.make ?loc (TacThens (t, List.map (intern_pure_tactic ist') tl))
  | TacDo (n,tac) ->
      ist.ltacvars, CAst.make ?loc (TacDo (intern_int_or_var ist n,intern_pure_tactic ist tac))
  | TacTry tac -> ist.ltacvars, CAst.make ?loc (TacTry (intern_pure_tactic ist tac))
  | TacRepeat tac -> ist.ltacvars, CAst.make ?loc (TacRepeat (intern_pure_tactic ist tac))
  | TacTimeout (n,tac) ->
      ist.ltacvars, CAst.make ?loc (TacTimeout (intern_int_or_var ist n,intern_tactic onlytac ist tac))
  | TacTime (s,tac) ->
      ist.ltacvars, CAst.make ?loc (TacTime (s,intern_tactic onlytac ist tac))
  | TacOr (tac1,tac2) ->
      ist.ltacvars, CAst.make ?loc (TacOr (intern_pure_tactic ist tac1,intern_pure_tactic ist tac2))
  | TacOnce tac ->
      ist.ltacvars, CAst.make ?loc (TacOnce (intern_pure_tactic ist tac))
  | TacExactlyOnce tac ->
      ist.ltacvars, CAst.make ?loc (TacExactlyOnce (intern_pure_tactic ist tac))
  | TacIfThenCatch (tac,tact,tace) ->
      ist.ltacvars,
      CAst.make ?loc (TacIfThenCatch (
        intern_pure_tactic ist tac,
        intern_pure_tactic ist tact,
        intern_pure_tactic ist tace))
  | TacOrelse (tac1,tac2) ->
      ist.ltacvars, CAst.make ?loc (TacOrelse (intern_pure_tactic ist tac1,intern_pure_tactic ist tac2))
  | TacFirst l -> ist.ltacvars, CAst.make ?loc (TacFirst (List.map (intern_pure_tactic ist) l))
  | TacSolve l -> ist.ltacvars, CAst.make ?loc (TacSolve (List.map (intern_pure_tactic ist) l))
  | TacArg a -> ist.ltacvars, intern_tactic_as_arg loc onlytac ist a
  | TacSelect (sel, tac) ->
      ist.ltacvars, CAst.make ?loc (TacSelect (sel, intern_pure_tactic ist tac))

  (* For extensions *)
  | TacAlias (s,l) ->
      let alias = Tacenv.interp_alias s in
      Option.iter (fun o -> warn_deprecated_alias ?loc (s,o)) @@ alias.Tacenv.alias_deprecation;
      let l = List.map (intern_tacarg ist.strict_check false ist) l in
      ist.ltacvars, CAst.make ?loc (TacAlias (s,l))
  | TacML (opn,l) ->
      let _ignore = Tacenv.interp_ml_tactic opn in
      ist.ltacvars, CAst.make ?loc (TacML (opn,List.map (intern_tacarg ist.strict_check false ist) l))

and intern_tactic_as_arg loc onlytac ist a =
  match intern_tacarg ist.strict_check onlytac ist a with
  | TacCall _ | Reference _
  | TacGeneric _ as a -> CAst.make ?loc (TacArg a)
  | Tacexp a -> a
  | ConstrMayEval _ | TacFreshId _ | TacPretype _ | TacNumgoals as a ->
      if onlytac then error_tactic_expected ?loc else CAst.make ?loc (TacArg a)

and intern_tactic_or_tacarg ist = intern_tactic false ist

and intern_pure_tactic ist = intern_tactic true ist

and intern_tactic_fun ist (var,body) =
  let lfun = List.fold_left name_cons ist.ltacvars var in
  (var,intern_tactic_or_tacarg { ist with ltacvars = lfun } body)

and intern_tacarg strict onlytac ist = function
  | Reference r -> intern_non_tactic_reference strict ist r
  | ConstrMayEval c -> ConstrMayEval (intern_constr_may_eval ist c)
  | TacCall { loc; v=(f,[]) } -> intern_isolated_tactic_reference strict ist f
  | TacCall { loc; v=(f,l) } ->
      TacCall (CAst.make ?loc (
        intern_applied_tactic_reference ist f,
        List.map (intern_tacarg ist.strict_check false ist) l))
  | TacFreshId x -> TacFreshId (List.map (intern_string_or_var ist) x)
  | TacPretype c -> TacPretype (intern_constr ist c)
  | TacNumgoals -> TacNumgoals
  | Tacexp t -> Tacexp (intern_tactic onlytac ist t)
  | TacGeneric (isquot,arg) ->
    let arg = intern_genarg ist arg in
    TacGeneric (isquot,arg)

(* Reads the rules of a Match Context or a Match *)
and intern_match_rule onlytac ist ?(as_type=false) = function
  | (All tc)::tl ->
      All (intern_tactic onlytac ist tc) :: (intern_match_rule onlytac ist ~as_type tl)
  | (Pat (rl,mp,tc))::tl ->
      let {ltacvars=lfun; genv=env} = ist in
      let lfun',metas1,hyps = intern_match_goal_hyps ist ~as_type lfun rl in
      let ido,metas2,pat = intern_pattern ist ~as_type lfun mp in
      let ltacvars = Id.Set.union (opt_cons lfun' ido) metas1 in
      let ltacvars = Id.Set.union ltacvars metas2 in
      let ist' = { ist with ltacvars } in
      Pat (hyps,pat,intern_tactic onlytac ist' tc) :: (intern_match_rule onlytac ist ~as_type tl)
  | [] -> []

and intern_genarg ist (GenArg (Rawwit wit, x)) =
  match wit with
  | ListArg wit ->
      let map x =
        let ans = intern_genarg ist (in_gen (rawwit wit) x) in
        out_gen (glbwit wit) ans
      in
      in_gen (glbwit (wit_list wit)) (List.map map x)
  | OptArg wit ->
      let ans = match x with
      | None -> in_gen (glbwit (wit_opt wit)) None
      | Some x ->
        let s = out_gen (glbwit wit) (intern_genarg ist (in_gen (rawwit wit) x)) in
        in_gen (glbwit (wit_opt wit)) (Some s)
      in
      ans
  | PairArg (wit1, wit2) ->
      let p, q = x in
      let p = out_gen (glbwit wit1) (intern_genarg ist (in_gen (rawwit wit1) p)) in
      let q = out_gen (glbwit wit2) (intern_genarg ist (in_gen (rawwit wit2) q)) in
      in_gen (glbwit (wit_pair wit1 wit2)) (p, q)
  | ExtraArg s ->
      snd (Genintern.generic_intern ist (in_gen (rawwit wit) x))

(** Other entry points *)

let glob_tactic x =
  intern_pure_tactic (make_empty_glob_sign ~strict:true) x

let glob_tactic_env l env x =
  let ltacvars =
    List.fold_left (fun accu x -> Id.Set.add x accu) Id.Set.empty l in
  intern_pure_tactic { (Genintern.empty_glob_sign ~strict:true env) with ltacvars } x

let intern_strategy ist s =
  let rec aux stratvars = function
    | Rewrite.StratVar x ->
      (* We could make this whole branch assert false, since it's
         unreachable except from plugins. But maybe it's useful if any
         plug-in wants to craft a strategy by hand. *)
      if Id.Set.mem x.v stratvars then Rewrite.StratVar x.v
      else CErrors.user_err ?loc:x.loc Pp.(str "Unbound strategy" ++ spc() ++ Id.print x.v)
    | StratConstr ({ v = CRef (qid, None) }, true) when idset_mem_qualid qid stratvars ->
      let (_, x) = repr_qualid qid in Rewrite.StratVar x
    | StratConstr (c, b) -> StratConstr (intern_constr ist c, b)
    | StratFix (x, s) -> StratFix (x.v, aux (Id.Set.add x.v stratvars) s)
    | StratId | StratFail | StratRefl as s -> s
    | StratUnary (s, str) -> StratUnary (s, aux stratvars str)
    | StratBinary (s, str, str') -> StratBinary (s, aux stratvars str, aux stratvars str')
    | StratNAry (s, strs) -> StratNAry (s, List.map (aux stratvars) strs)
    | StratTerms l -> StratTerms (List.map (intern_constr ist) l)
    | StratHints (b, id) -> StratHints (b, id)
    | StratEval r -> StratEval (intern_red_expr ist r)
    | StratFold c -> StratFold (intern_constr ist c)
  in
  aux Id.Set.empty s

(** Registering *)

let lift intern = (); fun ist x -> (ist, intern ist x)

let () =
  let intern_intro_pattern ist pat =
    let lf = ref Id.Set.empty in
    let ans = intern_intro_pattern lf ist pat in
    let ist = { ist with ltacvars = !lf } in
    (ist, ans)
  in
  Genintern.register_intern0 wit_intropattern intern_intro_pattern [@warning "-3"];
  Genintern.register_intern0 wit_simple_intropattern intern_intro_pattern

let () =
  let intern_clause ist cl =
    let ans = clause_app (intern_hyp_location ist) cl in
    (ist, ans)
  in
  Genintern.register_intern0 wit_clause_dft_concl intern_clause

let intern_ident' ist id =
  let lf = ref Id.Set.empty in
  (ist, intern_ident lf ist id)

let intern_ltac ist tac =
  intern_pure_tactic { ist with strict_check = true } tac

let () =
  Genintern.register_intern0 wit_int_or_var (lift intern_int_or_var);
  Genintern.register_intern0 wit_nat_or_var (lift intern_int_or_var);
  Genintern.register_intern0 wit_smart_global (lift intern_smart_global);
  Genintern.register_intern0 wit_ref (lift intern_global_reference);
  Genintern.register_intern0 wit_pre_ident (fun ist c -> (ist,c));
  Genintern.register_intern0 wit_ident intern_ident';
  Genintern.register_intern0 wit_hyp (lift intern_hyp);
  Genintern.register_intern0 wit_tactic (lift intern_tactic_or_tacarg);
  Genintern.register_intern0 wit_ltac (lift intern_ltac);
  Genintern.register_intern0 wit_quant_hyp (lift intern_quantified_hypothesis);
  Genintern.register_intern0 wit_constr (fun ist c -> (ist,intern_constr ist c));
  Genintern.register_intern0 wit_uconstr (fun ist c -> (ist,intern_constr ist c));
  Genintern.register_intern0 wit_open_constr (fun ist c -> (ist,intern_constr ist c));
  Genintern.register_intern0 Redexpr.wit_red_expr (lift intern_red_expr);
  Genintern.register_intern0 wit_bindings (lift intern_bindings);
  Genintern.register_intern0 wit_constr_with_bindings (lift intern_constr_with_bindings);
  Genintern.register_intern0 wit_destruction_arg (lift intern_destruction_arg);
  ()

(** Substitution for notations containing tactic-in-terms *)

let notation_subst _avoid bindings tac =
  let fold id c accu =
    let loc = Glob_ops.loc_of_glob_constr c in
    let c = ConstrMayEval (ConstrTerm (c, None)) in
    (make ?loc @@ Name id, c) :: accu
  in
  let bindings = Id.Map.fold fold bindings [] in
  (* This is theoretically not correct due to potential variable
     capture, but Ltac has no true variables so one cannot simply
     substitute *)
  if List.is_empty bindings then tac
  else CAst.make (TacLetIn (false, bindings, tac))

let () = Genintern.register_ntn_subst0 wit_tactic notation_subst
