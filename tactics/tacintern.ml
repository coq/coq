(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pattern
open Pp
open Genredexpr
open Glob_term
open Tacred
open Errors
open Util
open Names
open Nameops
open Libnames
open Globnames
open Nametab
open Smartlocate
open Constrexpr
open Termops
open Tacexpr
open Genarg
open Constrarg
open Misctypes
open Locus

(** Globalization of tactic expressions :
    Conversion from [raw_tactic_expr] to [glob_tactic_expr] *)

let dloc = Loc.ghost

let error_global_not_found_loc (loc,qid) =
  error_global_not_found_loc loc qid

let error_syntactic_metavariables_not_allowed loc =
  user_err_loc
    (loc,"out_ident",
     str "Syntactic metavariables allowed only in quotations.")

let error_tactic_expected loc =
  user_err_loc (loc,"",str "Tactic expected.")

(** Generic arguments *)

type glob_sign = Genintern.glob_sign = {
  ltacvars : Id.Set.t;
     (* ltac variables and the subset of vars introduced by Intro/Let/... *)
  ltacrecvars : ltac_constant Id.Map.t;
     (* ltac recursive names *)
  genv : Environ.env }

let fully_empty_glob_sign =
  { ltacvars = Id.Set.empty; ltacrecvars = Id.Map.empty; genv = Environ.empty_env }

let make_empty_glob_sign () =
  { fully_empty_glob_sign with genv = Global.env () }

(* We have identifier <| global_reference <| constr *)

let find_ident id ist =
  Id.Set.mem id ist.ltacvars ||
  Id.List.mem id (ids_of_named_context (Environ.named_context ist.genv))

let find_recvar qid ist = Id.Map.find qid ist.ltacrecvars

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

let strict_check = ref false

let adjust_loc loc = if !strict_check then dloc else loc

(* Globalize a name which must be bound -- actually just check it is bound *)
let intern_hyp ist (loc,id as locid) =
  if not !strict_check then
    locid
  else if find_ident id ist then
    (dloc,id)
  else
    Pretype_errors.error_var_not_found_loc loc id

let intern_or_var f ist = function
  | ArgVar locid -> ArgVar (intern_hyp ist locid)
  | ArgArg x -> ArgArg (f x)

let intern_int_or_var = intern_or_var (fun (n : int) -> n)
let intern_id_or_var = intern_or_var (fun (id : Id.t) -> id)
let intern_string_or_var = intern_or_var (fun (s : string) -> s)

let intern_global_reference ist = function
  | Ident (loc,id) when find_var id ist -> ArgVar (loc,id)
  | r ->
      let loc,_ as lqid = qualid_of_reference r in
      try ArgArg (loc,locate_global_with_alias lqid)
      with Not_found -> error_global_not_found_loc lqid

let intern_ltac_variable ist = function
  | Ident (loc,id) ->
      if find_var id ist then
	(* A local variable of any type *)
	ArgVar (loc,id)
      else
      (* A recursive variable *)
      ArgArg (loc,find_recvar id ist)
  | _ ->
      raise Not_found

let intern_constr_reference strict ist = function
  | Ident (_,id) as r when not strict && find_hyp id ist ->
      GVar (dloc,id), Some (CRef (r,None))
  | Ident (_,id) as r when find_var id ist ->
      GVar (dloc,id), if strict then None else Some (CRef (r,None))
  | r ->
      let loc,_ as lqid = qualid_of_reference r in
      GRef (loc,locate_global_with_alias lqid,None), 
	if strict then None else Some (CRef (r,None))

let intern_move_location ist = function
  | MoveAfter id -> MoveAfter (intern_hyp ist id)
  | MoveBefore id -> MoveBefore (intern_hyp ist id)
  | MoveFirst -> MoveFirst
  | MoveLast -> MoveLast

(* Internalize an isolated reference in position of tactic *)

let intern_isolated_global_tactic_reference r =
  let (loc,qid) = qualid_of_reference r in
  TacCall (loc,ArgArg (loc,locate_tactic qid),[])

let intern_isolated_tactic_reference strict ist r =
  (* An ltac reference *)
  try Reference (intern_ltac_variable ist r)
  with Not_found ->
  (* A global tactic *)
  try intern_isolated_global_tactic_reference r
  with Not_found ->
  (* Tolerance for compatibility, allow not to use "constr:" *)
  try ConstrMayEval (ConstrTerm (intern_constr_reference strict ist r))
  with Not_found ->
  (* Reference not found *)
  error_global_not_found_loc (qualid_of_reference r)

(* Internalize an applied tactic reference *)

let intern_applied_global_tactic_reference r =
  let (loc,qid) = qualid_of_reference r in
  ArgArg (loc,locate_tactic qid)

let intern_applied_tactic_reference ist r =
  (* An ltac reference *)
  try intern_ltac_variable ist r
  with Not_found ->
  (* A global tactic *)
  try intern_applied_global_tactic_reference r
  with Not_found ->
  (* Reference not found *)
  error_global_not_found_loc (qualid_of_reference r)

(* Intern a reference parsed in a non-tactic entry *)

let intern_non_tactic_reference strict ist r =
  (* An ltac reference *)
  try Reference (intern_ltac_variable ist r)
  with Not_found ->
  (* A constr reference *)
  try ConstrMayEval (ConstrTerm (intern_constr_reference strict ist r))
  with Not_found ->
  (* Tolerance for compatibility, allow not to use "ltac:" *)
  try intern_isolated_global_tactic_reference r
  with Not_found ->
  (* By convention, use IntroIdentifier for unbound ident, when not in a def *)
  match r with
  | Ident (loc,id) when not strict ->
    let ipat = in_gen (glbwit wit_intro_pattern) (loc, IntroNaming (IntroIdentifier id)) in
    TacGeneric ipat
  | _ ->
  (* Reference not found *)
  error_global_not_found_loc (qualid_of_reference r)

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

let intern_constr_gen allow_patvar isarity {ltacvars=lfun; genv=env} c =
  let warn = if !strict_check then fun x -> x else Constrintern.for_grammar in
  let scope = if isarity then Pretyping.IsType else Pretyping.WithoutTypeConstraint in
  let ltacvars = {
    Constrintern.ltac_vars = lfun;
    ltac_bound = Id.Set.empty;
  } in
  let c' =
    warn (Constrintern.intern_gen scope ~allow_patvar ~ltacvars env) c
  in
  (c',if !strict_check then None else Some c)

let intern_constr = intern_constr_gen false false
let intern_type = intern_constr_gen false true

(* Globalize bindings *)
let intern_binding ist (loc,b,c) =
  (loc,intern_binding_name ist b,intern_constr ist c)

let intern_bindings ist = function
  | NoBindings -> NoBindings
  | ImplicitBindings l -> ImplicitBindings (List.map (intern_constr ist) l)
  | ExplicitBindings l -> ExplicitBindings (List.map (intern_binding ist) l)

let intern_constr_with_bindings ist (c,bl) =
  (intern_constr ist c, intern_bindings ist bl)

let intern_constr_with_bindings_arg ist (clear,c) =
  (clear,intern_constr_with_bindings ist c)

let rec intern_intro_pattern lf ist = function
  | loc, IntroNaming pat ->
      loc, IntroNaming (intern_intro_pattern_naming lf ist pat)
  | loc, IntroAction pat ->
      loc, IntroAction (intern_intro_pattern_action lf ist pat)
  | loc, IntroForthcoming _ as x -> x

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
  | IntroApplyOn (c,pat) ->
      IntroApplyOn (intern_constr ist c, intern_intro_pattern lf ist pat)

and intern_or_and_intro_pattern lf ist =
  List.map (List.map (intern_intro_pattern lf ist))

let intern_or_and_intro_pattern_loc lf ist = function
  | ArgVar (_,id) as x ->
      if find_var id ist then x
      else error "Disjunctive/conjunctive introduction pattern expected."
  | ArgArg (loc,l) -> ArgArg (loc,intern_or_and_intro_pattern lf ist l)

let intern_intro_pattern_naming_loc lf ist (loc,pat) =
  (loc,intern_intro_pattern_naming lf ist pat)

  (* TODO: catch ltac vars *)
let intern_induction_arg ist = function
  | clear,ElimOnConstr c -> clear,ElimOnConstr (intern_constr_with_bindings ist c)
  | clear,ElimOnAnonHyp n as x -> x
  | clear,ElimOnIdent (loc,id) ->
      if !strict_check then
	(* If in a defined tactic, no intros-until *)
	match intern_constr ist (CRef (Ident (dloc,id), None)) with
	| GVar (loc,id),_ -> clear,ElimOnIdent (loc,id)
	| c -> clear,ElimOnConstr (c,NoBindings)
      else
	clear,ElimOnIdent (loc,id)

let short_name = function
  | AN (Ident (loc,id)) when not !strict_check -> Some (loc,id)
  | _ -> None

let intern_evaluable_global_reference ist r =
  let lqid = qualid_of_reference r in
  try evaluable_of_global_reference ist.genv (locate_global_with_alias ~head:true lqid)
  with Not_found ->
  match r with
  | Ident (loc,id) when not !strict_check -> EvalVarRef id
  | _ -> error_global_not_found_loc lqid

let intern_evaluable_reference_or_by_notation ist = function
  | AN r -> intern_evaluable_global_reference ist r
  | ByNotation (loc,ntn,sc) ->
      evaluable_of_global_reference ist.genv
      (Notation.interp_notation_as_global_reference loc
        (function ConstRef _ | VarRef _ -> true | _ -> false) ntn sc)

(* Globalize a reduction expression *)
let intern_evaluable ist = function
  | AN (Ident (loc,id)) when find_var id ist -> ArgVar (loc,id)
  | AN (Ident (loc,id)) when not !strict_check && find_hyp id ist ->
      ArgArg (EvalVarRef id, Some (loc,id))
  | r ->
      let e = intern_evaluable_reference_or_by_notation ist r in
      let na = short_name r in
      ArgArg (e,na)

let intern_unfold ist (l,qid) = (l,intern_evaluable ist qid)

let intern_flag ist red =
  { red with rConst = List.map (intern_evaluable ist) red.rConst }

let intern_constr_with_occurrences ist (l,c) = (l,intern_constr ist c)

let intern_constr_pattern ist ~as_type ~ltacvars pc =
  let ltacvars = {
    Constrintern.ltac_vars = ltacvars;
    ltac_bound = Id.Set.empty;
  } in
  let metas,pat = Constrintern.intern_constr_pattern
    ist.genv ~as_type ~ltacvars pc
  in
  let c = intern_constr_gen true false ist pc in
  metas,(c,pat)

let dummy_pat = PRel 0

let intern_typed_pattern ist p =
  (* we cannot ensure in non strict mode that the pattern is closed *)
  (* keeping a constr_expr copy is too complicated and we want anyway to *)
  (* type it, so we remember the pattern as a glob_constr only *)
  (intern_constr_gen true false ist p,dummy_pat)

let rec intern_typed_pattern_or_ref_with_occurrences ist (l,p) =
  let interp_ref r =
    try l, Inl (intern_evaluable ist r)
    with e when Logic.catchable_exception e ->
      (* Compatibility. In practice, this means that the code above
         is useless. Still the idea of having either an evaluable
         ref or a pattern seems interesting, with "head" reduction
         in case of an evaluable ref, and "strong" reduction in the
         subterm matched when a pattern *)
      let loc = loc_of_smart_reference r in
      let r = match r with
      | AN r -> r
      | _ -> Qualid (loc,qualid_of_path (path_of_global (smart_global r))) in
      let sign = { Constrintern.ltac_vars = ist.ltacvars; Constrintern.ltac_bound = Id.Set.empty } in
      let c = Constrintern.interp_reference sign r in
      match c with
      | GRef (_,r,None) ->
          l, Inl (ArgArg (evaluable_of_global_reference ist.genv r,None))
      | GVar (_,id) ->
          let r = evaluable_of_global_reference ist.genv (VarRef id) in
          l, Inl (ArgArg (r,None))
      | _ ->
          l, Inr ((c,None),dummy_pat) in
  match p with
  | Inl r -> interp_ref r
  | Inr (CAppExpl(_,(None,r,None),[])) ->
      (* We interpret similarly @ref and ref *)
      interp_ref (AN r)
  | Inr c ->
      l, Inr (intern_typed_pattern ist c)

(* This seems fairly hacky, but it's the first way I've found to get proper
   globalization of [unfold].  --adamc *)
let dump_glob_red_expr = function
  | Unfold occs -> List.iter (fun (_, r) ->
    try
      Dumpglob.add_glob (loc_of_or_by_notation Libnames.loc_of_reference r)
	(Smartlocate.smart_global r)
    with e when Errors.noncritical e -> ()) occs
  | Cbv grf | Lazy grf ->
    List.iter (fun r ->
      try
        Dumpglob.add_glob (loc_of_or_by_notation Libnames.loc_of_reference r)
	  (Smartlocate.smart_global r)
      with e when Errors.noncritical e -> ()) grf.rConst
  | _ -> ()

let intern_red_expr ist = function
  | Unfold l -> Unfold (List.map (intern_unfold ist) l)
  | Fold l -> Fold (List.map (intern_constr ist) l)
  | Cbv f -> Cbv (intern_flag ist f)
  | Cbn f -> Cbn (intern_flag ist f)
  | Lazy f -> Lazy (intern_flag ist f)
  | Pattern l -> Pattern (List.map (intern_constr_with_occurrences ist) l)
  | Simpl (f,o) ->
     Simpl (intern_flag ist f,
	    Option.map (intern_typed_pattern_or_ref_with_occurrences ist) o)
  | CbvVm o -> CbvVm (Option.map (intern_typed_pattern_or_ref_with_occurrences ist) o)
  | CbvNative o -> CbvNative (Option.map (intern_typed_pattern_or_ref_with_occurrences ist) o)
  | (Red _ | Hnf | ExtraRedExpr _ as r ) -> r

let intern_in_hyp_as ist lf (clear,id,ipat) =
  (clear,intern_hyp ist id, Option.map (intern_intro_pattern lf ist) ipat)

let intern_hyp_list ist = List.map (intern_hyp ist)

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
  | Subterm (b,ido,pc) ->
      let (metas,pc) = intern_constr_pattern ist ~as_type ~ltacvars pc in
      ido, metas, Subterm (b,ido,pc)
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
let rec intern_match_goal_hyps ist lfun = function
  | (Hyp ((_,na) as locna,mp))::tl ->
      let ido, metas1, pat = intern_pattern ist ~as_type:true lfun mp in
      let lfun, metas2, hyps = intern_match_goal_hyps ist lfun tl in
      let lfun' = name_cons (opt_cons lfun ido) na in
      lfun', metas1@metas2, Hyp (locna,pat)::hyps
  | (Def ((_,na) as locna,mv,mp))::tl ->
      let ido, metas1, patv = intern_pattern ist ~as_type:false lfun mv in
      let ido', metas2, patt = intern_pattern ist ~as_type:true lfun mp in
      let lfun, metas3, hyps = intern_match_goal_hyps ist lfun tl in
      let lfun' = name_cons (opt_cons (opt_cons lfun ido) ido') na in
      lfun', metas1@metas2@metas3, Def (locna,patv,patt)::hyps
  | [] -> lfun, [], []

(* Utilities *)
let extract_let_names lrc =
  let fold accu ((loc, name), _) =
    if Id.Set.mem name accu then user_err_loc
      (loc, "glob_tactic", str "This variable is bound several times.")
    else Id.Set.add name accu
  in
  List.fold_left fold Id.Set.empty lrc

let clause_app f = function
    { onhyps=None; concl_occs=nl } ->
      { onhyps=None; concl_occs=nl }
  | { onhyps=Some l; concl_occs=nl } ->
      { onhyps=Some(List.map f l); concl_occs=nl}

let map_raw wit f ist x =
  in_gen (glbwit wit) (f ist (out_gen (rawwit wit) x))

(* Globalizes tactics : raw_tactic_expr -> glob_tactic_expr *)
let rec intern_atomic lf ist x =
  match (x:raw_atomic_tactic_expr) with
  (* Basic tactics *)
  | TacIntroPattern l ->
      TacIntroPattern (List.map (intern_intro_pattern lf ist) l)
  | TacIntroMove (ido,hto) ->
      TacIntroMove (Option.map (intern_ident lf ist) ido,
                    intern_move_location ist hto)
  | TacExact c -> TacExact (intern_constr ist c)
  | TacApply (a,ev,cb,inhyp) ->
      TacApply (a,ev,List.map (intern_constr_with_bindings_arg ist) cb,
                Option.map (intern_in_hyp_as ist lf) inhyp)
  | TacElim (ev,cb,cbo) ->
      TacElim (ev,intern_constr_with_bindings_arg ist cb,
               Option.map (intern_constr_with_bindings ist) cbo)
  | TacCase (ev,cb) -> TacCase (ev,intern_constr_with_bindings_arg ist cb)
  | TacFix (idopt,n) -> TacFix (Option.map (intern_ident lf ist) idopt,n)
  | TacMutualFix (id,n,l) ->
      let f (id,n,c) = (intern_ident lf ist id,n,intern_type ist c) in
      TacMutualFix (intern_ident lf ist id, n, List.map f l)
  | TacCofix idopt -> TacCofix (Option.map (intern_ident lf ist) idopt)
  | TacMutualCofix (id,l) ->
      let f (id,c) = (intern_ident lf ist id,intern_type ist c) in
      TacMutualCofix (intern_ident lf ist id, List.map f l)
  | TacAssert (b,otac,ipat,c) ->
      TacAssert (b,Option.map (intern_pure_tactic ist) otac,
                 Option.map (intern_intro_pattern lf ist) ipat,
                 intern_constr_gen false (not (Option.is_empty otac)) ist c)
  | TacGeneralize cl ->
      TacGeneralize (List.map (fun (c,na) ->
	               intern_constr_with_occurrences ist c,
                       intern_name lf ist na) cl)
  | TacGeneralizeDep c -> TacGeneralizeDep (intern_constr ist c)
  | TacLetTac (na,c,cls,b,eqpat) ->
      let na = intern_name lf ist na in
      TacLetTac (na,intern_constr ist c,
                 (clause_app (intern_hyp_location ist) cls),b,
		 (Option.map (intern_intro_pattern_naming_loc lf ist) eqpat))

  (* Automation tactics *)
  | TacTrivial (d,lems,l) -> TacTrivial (d,List.map (intern_constr ist) lems,l)
  | TacAuto (d,n,lems,l) ->
      TacAuto (d,Option.map (intern_int_or_var ist) n,
        List.map (intern_constr ist) lems,l)

  (* Derived basic tactics *)
  | TacInductionDestruct (ev,isrec,(l,el)) ->
      TacInductionDestruct (ev,isrec,(List.map (fun (c,(ipato,ipats),cls) ->
	      (intern_induction_arg ist c,
               (Option.map (intern_intro_pattern_naming_loc lf ist) ipato,
               Option.map (intern_or_and_intro_pattern_loc lf ist) ipats),
               Option.map (clause_app (intern_hyp_location ist)) cls)) l,
               Option.map (intern_constr_with_bindings ist) el))
  | TacDoubleInduction (h1,h2) ->
      let h1 = intern_quantified_hypothesis ist h1 in
      let h2 = intern_quantified_hypothesis ist h2 in
      TacDoubleInduction (h1,h2)
  (* Context management *)
  | TacClear (b,l) -> TacClear (b,List.map (intern_hyp ist) l)
  | TacClearBody l -> TacClearBody (List.map (intern_hyp ist) l)
  | TacMove (id1,id2) ->
    TacMove (intern_hyp ist id1,intern_move_location ist id2)
  | TacRename l ->
      TacRename (List.map (fun (id1,id2) ->
			     intern_hyp ist id1,
			     intern_hyp ist id2) l)

  (* Constructors *)
  | TacSplit (ev,bll) -> TacSplit (ev,List.map (intern_bindings ist) bll)

  (* Conversion *)
  | TacReduce (r,cl) ->
      dump_glob_red_expr r;
      TacReduce (intern_red_expr ist r, clause_app (intern_hyp_location ist) cl)
  | TacChange (None,c,cl) ->
      let is_onhyps = match cl.onhyps with
      | None | Some [] -> true
      | _ -> false
      in
      let is_onconcl = match cl.concl_occs with
      | AllOccurrences | NoOccurrences -> true
      | _ -> false
      in
      TacChange (None,
        (if is_onhyps && is_onconcl
         then intern_type ist c else intern_constr ist c),
	clause_app (intern_hyp_location ist) cl)
  | TacChange (Some p,c,cl) ->
      TacChange (Some (intern_typed_pattern ist p),intern_constr ist c,
	clause_app (intern_hyp_location ist) cl)

  (* Equivalence relations *)
  | TacSymmetry idopt ->
      TacSymmetry (clause_app (intern_hyp_location ist) idopt)

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

and intern_tactic_seq onlytac ist = function
  | TacAtom (loc,t) ->
      let lf = ref ist.ltacvars in
      let t = intern_atomic lf ist t in
      !lf, TacAtom (adjust_loc loc, t)
  | TacFun tacfun -> ist.ltacvars, TacFun (intern_tactic_fun ist tacfun)
  | TacLetIn (isrec,l,u) ->
      let ltacvars = Id.Set.union (extract_let_names l) ist.ltacvars in
      let ist' = { ist with ltacvars } in
      let l = List.map (fun (n,b) ->
	  (n,intern_tacarg !strict_check false (if isrec then ist' else ist) b)) l in
      ist.ltacvars, TacLetIn (isrec,l,intern_tactic onlytac ist' u)

  | TacMatchGoal (lz,lr,lmr) ->
      ist.ltacvars, TacMatchGoal(lz,lr, intern_match_rule onlytac ist lmr)
  | TacMatch (lz,c,lmr) ->
      ist.ltacvars,
      TacMatch (lz,intern_tactic_or_tacarg ist c,intern_match_rule onlytac ist lmr)
  | TacId l -> ist.ltacvars, TacId (intern_message ist l)
  | TacFail (g,n,l) ->
      ist.ltacvars, TacFail (g,intern_int_or_var ist n,intern_message ist l)
  | TacProgress tac -> ist.ltacvars, TacProgress (intern_pure_tactic ist tac)
  | TacShowHyps tac -> ist.ltacvars, TacShowHyps (intern_pure_tactic ist tac)
  | TacAbstract (tac,s) ->
      ist.ltacvars, TacAbstract (intern_pure_tactic ist tac,s)
  | TacThen (t1,t2) ->
      let lfun', t1 = intern_tactic_seq onlytac ist t1 in
      let lfun'', t2 = intern_tactic_seq onlytac { ist with ltacvars = lfun' } t2 in
      lfun'', TacThen (t1,t2)
  | TacDispatch tl ->
      ist.ltacvars , TacDispatch (List.map (intern_pure_tactic ist) tl)
  | TacExtendTac (tf,t,tl) ->
      ist.ltacvars ,
      TacExtendTac (Array.map (intern_pure_tactic ist) tf,
                    intern_pure_tactic ist t,
		    Array.map (intern_pure_tactic ist) tl)
  | TacThens3parts (t1,tf,t2,tl) ->
      let lfun', t1 = intern_tactic_seq onlytac ist t1 in
      let ist' = { ist with ltacvars = lfun' } in
      (* Que faire en cas de (tac complexe avec Match et Thens; tac2) ?? *)
      lfun', TacThens3parts (t1,Array.map (intern_pure_tactic ist') tf,intern_pure_tactic ist' t2,
		       Array.map (intern_pure_tactic ist') tl)
  | TacThens (t,tl) ->
      let lfun', t = intern_tactic_seq true ist t in
      let ist' = { ist with ltacvars = lfun' } in
      (* Que faire en cas de (tac complexe avec Match et Thens; tac2) ?? *)
      lfun', TacThens (t, List.map (intern_pure_tactic ist') tl)
  | TacDo (n,tac) ->
      ist.ltacvars, TacDo (intern_int_or_var ist n,intern_pure_tactic ist tac)
  | TacTry tac -> ist.ltacvars, TacTry (intern_pure_tactic ist tac)
  | TacInfo tac -> ist.ltacvars, TacInfo (intern_pure_tactic ist tac)
  | TacRepeat tac -> ist.ltacvars, TacRepeat (intern_pure_tactic ist tac)
  | TacTimeout (n,tac) ->
      ist.ltacvars, TacTimeout (intern_int_or_var ist n,intern_tactic onlytac ist tac)
  | TacTime (s,tac) ->
      ist.ltacvars, TacTime (s,intern_tactic onlytac ist tac)
  | TacOr (tac1,tac2) ->
      ist.ltacvars, TacOr (intern_pure_tactic ist tac1,intern_pure_tactic ist tac2)
  | TacOnce tac ->
      ist.ltacvars, TacOnce (intern_pure_tactic ist tac)
  | TacExactlyOnce tac ->
      ist.ltacvars, TacExactlyOnce (intern_pure_tactic ist tac)
  | TacIfThenCatch (tac,tact,tace) ->
      ist.ltacvars,
      TacIfThenCatch (
        intern_pure_tactic ist tac,
        intern_pure_tactic ist tact,
        intern_pure_tactic ist tace)
  | TacOrelse (tac1,tac2) ->
      ist.ltacvars, TacOrelse (intern_pure_tactic ist tac1,intern_pure_tactic ist tac2)
  | TacFirst l -> ist.ltacvars, TacFirst (List.map (intern_pure_tactic ist) l)
  | TacSolve l -> ist.ltacvars, TacSolve (List.map (intern_pure_tactic ist) l)
  | TacComplete tac -> ist.ltacvars, TacComplete (intern_pure_tactic ist tac)
  | TacArg (loc,a) -> ist.ltacvars, intern_tactic_as_arg loc onlytac ist a

  (* For extensions *)
  | TacAlias (loc,s,l) ->
      let l = List.map (fun (id,a) -> (id,intern_genarg ist a)) l in
      ist.ltacvars, TacAlias (loc,s,l)
  | TacML (loc,opn,l) ->
      let _ignore = Tacenv.interp_ml_tactic opn in
      ist.ltacvars, TacML (adjust_loc loc,opn,List.map (intern_genarg ist) l)

and intern_tactic_as_arg loc onlytac ist a =
  match intern_tacarg !strict_check onlytac ist a with
  | TacCall _ | Reference _
  | TacDynamic _ | TacGeneric _ as a -> TacArg (loc,a)
  | Tacexp a -> a
  | ConstrMayEval _ | UConstr _ | TacFreshId _ | TacPretype _ | TacNumgoals as a ->
      if onlytac then error_tactic_expected loc else TacArg (loc,a)
  | MetaIdArg _ -> assert false

and intern_tactic_or_tacarg ist = intern_tactic false ist

and intern_pure_tactic ist = intern_tactic true ist

and intern_tactic_fun ist (var,body) =
  let lfun = List.fold_left opt_cons ist.ltacvars var in
  (var,intern_tactic_or_tacarg { ist with ltacvars = lfun } body)

and intern_tacarg strict onlytac ist = function
  | Reference r -> intern_non_tactic_reference strict ist r
  | ConstrMayEval c -> ConstrMayEval (intern_constr_may_eval ist c)
  | UConstr c -> UConstr (intern_constr ist c)
  | MetaIdArg (loc,istac,s) ->
      (* $id can occur in Grammar tactic... *)
      let id = Id.of_string s in
      if find_var id ist then
	if istac then Reference (ArgVar (adjust_loc loc,id))
	else ConstrMayEval (ConstrTerm (GVar (adjust_loc loc,id), None))
      else error_syntactic_metavariables_not_allowed loc
  | TacCall (loc,f,[]) -> intern_isolated_tactic_reference strict ist f
  | TacCall (loc,f,l) ->
      TacCall (loc,
        intern_applied_tactic_reference ist f,
        List.map (intern_tacarg !strict_check false ist) l)
  | TacFreshId x -> TacFreshId (List.map (intern_string_or_var ist) x)
  | TacPretype c -> TacPretype (intern_constr ist c)
  | TacNumgoals -> TacNumgoals
  | Tacexp t -> Tacexp (intern_tactic onlytac ist t)
  | TacGeneric arg ->
    let (_, arg) = Genintern.generic_intern ist arg in
    TacGeneric arg
  | TacDynamic(loc,t) as x ->
    if Dyn.has_tag t "tactic" || Dyn.has_tag t "value" then x
    else if Dyn.has_tag t "constr" then
      if onlytac then error_tactic_expected loc else x
    else
      let tag = Dyn.tag t in
      anomaly ~loc (str "Unknown dynamic: <" ++ str tag ++ str ">")

(* Reads the rules of a Match Context or a Match *)
and intern_match_rule onlytac ist = function
  | (All tc)::tl ->
      All (intern_tactic onlytac ist tc) :: (intern_match_rule onlytac ist tl)
  | (Pat (rl,mp,tc))::tl ->
      let {ltacvars=lfun; genv=env} = ist in
      let lfun',metas1,hyps = intern_match_goal_hyps ist lfun rl in
      let ido,metas2,pat = intern_pattern ist lfun mp in
      let fold accu x = Id.Set.add x accu in
      let ltacvars = List.fold_left fold (opt_cons lfun' ido) metas1 in
      let ltacvars = List.fold_left fold ltacvars metas2 in
      let ist' = { ist with ltacvars } in
      Pat (hyps,pat,intern_tactic onlytac ist' tc) :: (intern_match_rule onlytac ist tl)
  | [] -> []

and intern_genarg ist x =
  match genarg_tag x with
  | IntOrVarArgType -> map_raw wit_int_or_var intern_int_or_var ist x
  | IdentArgType ->
    let lf = ref Id.Set.empty in
    map_raw wit_ident (intern_ident lf) ist x
  | VarArgType ->
    map_raw wit_var intern_hyp ist x
  | GenArgType ->
    map_raw wit_genarg intern_genarg ist x
  | ConstrArgType ->
    map_raw wit_constr intern_constr ist x
  | ConstrMayEvalArgType ->
    map_raw wit_constr_may_eval intern_constr_may_eval ist x
  | QuantHypArgType ->
    map_raw wit_quant_hyp intern_quantified_hypothesis ist x
  | RedExprArgType ->
    map_raw wit_red_expr intern_red_expr ist x
  | OpenConstrArgType ->
    map_raw wit_open_constr (fun ist -> on_snd (intern_constr ist)) ist x
  | ConstrWithBindingsArgType ->
    map_raw wit_constr_with_bindings intern_constr_with_bindings ist x
  | BindingsArgType ->
    map_raw wit_bindings intern_bindings ist x
  | ListArgType _ ->
      let list_unpacker wit l =
        let map x =
          let ans = intern_genarg ist (in_gen (rawwit wit) x) in
          out_gen (glbwit wit) ans
        in
        in_gen (glbwit (wit_list wit)) (List.map map (raw l))
      in
      list_unpack { list_unpacker } x
  | OptArgType _ ->
      let opt_unpacker wit o = match raw o with
      | None -> in_gen (glbwit (wit_opt wit)) None
      | Some x ->
        let s = out_gen (glbwit wit) (intern_genarg ist (in_gen (rawwit wit) x)) in
        in_gen (glbwit (wit_opt wit)) (Some s)
      in
      opt_unpack { opt_unpacker } x
  | PairArgType _ ->
      let pair_unpacker wit1 wit2 o =
        let p, q = raw o in
        let p = out_gen (glbwit wit1) (intern_genarg ist (in_gen (rawwit wit1) p)) in
        let q = out_gen (glbwit wit2) (intern_genarg ist (in_gen (rawwit wit2) q)) in
        in_gen (glbwit (wit_pair wit1 wit2)) (p, q)
      in
      pair_unpack { pair_unpacker } x
  | ExtraArgType s ->
      snd (Genintern.generic_intern ist x)

(** Other entry points *)

let glob_tactic x =
  Flags.with_option strict_check
    (intern_pure_tactic (make_empty_glob_sign ())) x

let glob_tactic_env l env x =
  let ltacvars =
    List.fold_left (fun accu x -> Id.Set.add x accu) Id.Set.empty l in
  Flags.with_option strict_check
  (intern_pure_tactic
    { ltacvars; ltacrecvars = Id.Map.empty; genv = env })
    x

let split_ltac_fun = function
  | TacFun (l,t) -> (l,t)
  | t -> ([],t)

let pr_ltac_fun_arg = function
  | None -> spc () ++ str "_"
  | Some id -> spc () ++ pr_id id

let print_ltac id =
 try
  let kn = Nametab.locate_tactic id in
  let l,t = split_ltac_fun (Tacenv.interp_ltac kn) in
  hv 2 (
    hov 2 (str "Ltac" ++ spc() ++ pr_qualid id ++
           prlist pr_ltac_fun_arg l ++ spc () ++ str ":=")
    ++ spc() ++ Pptactic.pr_glob_tactic (Global.env ()) t)
 with
  Not_found ->
   errorlabstrm "print_ltac"
    (pr_qualid id ++ spc() ++ str "is not a user defined tactic.")

(** Registering *)

let lift intern = (); fun ist x -> (ist, intern ist x)

let () =
  let intern_intro_pattern ist pat =
    let lf = ref Id.Set.empty in
    let ans = intern_intro_pattern lf ist pat in
    let ist = { ist with ltacvars = !lf } in
    (ist, ans)
  in
  Genintern.register_intern0 wit_intro_pattern intern_intro_pattern

let () =
  let intern_clause ist cl =
    let ans = clause_app (intern_hyp_location ist) cl in
    (ist, ans)
  in
  Genintern.register_intern0 wit_clause_dft_concl intern_clause

let () =
  Genintern.register_intern0 wit_ref (lift intern_global_reference);
  Genintern.register_intern0 wit_tactic (lift intern_tactic_or_tacarg);
  Genintern.register_intern0 wit_sort (fun ist s -> (ist, s))

let () =
  Genintern.register_intern0 wit_uconstr (fun ist c -> (ist,intern_constr ist c))

(***************************************************************************)
(* Backwarding recursive needs of tactic glob/interp/eval functions *)

let _ =
  let f l =
    let ltacvars =
      List.fold_left (fun accu x -> Id.Set.add x accu) Id.Set.empty l
    in
    Flags.with_option strict_check
    (intern_pure_tactic { (make_empty_glob_sign()) with ltacvars })
  in
  Hook.set Hints.extern_intern_tac f
