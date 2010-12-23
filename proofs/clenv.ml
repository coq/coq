(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Namegen
open Sign
open Environ
open Evd
open Reduction
open Reductionops
open Glob_term
open Pattern
open Tacred
open Pretype_errors
open Evarutil
open Unification
open Mod_subst
open Coercion.Default

(* Abbreviations *)

let pf_env = Refiner.pf_env
let pf_type_of gls c  = Typing.type_of (pf_env gls) gls.sigma c

(******************************************************************)
(* Clausal environments *)

type clausenv = {
  env      : env;
  evd      : evar_map;
  templval : constr freelisted;
  templtyp : constr freelisted }

let cl_env ce = ce.env
let cl_sigma ce =  ce.evd

let subst_clenv sub clenv =
  { templval = map_fl (subst_mps sub) clenv.templval;
    templtyp = map_fl (subst_mps sub) clenv.templtyp;
    evd = subst_evar_defs_light sub clenv.evd;
    env = clenv.env }

let clenv_nf_meta clenv c = nf_meta clenv.evd c
let clenv_term clenv c = meta_instance clenv.evd c
let clenv_meta_type clenv mv = Typing.meta_type clenv.evd mv
let clenv_value clenv = meta_instance clenv.evd clenv.templval
let clenv_type clenv = meta_instance clenv.evd clenv.templtyp


let clenv_hnf_constr ce t = hnf_constr (cl_env ce) (cl_sigma ce) t

let clenv_get_type_of ce c = Retyping.get_type_of (cl_env ce) (cl_sigma ce) c

exception NotExtensibleClause

let clenv_push_prod cl =
  let typ = whd_betadeltaiota (cl_env cl) (cl_sigma cl) (clenv_type cl) in
  let rec clrec typ = match kind_of_term typ with
    | Cast (t,_,_) -> clrec t
    | Prod (na,t,u) ->
	let mv = new_meta () in
	let dep = dependent (mkRel 1) u in
	let na' = if dep then na else Anonymous in
	let e' = meta_declare mv t ~name:na' cl.evd in
	let concl = if dep then subst1 (mkMeta mv) u else u in
	let def = applist (cl.templval.rebus,[mkMeta mv]) in
	{ templval = mk_freelisted def;
	  templtyp = mk_freelisted concl;
	  evd = e';
	  env = cl.env }
    | _ -> raise NotExtensibleClause
  in clrec typ

(* Instantiate the first [bound] products of [t] with metas (all products if
   [bound] is [None]; unfold local defs *)

let clenv_environments evd bound t =
  let rec clrec (e,metas) n t =
    match n, kind_of_term t with
      | (Some 0, _) -> (e, List.rev metas, t)
      | (n, Cast (t,_,_)) -> clrec (e,metas) n t
      | (n, Prod (na,t1,t2)) ->
	  let mv = new_meta () in
	  let dep = dependent (mkRel 1) t2 in
	  let na' = if dep then na else Anonymous in
	  let e' = meta_declare mv t1 ~name:na' e in
	  clrec (e', (mkMeta mv)::metas) (Option.map ((+) (-1)) n)
	    (if dep then (subst1 (mkMeta mv) t2) else t2)
      | (n, LetIn (na,b,_,t)) -> clrec (e,metas) n (subst1 b t)
      | (n, _) -> (e, List.rev metas, t)
  in
  clrec (evd,[]) bound t

(* Instantiate the first [bound] products of [t] with evars (all products if
   [bound] is [None]; unfold local defs *)

let clenv_environments_evars env evd bound t =
  let rec clrec (e,ts) n t =
    match n, kind_of_term t with
      | (Some 0, _) -> (e, List.rev ts, t)
      | (n, Cast (t,_,_)) -> clrec (e,ts) n t
      | (n, Prod (na,t1,t2)) ->
          let e',constr = Evarutil.new_evar e env t1 in
	  let dep = dependent (mkRel 1) t2 in
	  clrec (e', constr::ts) (Option.map ((+) (-1)) n)
	    (if dep then (subst1 constr t2) else t2)
      | (n, LetIn (na,b,_,t)) -> clrec (e,ts) n (subst1 b t)
      | (n, _) -> (e, List.rev ts, t)
  in
  clrec (evd,[]) bound t

let clenv_conv_leq env sigma t c bound =
  let ty = Retyping.get_type_of env sigma c in
  let evd = Evd.create_goal_evar_defs sigma in
  let evars,args,_ = clenv_environments_evars env evd (Some bound) ty in
  let evars = Evarconv.the_conv_x_leq env t (applist (c,args)) evars in
  let evars = Evarconv.consider_remaining_unif_problems env evars in
  let args = List.map (whd_evar evars) args in
  check_evars env sigma evars (applist (c,args));
  args

let mk_clenv_from_env environ sigma n (c,cty) =
  let evd = create_goal_evar_defs sigma in
  let (evd,args,concl) = clenv_environments evd n cty in
  { templval = mk_freelisted (match args with [] -> c | _ -> applist (c,args));
    templtyp = mk_freelisted concl;
    evd = evd;
    env = environ }

let mk_clenv_from_n gls n (c,cty) =
  mk_clenv_from_env (pf_env gls) gls.sigma n (c, cty)

let mk_clenv_from gls = mk_clenv_from_n gls None

let mk_clenv_type_of gls t = mk_clenv_from gls (t,pf_type_of gls t)

(******************************************************************)

(* [mentions clenv mv0 mv1] is true if mv1 is defined and mentions
 * mv0, or if one of the free vars on mv1's freelist mentions
 * mv0 *)

let mentions clenv mv0 =
  let rec menrec mv1 =
    mv0 = mv1 ||
    let mlist =
      try match meta_opt_fvalue clenv.evd mv1 with
      | Some (b,_) -> b.freemetas
      | None -> Metaset.empty
      with Not_found -> Metaset.empty in
    meta_exists menrec mlist
  in menrec

let error_incompatible_inst clenv mv  =
  let na = meta_name clenv.evd mv in
  match na with
      Name id ->
        errorlabstrm "clenv_assign"
          (str "An incompatible instantiation has already been found for " ++
           pr_id id)
    | _ ->
        anomaly "clenv_assign: non dependent metavar already assigned"

(* TODO: replace by clenv_unify (mkMeta mv) rhs ? *)
let clenv_assign mv rhs clenv =
  let rhs_fls = mk_freelisted rhs in
  if meta_exists (mentions clenv mv) rhs_fls.freemetas then
    error "clenv_assign: circularity in unification";
  try
    if meta_defined clenv.evd mv then
      if not (eq_constr (fst (meta_fvalue clenv.evd mv)).rebus rhs) then
        error_incompatible_inst clenv mv
      else
	clenv
    else
      let st = (ConvUpToEta 0,TypeNotProcessed) in
      {clenv with evd = meta_assign mv (rhs_fls.rebus,st) clenv.evd}
  with Not_found ->
    error "clenv_assign: undefined meta"



(* [clenv_dependent hyps_only clenv]
 * returns a list of the metavars which appear in the template of clenv,
 * and which are dependent, This is computed by taking the metavars of the
 * template in right-to-left order, and collecting the metavars which appear
 * in their types, and adding in all the metavars appearing in the
 * type of clenv.
 * If [hyps_only] then metavariables occurring in the concl are _excluded_
 * If [iter] is also set then all metavariables *recursively* occurring
 * in the concl are _excluded_

   Details of the strategies used for computing the set of unresolved
   dependent metavariables

   We typically have a clause of the form

   lem(?T:Type,?T,?U:Type,?V:Type,?x:?T,?y:?U,?z:?V,?H:hyp(?x,?z)) :concl(?y,?z)

   Then, we compute:
   A  = the set of all unresolved metas
   C  = the set of metas occurring in concl (here ?y, ?z)
   C* = the recursive closure of C wrt types (here ?y, ?z, ?U, ?V)
   D  = the set of metas occurring in a type of meta (here ?x, ?T, ?z, ?U, ?V)
   NL = the set of duplicated metas even if non dependent (here ?T)
       (we make the assumption that duplicated metas have internal dependencies)

   Then, for the "apply"-style tactic (hyps_only), missing metas are
     A inter ((D minus C) union NL)

   for the optimized "apply"-style tactic (taking in care, f_equal style
   lemma, from 2/8/10, Coq > 8.3), missing metas are
     A inter (( D minus C* ) union NL)

   for the "elim"-style tactic, missing metas are
     A inter (D union C union NL)

   In any case, we respect the order given in A.
*)

let clenv_metas_in_type_of_meta evd mv =
  (mk_freelisted (meta_instance evd (meta_ftype evd mv))).freemetas

let dependent_in_type_of_metas clenv mvs =
  List.fold_right
    (fun mv -> Metaset.union (clenv_metas_in_type_of_meta clenv.evd mv))
    mvs Metaset.empty

let dependent_closure clenv mvs =
  let rec aux mvs acc =
    Metaset.fold
      (fun mv deps ->
	let metas_of_meta_type = clenv_metas_in_type_of_meta clenv.evd mv in
	aux metas_of_meta_type (Metaset.union deps metas_of_meta_type))
      mvs acc in
  aux mvs mvs

let duplicated_metas c =
  let rec collrec (one,more as acc) c =
    match kind_of_term c with
    | Meta mv -> if List.mem mv one then (one,mv::more) else (mv::one,more)
    | _       -> fold_constr collrec acc c
  in
  snd (collrec ([],[]) c)

let clenv_dependent_gen hyps_only ?(iter=true) clenv =
  let all_undefined = undefined_metas clenv.evd in
  let deps_in_concl = (mk_freelisted (clenv_type clenv)).freemetas in
  let deps_in_hyps = dependent_in_type_of_metas clenv all_undefined in
  let non_linear = duplicated_metas (clenv_value clenv) in
  let deps_in_concl =
    if hyps_only && iter then dependent_closure clenv deps_in_concl
    else deps_in_concl in
  List.filter
    (fun mv ->
      Metaset.mem mv deps_in_hyps &&
	not (hyps_only && Metaset.mem mv deps_in_concl)
      || not hyps_only && Metaset.mem mv deps_in_concl
      || List.mem mv non_linear)
    all_undefined

let clenv_missing ce = clenv_dependent_gen true ce
let clenv_dependent ce = clenv_dependent_gen false ce

(******************************************************************)

let clenv_unify allow_K ?(flags=default_unify_flags) cv_pb t1 t2 clenv =
  { clenv with
      evd = w_unify allow_K ~flags:flags clenv.env cv_pb t1 t2 clenv.evd }

let clenv_unify_meta_types ?(flags=default_unify_flags) clenv =
  { clenv with evd = w_unify_meta_types ~flags:flags clenv.env clenv.evd }

let clenv_unique_resolver allow_K ?(flags=default_unify_flags) clenv gl =
  let concl = Goal.V82.concl clenv.evd (sig_it gl) in
  if isMeta (fst (whd_stack clenv.evd clenv.templtyp.rebus)) then
    clenv_unify allow_K CUMUL ~flags:flags (clenv_type clenv) concl
      (clenv_unify_meta_types ~flags:flags clenv)
  else
    clenv_unify allow_K CUMUL ~flags:flags
      (meta_reducible_instance clenv.evd clenv.templtyp) concl clenv

(* [clenv_pose_metas_as_evars clenv dep_mvs]
 * For each dependent evar in the clause-env which does not have a value,
 * pose a value for it by constructing a fresh evar.  We do this in
 * left-to-right order, so that every evar's type is always closed w.r.t.
 * metas.

 * Node added 14/4/08 [HH]: before this date, evars were collected in
   clenv_dependent by collect_metas in the fold_constr order which is
   (almost) the left-to-right order of dependencies in term. However,
   due to K-redexes, collect_metas was sometimes missing some metas.
   The call to collect_metas has been replaced by a call to
   undefined_metas, but then the order was the one of definition of
   the metas (numbers in increasing order) which is _not_ the
   dependency order when a clenv_fchain occurs (because clenv_fchain
   plugs a term with a list of consecutive metas in place of a - a priori -
   arbitrary metavariable belonging to another sequence of consecutive metas:
   e.g., clenv_fchain may plug (H ?1 ?2) at the position ?6 of
   (nat_ind ?3 ?4 ?5 ?6), leading to a dependency order 3<4<5<1<2).
   To ensure the dependency order, we check that the type of each meta
   to pose is already meta-free, otherwise we postpone the transformation,
   hoping that no cycle may happen.

   Another approach could have been to use decimal numbers for metas so that
   in the example above, (H ?1 ?2) would have been renumbered (H ?6.1 ?6.2)
   then making the numeric order match the dependency order.
*)

let clenv_pose_metas_as_evars clenv dep_mvs =
  let rec fold clenv = function
  | [] -> clenv
  | mv::mvs ->
      let ty = clenv_meta_type clenv mv in
      (* Postpone the evar-ization if dependent on another meta *)
      (* This assumes no cycle in the dependencies - is it correct ? *)
      if occur_meta ty then fold clenv (mvs@[mv])
      else
	let (evd,evar) =
	  new_evar clenv.evd (cl_env clenv) ~src:(dummy_loc,GoalEvar) ty in
	let clenv = clenv_assign mv evar {clenv with evd=evd} in
	fold clenv mvs in
  fold clenv dep_mvs

let evar_clenv_unique_resolver = clenv_unique_resolver

(******************************************************************)

let connect_clenv gls clenv =
  let evd = evars_reset_evd gls.sigma clenv.evd in
  { clenv with
    evd = evd ;
    env = Goal.V82.env evd (sig_it gls) }

(* [clenv_fchain mv clenv clenv']
 *
 * Resolves the value of "mv" (which must be undefined) in clenv to be
 * the template of clenv' be the value "c", applied to "n" fresh
 * metavars, whose types are chosen by destructing "clf", which should
 * be a clausale forme generated from the type of "c".  The process of
 * resolution can cause unification of already-existing metavars, and
 * of the fresh ones which get created.  This operation is a composite
 * of operations which pose new metavars, perform unification on
 * terms, and make bindings.

   Otherwise said, from

     [clenv] = [env;sigma;metas |- c:T]
     [clenv'] = [env';sigma';metas' |- d:U]
     [mv] = [mi] of type [Ti] in [metas]

   then, if the unification of [Ti] and [U] produces map [rho], the
   chaining is [env';sigma';rho'(metas),rho(metas') |- c:rho'(T)] for
   [rho'] being [rho;mi:=d].

   In particular, it assumes that [env'] and [sigma'] extend [env] and [sigma].
*)
let clenv_fchain ?(allow_K=true) ?(flags=default_unify_flags) mv clenv nextclenv =
  (* Add the metavars of [nextclenv] to [clenv], with their name-environment *)
  let clenv' =
    { templval = clenv.templval;
      templtyp = clenv.templtyp;
      evd = meta_merge nextclenv.evd clenv.evd;
      env = nextclenv.env } in
  (* unify the type of the template of [nextclenv] with the type of [mv] *)
  let clenv'' =
    clenv_unify allow_K ~flags:flags CUMUL
      (clenv_term clenv' nextclenv.templtyp)
      (clenv_meta_type clenv' mv)
      clenv' in
  (* assign the metavar *)
  let clenv''' =
    clenv_assign mv (clenv_term clenv' nextclenv.templval) clenv''
  in
  clenv'''

(***************************************************************)
(* Bindings *)

type arg_bindings = constr explicit_bindings

(* [clenv_independent clenv]
 * returns a list of metavariables which appear in the term cval,
 * and which are not dependent.  That is, they do not appear in
 * the types of other metavars which are in cval, nor in the type
 * of cval, ctyp. *)

let clenv_independent clenv =
  let mvs = collect_metas (clenv_value clenv) in
  let ctyp_mvs = (mk_freelisted (clenv_type clenv)).freemetas in
  let deps = Metaset.union (dependent_in_type_of_metas clenv mvs) ctyp_mvs in
  List.filter (fun mv -> not (Metaset.mem mv deps)) mvs

let check_bindings bl =
  match list_duplicates (List.map pi2 bl) with
    | NamedHyp s :: _ ->
	errorlabstrm ""
	  (str "The variable " ++ pr_id s ++
	   str " occurs more than once in binding list.");
    | AnonHyp n :: _ ->
	errorlabstrm ""
	  (str "The position " ++ int n ++
	   str " occurs more than once in binding list.")
    | [] -> ()

let meta_of_binder clause loc mvs = function
  | NamedHyp s -> meta_with_name clause.evd s
  | AnonHyp n ->
      try List.nth mvs (n-1)
      with (Failure _|Invalid_argument _) ->
        errorlabstrm "" (str "No such binder.")

let error_already_defined b =
  match b with
    | NamedHyp id ->
        errorlabstrm ""
          (str "Binder name \"" ++ pr_id id ++
           str"\" already defined with incompatible value.")
    | AnonHyp n ->
        anomalylabstrm ""
          (str "Position " ++ int n ++ str" already defined.")

let clenv_unify_binding_type clenv c t u =
  if isMeta (fst (whd_stack clenv.evd u)) then
    (* Not enough information to know if some subtyping is needed *)
    CoerceToType, clenv, c
  else
    (* Enough information so as to try a coercion now *)
    try
      let evd,c = w_coerce_to_type (cl_env clenv) clenv.evd c t u in
      TypeProcessed, { clenv with evd = evd }, c
    with 
      | PretypeError (_,_,NotClean _) as e -> raise e
      | e when precatchable_exception e ->
	  TypeNotProcessed, clenv, c

let clenv_assign_binding clenv k c =
  let k_typ = clenv_hnf_constr clenv (clenv_meta_type clenv k) in
  let c_typ = nf_betaiota clenv.evd (clenv_get_type_of clenv c) in
  let status,clenv',c = clenv_unify_binding_type clenv c c_typ k_typ in
  { clenv' with evd = meta_assign k (c,(UserGiven,status)) clenv'.evd }

let clenv_match_args bl clenv =
  if bl = [] then
    clenv
  else
    let mvs = clenv_independent clenv in
    check_bindings bl;
    List.fold_left
      (fun clenv (loc,b,c) ->
	let k = meta_of_binder clenv loc mvs b in
        if meta_defined clenv.evd k then
          if eq_constr (fst (meta_fvalue clenv.evd k)).rebus c then clenv
          else error_already_defined b
        else
	  clenv_assign_binding clenv k c)
      clenv bl

exception NoSuchBinding

let clenv_constrain_last_binding c clenv =
  let all_mvs = collect_metas clenv.templval.rebus in
  let k = try list_last all_mvs with Failure _ -> raise NoSuchBinding in
  clenv_assign_binding clenv k c

let error_not_right_number_missing_arguments n =
  errorlabstrm ""
    (strbrk "Not the right number of missing arguments (expected " ++
      int n ++ str ").")

let clenv_constrain_dep_args hyps_only bl clenv =
  if bl = [] then
    clenv
  else
    let occlist = clenv_dependent_gen hyps_only clenv in
    if List.length occlist = List.length bl then
      List.fold_left2 clenv_assign_binding clenv occlist bl
    else
      if hyps_only then
	(* Tolerance for compatibility <= 8.3 *)
	let occlist' = clenv_dependent_gen hyps_only ~iter:false clenv in
	if List.length occlist' = List.length bl then
	  List.fold_left2 clenv_assign_binding clenv occlist' bl
	else
	  error_not_right_number_missing_arguments (List.length occlist)
      else
	error_not_right_number_missing_arguments (List.length occlist)

(****************************************************************)
(* Clausal environment for an application *)

let make_clenv_binding_gen hyps_only n env sigma (c,t) = function
  | ImplicitBindings largs ->
      let clause = mk_clenv_from_env env sigma n (c,t) in
      clenv_constrain_dep_args hyps_only largs clause
  | ExplicitBindings lbind ->
      let clause = mk_clenv_from_env env sigma n 
	(c,rename_bound_vars_as_displayed [] t) 
      in clenv_match_args lbind clause
  | NoBindings ->
      mk_clenv_from_env env sigma n (c,t)

let make_clenv_binding_env_apply env sigma n =
  make_clenv_binding_gen true n env sigma
	
let make_clenv_binding_apply gls n = make_clenv_binding_gen true n (pf_env gls) gls.sigma
let make_clenv_binding gls = make_clenv_binding_gen false None (pf_env gls) gls.sigma

(****************************************************************)
(* Pretty-print *)

let pr_clenv clenv =
  h 0
    (str"TEMPL: " ++ print_constr clenv.templval.rebus ++
     str" : " ++ print_constr clenv.templtyp.rebus ++ fnl () ++
     pr_evar_map clenv.evd)
