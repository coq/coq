(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Nameops
open Term
open Termops
open Namegen
open Environ
open Evd
open EConstr
open Vars
open Reduction
open Reductionops
open Tacred
open Pretype_errors
open Evarutil
open Unification
open Misctypes

(******************************************************************)
(* Clausal environments *)

type clausenv = {
  env      : env;
  evd      : evar_map;
  templval : constr freelisted;
  templtyp : constr freelisted }

let cl_env ce = ce.env
let cl_sigma ce =  ce.evd

let clenv_nf_meta clenv c = nf_meta clenv.evd c
let clenv_term clenv c = meta_instance clenv.evd c
let clenv_meta_type clenv mv = Typing.meta_type clenv.evd mv
let clenv_value clenv = meta_instance clenv.evd clenv.templval
let clenv_type clenv = meta_instance clenv.evd clenv.templtyp

let refresh_undefined_univs clenv =
  match EConstr.kind clenv.evd clenv.templval.rebus with
  | Var _ -> clenv, Univ.empty_level_subst
  | App (f, args) when isVar clenv.evd f -> clenv, Univ.empty_level_subst
  | _ ->  
    let evd', subst = Evd.refresh_undefined_universes clenv.evd in
    let map_freelisted f = { f with rebus = subst_univs_level_constr subst f.rebus } in
      { clenv with evd = evd'; templval = map_freelisted clenv.templval;
	templtyp = map_freelisted clenv.templtyp }, subst

let clenv_hnf_constr ce t = hnf_constr (cl_env ce) (cl_sigma ce) t

let clenv_get_type_of ce c = Retyping.get_type_of (cl_env ce) (cl_sigma ce) c

exception NotExtensibleClause

let mk_freelisted c =
  map_fl EConstr.of_constr (mk_freelisted (EConstr.Unsafe.to_constr c))

let clenv_push_prod cl =
  let typ = whd_all (cl_env cl) (cl_sigma cl) (clenv_type cl) in
  let rec clrec typ = match EConstr.kind cl.evd typ with
    | Cast (t,_,_) -> clrec t
    | Prod (na,t,u) ->
	let mv = new_meta () in
	let dep = not (noccurn (cl_sigma cl) 1 u) in
	let na' = if dep then na else Anonymous in
	let e' = meta_declare mv (EConstr.Unsafe.to_constr t) ~name:na' cl.evd in
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

(** [clenv_environments sigma n t] returns [sigma',lmeta,ccl] where
   [lmetas] is a list of metas to be applied to a proof of [t] so that
   it produces the unification pattern [ccl]; [sigma'] is [sigma]
   extended with [lmetas]; if [n] is defined, it limits the size of
   the list even if [ccl] is still a product; otherwise, it stops when
   [ccl] is not a product; example: if [t] is [forall x y, x=y -> y=x]
   and [n] is [None], then [lmetas] is [Meta n1;Meta n2;Meta n3] and
   [ccl] is [Meta n1=Meta n2]; if [n] is [Some 1], [lmetas] is [Meta n1]
   and [ccl] is [forall y, Meta n1=y -> y=Meta n1] *)

let clenv_environments evd bound t =
  let open EConstr in
  let open Vars in
  let rec clrec (e,metas) n t =
    match n, EConstr.kind evd t with
      | (Some 0, _) -> (e, List.rev metas, t)
      | (n, Cast (t,_,_)) -> clrec (e,metas) n t
      | (n, Prod (na,t1,t2)) ->
	  let mv = new_meta () in
	  let dep = not (noccurn evd 1 t2) in
	  let na' = if dep then na else Anonymous in
	  let t1 = EConstr.Unsafe.to_constr t1 in
	  let e' = meta_declare mv t1 ~name:na' e in
	  clrec (e', (mkMeta mv)::metas) (Option.map ((+) (-1)) n)
	    (if dep then (subst1 (mkMeta mv) t2) else t2)
      | (n, LetIn (na,b,_,t)) -> clrec (e,metas) n (subst1 b t)
      | (n, _) -> (e, List.rev metas, t)
  in
  clrec (evd,[]) bound t

let mk_clenv_from_env env sigma n (c,cty) =
  let evd = clear_metas sigma in
  let (evd,args,concl) = clenv_environments evd n cty in
  { templval = mk_freelisted (applist (c,args));
    templtyp = mk_freelisted concl;
    evd = evd;
    env = env }

let mk_clenv_from_n gls n (c,cty) =
  let env = Proofview.Goal.env gls in
  let sigma = Tacmach.New.project gls in
  mk_clenv_from_env env sigma n (c, cty)

let mk_clenv_from gls = mk_clenv_from_n gls None

let mk_clenv_type_of gls t = mk_clenv_from gls (t,Tacmach.New.pf_unsafe_type_of gls t)

(******************************************************************)

(* [mentions clenv mv0 mv1] is true if mv1 is defined and mentions
 * mv0, or if one of the free vars on mv1's freelist mentions
 * mv0 *)

let mentions clenv mv0 =
  let rec menrec mv1 =
    Int.equal mv0 mv1 ||
    let mlist =
      try match meta_opt_fvalue clenv.evd mv1 with
      | Some (b,_) -> b.freemetas
      | None -> Metaset.empty
      with Not_found -> Metaset.empty in
    Metaset.exists menrec mlist
  in menrec

let error_incompatible_inst clenv mv  =
  let na = meta_name clenv.evd mv in
  match na with
      Name id ->
        user_err ~hdr:"clenv_assign"
          (str "An incompatible instantiation has already been found for " ++
           pr_id id)
    | _ ->
        anomaly ~label:"clenv_assign" (Pp.str "non dependent metavar already assigned.")

(* TODO: replace by clenv_unify (mkMeta mv) rhs ? *)
let clenv_assign mv rhs clenv =
  let rhs_fls = mk_freelisted rhs in
  if Metaset.exists (mentions clenv mv) rhs_fls.freemetas then
    user_err Pp.(str "clenv_assign: circularity in unification");
  try
    if meta_defined clenv.evd mv then
      if not (EConstr.eq_constr clenv.evd (EConstr.of_constr (fst (meta_fvalue clenv.evd mv)).rebus) rhs) then
        error_incompatible_inst clenv mv
      else
	clenv
    else
      let st = (Conv,TypeNotProcessed) in
      {clenv with evd = meta_assign mv (EConstr.Unsafe.to_constr rhs_fls.rebus,st) clenv.evd}
  with Not_found ->
    user_err Pp.(str "clenv_assign: undefined meta")



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
  (mk_freelisted (meta_instance evd (map_fl EConstr.of_constr (meta_ftype evd mv)))).freemetas

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

let clenv_dependent_gen hyps_only ?(iter=true) clenv =
  let all_undefined = undefined_metas clenv.evd in
  let deps_in_concl = (mk_freelisted (clenv_type clenv)).freemetas in
  let deps_in_hyps = dependent_in_type_of_metas clenv all_undefined in
  let deps_in_concl =
    if hyps_only && iter then dependent_closure clenv deps_in_concl
    else deps_in_concl in
  List.filter
    (fun mv ->
      if hyps_only then
	Metaset.mem mv deps_in_hyps && not (Metaset.mem mv deps_in_concl)
      else
	Metaset.mem mv deps_in_hyps || Metaset.mem mv deps_in_concl)
    all_undefined

let clenv_missing ce = clenv_dependent_gen true ce
let clenv_dependent ce = clenv_dependent_gen false ce

(******************************************************************)

let clenv_unify ?(flags=default_unify_flags ()) cv_pb t1 t2 clenv =
  { clenv with
      evd = w_unify ~flags clenv.env clenv.evd cv_pb t1 t2 }

let clenv_unify_meta_types ?(flags=default_unify_flags ()) clenv =
  { clenv with evd = w_unify_meta_types ~flags:flags clenv.env clenv.evd }

let clenv_unique_resolver_gen ?(flags=default_unify_flags ()) clenv concl =
  if isMeta clenv.evd (fst (decompose_app_vect clenv.evd (whd_nored clenv.evd clenv.templtyp.rebus))) then
    clenv_unify CUMUL ~flags (clenv_type clenv) concl
      (clenv_unify_meta_types ~flags clenv)
  else
    clenv_unify CUMUL ~flags
      (meta_reducible_instance clenv.evd clenv.templtyp) concl clenv

let old_clenv_unique_resolver ?flags clenv gl =
  let concl = Goal.V82.concl clenv.evd (sig_it gl) in
  clenv_unique_resolver_gen ?flags clenv concl

let clenv_unique_resolver ?flags clenv gl =
  let concl = Proofview.Goal.concl gl in
  clenv_unique_resolver_gen ?flags clenv concl

let adjust_meta_source evd mv = function
  | loc,Evar_kinds.VarInstance id ->
    let rec match_name c l =
      match EConstr.kind evd c, l with
      | Lambda (Name id,_,c), a::l when EConstr.eq_constr evd a (mkMeta mv) -> Some id
      | Lambda (_,_,c), a::l -> match_name c l
      | _ -> None in
    (* This is very ad hoc code so that an evar inherits the name of the binder
       in situations like "ex_intro (fun x => P) ?ev p" *)
    let f = function (mv',(Cltyp (_,t) | Clval (_,_,t))) ->
      if Metaset.mem mv t.freemetas then
        let f,l = decompose_app evd (EConstr.of_constr t.rebus) in
        match EConstr.kind evd f with
        | Meta mv'' ->
          (match meta_opt_fvalue evd mv'' with
          | Some (c,_) -> match_name (EConstr.of_constr c.rebus) l
          | None -> None)
        | _ -> None
      else None in
    let id = try List.find_map f (Evd.meta_list evd) with Not_found -> id in
    loc,Evar_kinds.VarInstance id
  | src -> src

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
      if occur_meta clenv.evd ty then fold clenv (mvs@[mv])
      else
        let src = evar_source_of_meta mv clenv.evd in
        let src = adjust_meta_source clenv.evd mv src in
        let evd = clenv.evd in
	let (evd, evar) = new_evar (cl_env clenv) evd ~src ty in
	let clenv = clenv_assign mv evar {clenv with evd=evd} in
	fold clenv mvs in
  fold clenv dep_mvs

(******************************************************************)

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

let fchain_flags () =
  { (default_unify_flags ()) with
    allow_K_in_toplevel_higher_order_unification = true }

let clenv_fchain ?with_univs ?(flags=fchain_flags ()) mv clenv nextclenv =
  (* Add the metavars of [nextclenv] to [clenv], with their name-environment *)
  let clenv' =
    { templval = clenv.templval;
      templtyp = clenv.templtyp;
      evd = meta_merge ?with_univs nextclenv.evd clenv.evd;
      env = nextclenv.env } in
  (* unify the type of the template of [nextclenv] with the type of [mv] *)
  let clenv'' =
    clenv_unify ~flags CUMUL
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
  let mvs = collect_metas clenv.evd (clenv_value clenv) in
  let ctyp_mvs = (mk_freelisted (clenv_type clenv)).freemetas in
  let deps = Metaset.union (dependent_in_type_of_metas clenv mvs) ctyp_mvs in
  List.filter (fun mv -> not (Metaset.mem mv deps)) mvs

let qhyp_eq h1 h2 = match h1, h2 with
| NamedHyp n1, NamedHyp n2 -> Id.equal n1 n2
| AnonHyp i1, AnonHyp i2 -> Int.equal i1 i2
| _ -> false

let check_bindings bl =
  match List.duplicates qhyp_eq (List.map (fun x -> fst (snd x)) bl) with
    | NamedHyp s :: _ ->
	user_err 
	  (str "The variable " ++ pr_id s ++
	   str " occurs more than once in binding list.");
    | AnonHyp n :: _ ->
	user_err 
	  (str "The position " ++ int n ++
	   str " occurs more than once in binding list.")
    | [] -> ()

let explain_no_such_bound_variable evd id =
  let fold l (n, clb) =
    let na = match clb with
    | Cltyp (na, _) -> na
    | Clval (na, _, _) -> na
    in
    if na != Anonymous then Name.get_id na :: l else l
  in
  let mvl = List.fold_left fold [] (Evd.meta_list evd) in
  user_err ~hdr:"Evd.meta_with_name"
    (str"No such bound variable " ++ pr_id id ++
     (if mvl == [] then str " (no bound variables at all in the expression)."
      else
        (str" (possible name" ++
         str (if List.length mvl == 1 then " is: " else "s are: ") ++
         pr_enum pr_id mvl ++ str").")))

let meta_with_name evd id =
  let na = Name id in
  let fold (l1, l2 as l) (n, clb) =
    let (na',def) = match clb with
    | Cltyp (na, _) -> (na, false)
    | Clval (na, _, _) -> (na, true)
    in
    if Name.equal na na' then if def then (n::l1,l2) else (n::l1,n::l2)
    else l
  in
  let (mvl, mvnodef) = List.fold_left fold ([], []) (Evd.meta_list evd) in
  match mvnodef, mvl with
    | _,[]  ->
      explain_no_such_bound_variable evd id
    | ([n],_|_,[n]) ->
        n
    | _  ->
        user_err ~hdr:"Evd.meta_with_name"
          (str "Binder name \"" ++ pr_id id ++
           strbrk "\" occurs more than once in clause.")

let meta_of_binder clause loc mvs = function
  | NamedHyp s -> meta_with_name clause.evd s
  | AnonHyp n ->
      try List.nth mvs (n-1)
      with (Failure _|Invalid_argument _) ->
        user_err  (str "No such binder.")

let error_already_defined b =
  match b with
    | NamedHyp id ->
        user_err 
          (str "Binder name \"" ++ pr_id id ++
           str"\" already defined with incompatible value.")
    | AnonHyp n ->
        anomaly
          (str "Position " ++ int n ++ str" already defined.")

let clenv_unify_binding_type clenv c t u =
  if isMeta clenv.evd (fst (decompose_app_vect clenv.evd (whd_nored clenv.evd u))) then
    (* Not enough information to know if some subtyping is needed *)
    CoerceToType, clenv, c
  else
    (* Enough information so as to try a coercion now *)
    try
      let evd,c = w_coerce_to_type (cl_env clenv) clenv.evd c t u in
      TypeProcessed, { clenv with evd = evd }, c
    with 
      | PretypeError (_,_,ActualTypeNotCoercible (_,_,
          (NotClean _ | ConversionFailed _))) as e ->
	  raise e
      | e when precatchable_exception e ->
	  TypeNotProcessed, clenv, c

let clenv_assign_binding clenv k c =
  let k_typ = clenv_hnf_constr clenv (clenv_meta_type clenv k) in
  let c_typ = nf_betaiota clenv.evd (clenv_get_type_of clenv c) in
  let status,clenv',c = clenv_unify_binding_type clenv c c_typ k_typ in
  let c = EConstr.Unsafe.to_constr c in
  { clenv' with evd = meta_assign k (c,(Conv,status)) clenv'.evd }

let clenv_match_args bl clenv =
  if List.is_empty bl then
    clenv
  else
    let mvs = clenv_independent clenv in
    check_bindings bl;
    List.fold_left
      (fun clenv (loc,(b,c)) ->
	let k = meta_of_binder clenv loc mvs b in
        if meta_defined clenv.evd k then
          if EConstr.eq_constr clenv.evd (EConstr.of_constr (fst (meta_fvalue clenv.evd k)).rebus) c then clenv
          else error_already_defined b
        else
	  clenv_assign_binding clenv k c)
      clenv bl

exception NoSuchBinding

let clenv_constrain_last_binding c clenv =
  let all_mvs = collect_metas clenv.evd clenv.templval.rebus in
  let k = try List.last all_mvs with Failure _ -> raise NoSuchBinding in
  clenv_assign_binding clenv k c

let error_not_right_number_missing_arguments n =
  user_err 
    (strbrk "Not the right number of missing arguments (expected " ++
      int n ++ str ").")

let clenv_constrain_dep_args hyps_only bl clenv =
  if List.is_empty bl then
    clenv
  else
    let occlist = clenv_dependent_gen hyps_only clenv in
    if Int.equal (List.length occlist) (List.length bl) then
      List.fold_left2 clenv_assign_binding clenv occlist bl
    else
      if hyps_only then
	(* Tolerance for compatibility <= 8.3 *)
	let occlist' = clenv_dependent_gen hyps_only ~iter:false clenv in
	if Int.equal (List.length occlist') (List.length bl) then
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
      let t = rename_bound_vars_as_displayed sigma [] [] t in
      let clause = mk_clenv_from_env env sigma n
	(c, t)
      in clenv_match_args lbind clause
  | NoBindings ->
      mk_clenv_from_env env sigma n (c,t)

let make_clenv_binding_env_apply env sigma n =
  make_clenv_binding_gen true n env sigma

let make_clenv_binding_env env sigma =
  make_clenv_binding_gen false None env sigma
	
let make_clenv_binding_apply env sigma n = make_clenv_binding_gen true n env sigma
let make_clenv_binding env sigma = make_clenv_binding_gen false None env sigma

(****************************************************************)
(* Pretty-print *)

let pr_clenv clenv =
  h 0
    (str"TEMPL: " ++ print_constr clenv.templval.rebus ++
     str" : " ++ print_constr clenv.templtyp.rebus ++ fnl () ++
     pr_evar_map (Some 2) clenv.evd)

(****************************************************************)
(** Evar version of mk_clenv *)

type hole = {
  hole_evar : EConstr.constr;
  hole_type : EConstr.types;
  hole_deps  : bool;
  hole_name : Name.t;
}

type clause = {
  cl_holes : hole list;
  (** The holes of the clause. *)
  cl_concl : types;
  (** The conclusion: an evar applied to some terms *)
  cl_concl_occs : Evarconv.occurrences_selection option;
  (** The occurrences of the terms to be abstracted when unifying *)
  cl_val   : constr;
  (** The value the clause was built from, applied to holes *)
}

let make_prod_evar env sigma na t1 t2 =
  let store = Typeclasses.set_resolvable Evd.Store.empty false in
  let naming =
    match na with Name id -> IntroFresh id | Anonymous -> IntroAnonymous
  in
  let sigma, ev = new_evar ~future_goal:false ~store env sigma ~naming t1 in
  let dep = dependent sigma (mkRel 1) t2 in
  let hole = {
      hole_evar = ev;
      hole_deps = dep;
      hole_type = t1;
      (* We fix it later *)
      hole_name = na;
    } in
  let t2 = if dep then subst1 ev t2 else t2 in
  sigma, hole, t2

(** Stripping params on applications of primitive projections *)
let strip_params env sigma c =
  let open EConstr in
  match kind sigma c with
  | App (f, args) ->
    (match kind sigma f with
    | Const (p,_) ->
      let cb = lookup_constant p env in
	(match cb.Declarations.const_proj with
	| Some pb ->
	  let n = pb.Declarations.proj_npars in
	    if Array.length args > n then
	      mkApp (mkProj (Projection.make p false, args.(n)),
		     Array.sub args (n+1) (Array.length args - (n + 1)))
	    else c
	| None -> c)
    | _ -> c)
  | _ -> c

let make_evar_clause env sigma ?len ?occs c t =
  let bound = match len with
  | None -> -1
  | Some n -> assert (0 <= n); n
  in
  (** FIXME: do the renaming online *)
  let t = rename_bound_vars_as_displayed sigma [] [] t in
  let rec clrec (sigma, holes) n t =
    if n = 0 then (sigma, holes, t)
    else match EConstr.kind sigma t with
    | Cast (t, _, _) -> clrec (sigma, holes) n t
    | Prod (na, t1, t2) ->
       let sigma, hole, t2 = make_prod_evar env sigma na t1 t2 in
       clrec (sigma, hole :: holes) (pred n) t2
    | LetIn (na, b, _, t) -> clrec (sigma, holes) n (subst1 b t)
    | _ -> (sigma, holes, t)
  in
  let (sigma, holes, t) = clrec (sigma, []) bound t in
  let holes = List.rev holes in
  let v = applist (c, List.map (fun h -> h.hole_evar) holes) in
  let c = strip_params env sigma v in
  let clause = { cl_holes = holes; cl_val = c;
                 cl_concl = t; cl_concl_occs = occs } in
  (sigma, clause)

let explain_no_such_bound_variable holes id =
  let fold h accu = match h.hole_name with
  | Anonymous -> accu
  | Name id -> id :: accu
  in
  let mvl = List.fold_right fold holes [] in
  let expl = match mvl with
  | [] -> str " (no bound variables at all in the expression)."
  | [id] -> str "(possible name is: " ++ pr_id id ++ str ")."
  | _ -> str "(possible names are: " ++ pr_enum pr_id mvl ++ str ")."
  in
  user_err  (str "No such bound variable " ++ pr_id id ++ spc () ++ expl)

let evar_with_name holes id =
  let map h = match h.hole_name with
  | Anonymous -> None
  | Name id' -> if Id.equal id id' then Some h else None
  in
  let hole = List.map_filter map holes in
  match hole with
  | [] -> explain_no_such_bound_variable holes id
  | [h] -> h.hole_evar
  | _ ->
    user_err 
      (str "Binder name \"" ++ pr_id id ++
        str "\" occurs more than once in clause.")

let nth_anonymous holes n =
  let rec hole holes n =
    match holes, n with
    | h :: holes, n when h.hole_name <> Anonymous -> hole holes n
    | h :: holes, 0 -> h.hole_evar
    | h :: holes, n -> hole holes (pred n)
    | [], _ -> user_err (str "No such binder.")
  in hole holes (pred n)

let evar_of_binder holes = function
| NamedHyp s -> evar_with_name holes s
| AnonHyp n -> nth_anonymous holes n

let define_with_type env sigma ?flags ev c ty =
  let t = Retyping.get_type_of env sigma ev in
  let ty =
    match ty with
    | Some t -> t
    | None -> Retyping.get_type_of env sigma c in
  let j = Environ.make_judge c ty in
  let (sigma, j) = Coercion.inh_conv_coerce_to true env sigma ?flags j t in
  let (ev, _) = destEvar sigma ev in
  let sigma = Evd.define ev (EConstr.Unsafe.to_constr j.Environ.uj_val) sigma in
  sigma

(** This requires to look at the evar even if it is defined *)
let hole_goal h = fst (Term.destEvar (EConstr.Unsafe.to_constr h.hole_evar))

let clenv_advance sigma clenv =
  let { cl_concl; cl_holes; cl_val; cl_concl_occs } = clenv in
  let advance h =
    let h' = whd_evar sigma h.hole_evar in
    if Term.eq_constr (EConstr.Unsafe.to_constr h') (EConstr.Unsafe.to_constr h.hole_evar)
    then Some h
    else
      let ev = hole_goal h in
      match Proofview.Unsafe.advance sigma ev with
      | Some ev' ->
         let na =
           match evar_ident ev' sigma with
           | Some id -> Name id
           | None -> h.hole_name
         in
         Some { h with hole_evar = h'; hole_name = na }
      | None -> None
  in
  let holes = List.map_filter advance cl_holes in
    if holes == cl_holes then clenv
    else
      { cl_holes = holes;
        cl_concl = nf_evar sigma cl_concl;
        cl_val = nf_evar sigma cl_val;
        cl_concl_occs }

let hole_evar sigma hole = fst (destEvar sigma hole.hole_evar)

let hole_type sigma hole =
  let concl = Evd.evar_concl (Evd.find_undefined sigma (hole_evar sigma hole)) in
  Reductionops.nf_betaiota sigma (Evarutil.nf_evar sigma (EConstr.of_constr concl))

let clenv_recompute_deps sigma ~hyps_only clenv =
  let concl = clenv.cl_concl in
  let fold h rest =
    if h.hole_deps then
      (** Some subsequent term uses the hole *)
      let ev, _ = destEvar sigma h.hole_evar in
      let is_dep hole = occur_evar sigma ev (hole_type sigma hole) in
      let in_hyp = List.exists is_dep rest in
      let in_concl = occur_evar sigma ev concl in
      let dep = if hyps_only then in_hyp && not in_concl else in_hyp || in_concl in
      let h' = { h with hole_deps = dep } in
      h' :: rest
    else
      (** The hole does not occur anywhere *)
      h :: rest
  in
  let holes = List.fold_right fold clenv.cl_holes [] in
  { clenv with cl_holes = holes }

let solve_evar_clause env sigma ~hyps_only clause b =
  match b with
| NoBindings -> sigma, clause
| ImplicitBindings largs ->
  let clause = if hyps_only then clenv_recompute_deps sigma ~hyps_only clause else clause in
  let evs, holes' = List.partition (fun h -> h.hole_deps) clause.cl_holes in
  let len = List.length evs in
  if Int.equal len (List.length largs) then
    let fold sigma ev arg = define_with_type env sigma ev.hole_evar arg None in
    let sigma = List.fold_left2 fold sigma evs largs in
    let clause = { clause with cl_holes = holes' } in
    sigma, clenv_advance sigma clause
  else
    error_not_right_number_missing_arguments len
| ExplicitBindings lbind ->
  let () = check_bindings lbind in
  let fold (sigma, holes) (_, (binder, c)) =
    let ev = evar_of_binder clause.cl_holes binder in
    let rem ev' = EConstr.eq_constr sigma ev ev'.hole_evar in
    let holes = List.remove_first rem holes in
    define_with_type env sigma ev c None, holes
  in
  let sigma, holes = List.fold_left fold (sigma,clause.cl_holes) lbind in
  let clause = { clause with cl_holes = holes } in
  sigma, clenv_advance sigma clause

let make_clenv_from_env env sigma ?len ?occs (c, t) =
  make_evar_clause env sigma ?len ?occs (strip_outer_cast sigma c) t

let make_clenv_bindings env sigma ?len ?occs p ~hyps_only b =
  let sigma, cle = make_clenv_from_env env sigma ?len ?occs p in
  solve_evar_clause env sigma ~hyps_only cle b

let clenv_indep_holes c =
  let holes = c.cl_holes in
  let filter h = not h.hole_deps in
  List.filter filter holes

let clenv_concl cl = cl.cl_concl
let clenv_val   cl = cl.cl_val
let clenv_holes cl = cl.cl_holes

let clenv_dep_holes clenv =
  let holes = clenv_holes clenv in
  List.filter (fun h -> h.hole_deps) holes

let clenv_dest_prod env sigma
  { cl_concl = concl; cl_holes = holes; cl_val = v; cl_concl_occs = occs } =
  let typ = whd_all env sigma concl in
  let rec clrec typ = match EConstr.kind sigma typ with
    | Cast (t,_,_) -> clrec t
    | Prod (na,t,u) ->
       make_prod_evar env sigma na t u
    | _ -> raise NotExtensibleClause
  in
  let sigma, hole, typ' = clrec typ in
  let v = strip_params env sigma (applist (v, [hole.hole_evar])) in
  let occs' =
    match occs with
    | None -> None
    | Some (f, occs) -> Some (f, occs @ [Evarconv.default_occurrence_selection])
  in
  let clause =
    { cl_holes = holes @ [hole]; cl_val = v;
      cl_concl = typ'; cl_concl_occs = occs' }
  in sigma, clause

let clenv_map_concl f clenv =
  let concl = clenv.cl_concl in
  { clenv with cl_concl = f concl }

let clenv_unify_type env sigma flags hole occs ty =
  (** Give priority to second-order matching which avoids falling back
      to it with unfolded terms through evar_conv. *)
  let ev, l = decompose_appvect sigma hole in
  let hd, l' = decompose_appvect sigma ty in
  let is_explicit_pattern =
    if Array.length l == Array.length l' then
      try ignore(decompose_lam_n_assum sigma (Array.length l) hd); true
      with e -> not (isEvar sigma ev)
    else not (isEvar sigma ev)
  in
  (** In case the clause is not higher-order (has no occurrences selected)
      or the type we're unifying with is an explicit predicate
      applied to the right number of arguments, we favor direct
      unification. *)
  match occs with
  | Some (f, occs) when not is_explicit_pattern ->
     let (evk, subst as ev) = destEvar sigma ev in
     let sigma, ev' =
       Evardefine.evar_absorb_arguments env sigma ev (Array.to_list l) in
     let argoccs = Array.map_to_list (fun _ -> Evarconv.default_occurrence_selection) (snd ev) in
     let f, occs =
       (** We are lenient here, allowing more occurrences to be specified than
            the actual arguments of the evar. Helps dealing with eliminators we
            don't know the arity of (e.g. dependent or not). *)
       let () =
         if not (Array.length l <= List.length occs) then
           user_err (Pp.str"Clause unification: occurrence list does not match argument list")
       in (f, List.firstn (Array.length l) occs)
     in
     let occs = List.rev (argoccs @ occs) in
     let sigma, b =
       Evarconv.second_order_matching flags env sigma ev' (f, occs) ty
     in
     if not b then
       let reason = ConversionFailed (env,hole,ty) in
       Pretype_errors.error_cannot_unify env sigma ~reason (hole, ty)
     else
       (** Ensure we did actually find a solution *)
       Evarconv.consider_remaining_unif_problems
         ~flags ~with_ho:true env sigma
  | _ ->
     let ho () =
       let sigma = Evarutil.add_unification_pb (CUMUL,env,hole,ty) sigma in
        Evarconv.consider_remaining_unif_problems
          ~flags ~with_ho:true env sigma
     in
     (** Try normal unification first, if that fails use heuristics + higher-order unif *)
     let open Evarsolve in
     match Evarconv.evar_conv_x flags env sigma CUMUL hole ty with
     | Success sigma ->
        (try Evarconv.consider_remaining_unif_problems
               ~flags ~with_ho:false env sigma
         with e -> ho ())
     | UnifFailure _ -> ho ()


let clenv_unify_concl env sigma flags ty clenv =
  let concl, occs = clenv.cl_concl, clenv.cl_concl_occs in
  let sigma = clenv_unify_type env sigma flags concl occs ty in
  sigma, clenv_advance sigma clenv

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

let hole_def sigma h =
  match h.hole_name with
  | Name id ->
     let res = nf_evar sigma h.hole_evar in
     if isEvar sigma res then
       Some (fst (destEvar sigma res), id)
     else None
  | Anonymous -> None

let clenv_chain ?(holes_order=true) ?(flags=fchain_flags ()) ?occs
                env sigma h cl nextcl =
  let sigma, cl =
    match occs with
    | None -> define_with_type env sigma ~flags:(flags_of flags)
                 h.hole_evar nextcl.cl_val (Some nextcl.cl_concl), cl
    | Some _ ->
       let ty = hole_type sigma h in
       let ty' = nextcl.cl_concl in
       let sigma = clenv_unify_type env sigma (flags_of flags) ty occs ty' in
       let (ev, _) = destEvar sigma h.hole_evar in
       let sigma = Evd.define ev (EConstr.Unsafe.to_constr nextcl.cl_val) sigma in
       sigma, cl
  in
  let sigma, clholes =
    let nextclholes =
      List.map_filter (fun h -> hole_def sigma h) nextcl.cl_holes
    in
    List.fold_map (fun sigma h ->
        try
          let id = List.assoc_f Evar.equal (hole_goal h) nextclholes in
          Evd.rename (hole_goal h) id sigma, { h with hole_name = Name id }
        with Not_found -> sigma, h) sigma cl.cl_holes
  in
  let holes' =
    if holes_order then
      clholes @ nextcl.cl_holes
    else
      nextcl.cl_holes @ clholes
  in
  let cl = { cl with cl_holes = holes' } in
  sigma, clenv_advance sigma cl

let clenv_chain_last ?(flags=fchain_flags ()) env sigma c cl =
  let h = try List.last cl.cl_holes with Failure _ -> raise NoSuchBinding in
  let sigma = define_with_type env sigma ~flags:(flags_of flags) h.hole_evar c None in
  sigma, clenv_advance sigma cl
