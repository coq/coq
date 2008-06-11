(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Environ
open Evd
open Reduction
open Reductionops
open Rawterm
open Pattern
open Tacred
open Pretype_errors
open Evarutil
open Unification
open Mod_subst
open Coercion.Default

(* *)
let w_coerce env c ctyp target evd =
  try
    let j = make_judge c ctyp in
    let tycon = mk_tycon_type target in
    let (evd',j') = inh_conv_coerce_to dummy_loc env evd j tycon in
    (evd',j'.uj_val)
  with e when precatchable_exception e ->
    evd,c

let pf_env gls = Global.env_of_context gls.it.evar_hyps
let pf_type_of gls c  = Typing.type_of (pf_env gls) gls.sigma c
let pf_hnf_constr gls c = hnf_constr (pf_env gls) gls.sigma c
let pf_concl gl = gl.it.evar_concl

(******************************************************************)
(* Clausal environments *)

type clausenv = {
  env      : env;
  evd      : evar_defs;
  templval : constr freelisted;
  templtyp : constr freelisted }

let cl_env ce = ce.env
let cl_sigma ce = evars_of ce.evd

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

let clenv_get_type_of ce c =
  Retyping.get_type_of_with_meta (cl_env ce) (cl_sigma ce) (metas_of ce.evd) c

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
  let evars,_ = Evarconv.consider_remaining_unif_problems env evars in
  let args = List.map (whd_evar (Evd.evars_of evars)) args in
  check_evars env sigma evars (applist (c,args));
  args

(*arnaud: sans doute à déplacer :*)
let (>>=) = Goal.bind

(* arnaud: ça a l'air de construire une clause fraiche... *)
let mk_clenv_from_n n (c,cty) =
  Goal.defs >>= fun defs ->
  Goal.hyps >>= fun hyps ->
  let (env,args,concl) = clenv_environments defs n cty in
  Goal.return
    { templval = mk_freelisted (match args with 
				| [] -> c 
				| _ -> applist (c,args)
			       );
      templtyp = mk_freelisted concl;
      evd = env;
      env = Global.env_of_context hyps }
(* arnaud: original 
  let evd = create_goal_evar_defs gls.sigma in
  let (env,args,concl) = clenv_environments evd n cty in
  { templval = mk_freelisted (match args with [] -> c | _ -> applist (c,args));
    templtyp = mk_freelisted concl;
    evd = env;
    env = Global.env_of_context gls.it.evar_hyps }
*)

let mk_clenv_from = mk_clenv_from_n None

let mk_clenv_rename_from (c,t) = 
  Goal.env >>= fun env -> 
  mk_clenv_from (c,rename_bound_var env [] t)

let mk_clenv_rename_from_n n (c,t) = 
  Goal.env >>= fun env ->
  mk_clenv_from_n n (c,rename_bound_var env [] t)

let mk_clenv_type_of t = 
  (* spiwack: duplication of Logic.type_of to avoid inconvenient
     dependencies, should be removed in the final version *)
  let type_of c =
    Goal.env >>= fun env ->
      Goal.defs >>= fun defs ->
	Goal.return (Typing.type_of env (Evd.evars_of defs) c)
  in
  type_of t >>= fun ty ->
  mk_clenv_from (t,ty)

(******************************************************************)

(* [mentions clenv mv0 mv1] is true if mv1 is defined and mentions
 * mv0, or if one of the free vars on mv1's freelist mentions
 * mv0 *)

let mentions clenv mv0 =
  let rec menrec mv1 =
    mv0 = mv1 ||
    let mlist =
      try (fst (meta_fvalue clenv.evd mv1)).freemetas
      with Anomaly _ | Not_found -> Metaset.empty in
    meta_exists menrec mlist
  in menrec

let clenv_defined clenv mv = meta_defined clenv.evd mv

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


let clenv_wtactic f clenv = {clenv with evd = f clenv.evd }


(* [clenv_dependent hyps_only clenv]
 * returns a list of the metavars which appear in the template of clenv,
 * and which are dependent, This is computed by taking the metavars in cval,
 * in right-to-left order, and collecting the metavars which appear
 * in their types, and adding in all the metavars appearing in the
 * type of clenv.
 * If [hyps_only] then metavariables occurring in the type are _excluded_ *)

(* [clenv_metavars clenv mv]
 * returns a list of the metavars which appear in the type of
 * the metavar mv.  The list is unordered. *)

let clenv_metavars evd mv =
  (mk_freelisted (meta_instance evd (meta_ftype evd mv))).freemetas

let dependent_metas clenv mvs conclmetas =
  List.fold_right
    (fun mv deps ->
       Metaset.union deps (clenv_metavars clenv.evd mv))
    mvs conclmetas

let clenv_dependent hyps_only clenv =
  let mvs = collect_metas (clenv_value clenv) in
  let ctyp_mvs = (mk_freelisted (clenv_type clenv)).freemetas in
  let deps = dependent_metas clenv mvs ctyp_mvs in
  List.filter
    (fun mv -> Metaset.mem mv deps &&
               not (hyps_only && Metaset.mem mv ctyp_mvs))
    mvs

let clenv_missing ce = clenv_dependent true ce

(******************************************************************)

let clenv_unify allow_K cv_pb t1 t2 clenv =
  { clenv with evd = w_unify allow_K clenv.env cv_pb t1 t2 clenv.evd }

let clenv_unify_meta_types clenv =
  { clenv with evd = w_unify_meta_types clenv.env clenv.evd }

let clenv_unique_resolver allow_K clenv =
  let (>>=) = Goal.bind in (* arnaud: déplacer tout ça*)
  if isMeta (fst (whd_stack clenv.templtyp.rebus)) then
    Goal.concl >>= fun concl ->
    Goal.return (clenv_unify allow_K CUMUL (clenv_type clenv) concl
		   (clenv_unify_meta_types clenv))
  else
    Goal.concl >>= fun concl ->
    Goal.return (clenv_unify allow_K CUMUL 
		   (meta_reducible_instance clenv.evd clenv.templtyp) concl clenv)

(* [clenv_pose_dependent_evars clenv]
 * For each dependent evar in the clause-env which does not have a value,
 * pose a value for it by constructing a fresh evar.  We do this in
 * left-to-right order, so that every evar's type is always closed w.r.t.
 * metas. *)
(* spiwack: we return, additionally the list of evars so-introduced.
   which will be needed by eapply. *)
let clenv_pose_dependent_evars clenv =
  let dep_mvs = clenv_dependent false clenv in
  List.fold_left
    (fun (clenv,my_evars) mv ->
      let ty = clenv_meta_type clenv mv in
      let (evd,evar) = 
	new_evar clenv.evd (cl_env clenv) ~src:(dummy_loc,GoalEvar) ty in
      let (e,_) = destEvar evar in
      (clenv_assign mv evar {clenv with evd=evd}, e::my_evars))
    (clenv,[])
    dep_mvs

let evar_clenv_unique_resolver = clenv_unique_resolver

(******************************************************************)

let connect_clenv clenv =
  Goal.defs >>= fun defs ->
  let sigma = Evd.evars_of defs in
  Goal.hyps >>= fun hyps ->
  Goal.return
  { clenv with
    evd = evars_reset_evd sigma clenv.evd;
    env = Global.env_of_context hyps }

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
let clenv_fchain ?(allow_K=true) mv clenv nextclenv =
  (* Add the metavars of [nextclenv] to [clenv], with their name-environment *)
  let clenv' =
    { templval = clenv.templval;
      templtyp = clenv.templtyp;
      evd = 
        evar_merge (meta_merge clenv.evd nextclenv.evd) (evars_of clenv.evd);
      env = nextclenv.env } in
  (* unify the type of the template of [nextclenv] with the type of [mv] *)
  let clenv'' =
    clenv_unify allow_K CUMUL
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

type arg_bindings = Goal.open_constr explicit_bindings

(* [clenv_independent clenv]
 * returns a list of metavariables which appear in the term cval,
 * and which are not dependent.  That is, they do not appear in
 * the types of other metavars which are in cval, nor in the type
 * of cval, ctyp. *)

let clenv_independent clenv =
  let mvs = collect_metas (clenv_value clenv) in
  let ctyp_mvs = (mk_freelisted (clenv_type clenv)).freemetas in
  let deps = dependent_metas clenv mvs ctyp_mvs in
  List.filter (fun mv -> not (Metaset.mem mv deps)) mvs

let check_bindings bl =
  match list_duplicates (List.map pi2 bl) with
    | NamedHyp s :: _ -> 
	errorlabstrm ""
	  (str "The variable " ++ pr_id s ++ 
	   str " occurs more than once in binding list");
    | AnonHyp n :: _ ->
	errorlabstrm ""
	  (str "The position " ++ int n ++
	   str " occurs more than once in binding list")
    | [] -> ()

let meta_of_binder clause loc mvs = function
  | NamedHyp s -> meta_with_name clause.evd s
  | AnonHyp n ->
      try List.nth mvs (n-1)
      with (Failure _|Invalid_argument _) ->
        errorlabstrm "" (str "No such binder")

let error_already_defined b =
  match b with
    | NamedHyp id ->
        errorlabstrm ""
          (str "Binder name \"" ++ pr_id id ++
           str"\" already defined with incompatible value")
    | AnonHyp n ->
        anomalylabstrm ""
          (str "Position " ++ int n ++ str" already defined")

let rec similar_type_shapes t u =
  let t,_ = decompose_app t and u,_ = decompose_app u in
  match kind_of_term t, kind_of_term u with
  | Prod (_,t1,t2), Prod (_,u1,u2) -> similar_type_shapes t2 u2
  | Const cst, Const cst' -> cst = cst'
  | Var id, Var id' -> id = id'
  | Ind ind, Ind ind' -> ind = ind'
  | Rel n, Rel n' -> n = n'
  | Sort s, Sort s' -> family_of_sort s = family_of_sort s'
  | Case (_,_,c,_), Case (_,_,c',_) -> similar_type_shapes c c'
  | _ -> false

let clenv_unify_similar_types clenv c t u =
  if occur_meta u then
    if similar_type_shapes t u then
      try TypeProcessed, clenv_unify true CUMUL t u clenv, c
      with e when precatchable_exception e -> TypeNotProcessed, clenv, c
    else
      CoerceToType, clenv, c
  else
    let evd,c = w_coerce (cl_env clenv) c t u clenv.evd in
    TypeProcessed, { clenv with evd = evd }, c

let clenv_assign_binding clenv k oc = (*arnaud: original (sigma,c) =*)
  let (>>=) = Goal.bind in (* arnaud: à déplacer *)
  Goal.defs >>= fun defs ->
  let sigma = Evd.evars_of defs in
  let c = Goal.constr_of_open_constr oc in
  let k_typ = clenv_hnf_constr clenv (clenv_meta_type clenv k) in
  let clenv' = { clenv with evd = evar_merge clenv.evd sigma} in
  let c_typ = nf_betaiota (clenv_get_type_of clenv' c) in
  let c_typ = clenv_hnf_constr clenv' c_typ in
  let status,clenv'',c = clenv_unify_similar_types clenv' c c_typ k_typ in
(*  let evd,c' = w_coerce (cl_env clenv') c c_typ k_typ clenv'.evd in*)
  Goal.return
  { clenv'' with evd = meta_assign k (c,(UserGiven,status)) clenv''.evd }

let clenv_match_args bl clenv =
  let (>>=) = Goal.bind in (* arnaud: move ailleurs plus haut et tout *)
  if bl = [] then
    Goal.return clenv
  else
    let mvs = clenv_independent clenv in
    check_bindings bl;
    List.fold_left
      (* arnaud: original :
      (fun clenv (loc,b,(sigma,c as sc)) -> *)
      (fun clenv (loc,b,oc) ->
        clenv >>= fun clenv -> 
	let c = Goal.constr_of_open_constr oc in
	let k = meta_of_binder clenv loc mvs b in
        if meta_defined clenv.evd k then
          if eq_constr (fst (meta_fvalue clenv.evd k)).rebus c then 
	    Goal.return clenv 
          else 
	    error_already_defined b
        else
	  clenv_assign_binding clenv k oc)
      (Goal.return clenv) bl

let clenv_constrain_last_binding c clenv =
  let all_mvs = collect_metas clenv.templval.rebus in
  let k =
    try list_last all_mvs 
    with Failure _ -> error "clenv_constrain_with_bindings" in
  clenv_assign_binding clenv k (Goal.open_of_closed c)(* arnaud: original (Evd.empty,c)*)

let clenv_constrain_dep_args hyps_only bl clenv =
  let (>>=) = Goal.bind in (* arnaud: à mettre en haut *)
  if bl = [] then
    Goal.return clenv
  else
    let occlist = clenv_dependent hyps_only clenv in
    if List.length occlist = List.length bl then
      List.fold_left2 (fun ce m oc -> 
			 ce >>= fun clenv -> 
			 clenv_assign_binding clenv m oc)
	              (Goal.return clenv)
	              occlist
	              bl
      (* arnaud: mauvaise idée
      (* arnaud: sortir de là pour éviter la création inutile de clôture
	 peut-être ? *)
      let monadic_fold_left2 
      *)
      (* arnaud: original:
      List.fold_left2 clenv_assign_binding clenv occlist bl
      *)
    else 
      error ("Not the right number of missing arguments (expected "
	     ^(string_of_int (List.length occlist))^")")

(****************************************************************)
(* Clausal environment for an application *)

let make_clenv_binding_gen hyps_only n (c,t) = function
  | ImplicitBindings largs ->
      mk_clenv_from_n n (c,t) >>= fun clause ->
      clenv_constrain_dep_args hyps_only largs clause
  | ExplicitBindings lbind ->
      mk_clenv_rename_from_n n (c,t) >>= fun clause ->
      clenv_match_args lbind clause
  | NoBindings ->
      mk_clenv_from_n n (c,t)

let make_clenv_binding_apply n = make_clenv_binding_gen true n 
let make_clenv_binding = make_clenv_binding_gen false None

(****************************************************************)
(* Pretty-print *)

let pr_clenv clenv =
  h 0
    (str"TEMPL: " ++ print_constr clenv.templval.rebus ++
     str" : " ++ print_constr clenv.templtyp.rebus ++ fnl () ++
     pr_evar_defs clenv.evd)
