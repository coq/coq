(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Termops
open Constr
open Context
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
open Tactypes
open Logic

(******************************************************************)
(* Clausal environments *)

type clausenv = {
  env      : env;
  evd      : evar_map;
  templval : constr freelisted;
  templtyp : constr freelisted }

let cl_env ce = ce.env
let cl_sigma ce =  ce.evd

let clenv_term clenv c = meta_instance clenv.env clenv.evd c
let clenv_meta_type clenv mv = Typing.meta_type clenv.env clenv.evd mv
let clenv_value clenv = meta_instance clenv.env clenv.evd clenv.templval
let clenv_type clenv = meta_instance clenv.env clenv.evd clenv.templtyp

let clenv_hnf_constr ce t = hnf_constr (cl_env ce) (cl_sigma ce) t

let clenv_get_type_of ce c = Retyping.get_type_of (cl_env ce) (cl_sigma ce) c

exception NotExtensibleClause

let clenv_push_prod cl =
  let typ = whd_all (cl_env cl) (cl_sigma cl) (clenv_type cl) in
  let rec clrec typ = match EConstr.kind cl.evd typ with
    | Cast (t,_,_) -> clrec t
    | Prod (na,t,u) ->
        let mv = new_meta () in
        let dep = not (noccurn (cl_sigma cl) 1 u) in
        let na' = if dep then na.binder_name else Anonymous in
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
          let na' = if dep then na.binder_name else Anonymous in
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
           Id.print id)
    | _ ->
        anomaly ~label:"clenv_assign" (Pp.str "non dependent metavar already assigned.")

(* TODO: replace by clenv_unify (mkMeta mv) rhs ? *)
let clenv_assign mv rhs clenv =
  let rhs_fls = mk_freelisted rhs in
  if Metaset.exists (mentions clenv mv) rhs_fls.freemetas then
    user_err Pp.(str "clenv_assign: circularity in unification");
  try
    if meta_defined clenv.evd mv then
      if not (EConstr.eq_constr clenv.evd (fst (meta_fvalue clenv.evd mv)).rebus rhs) then
        error_incompatible_inst clenv mv
      else
        clenv
    else
      let st = (Conv,TypeNotProcessed) in
      {clenv with evd = meta_assign mv (rhs_fls.rebus,st) clenv.evd}
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

let clenv_metas_in_type_of_meta env evd mv =
  (mk_freelisted (meta_instance env evd (meta_ftype evd mv))).freemetas

let dependent_in_type_of_metas clenv mvs =
  List.fold_right
    (fun mv -> Metaset.union (clenv_metas_in_type_of_meta clenv.env clenv.evd mv))
    mvs Metaset.empty

let dependent_closure clenv mvs =
  let rec aux mvs acc =
    Metaset.fold
      (fun mv deps ->
        let metas_of_meta_type = clenv_metas_in_type_of_meta clenv.env clenv.evd mv in
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

(* Instantiate metas that create beta/iota redexes *)

let meta_reducible_instance env evd b =
  let fm = b.freemetas in
  let fold mv accu =
    let fvalue = try meta_opt_fvalue evd mv with Not_found -> None in
    match fvalue with
    | None -> accu
    | Some (g, (_, s)) -> Metamap.add mv (g.rebus, s) accu
  in
  let metas = Metaset.fold fold fm Metamap.empty in
  let rec irec u =
    let u = whd_betaiota env Evd.empty u (* FIXME *) in
    match EConstr.kind evd u with
    | Case (ci,p,iv,c,bl) when EConstr.isMeta evd (strip_outer_cast evd c) ->
        let m = destMeta evd (strip_outer_cast evd c) in
        (match
          try
            let g, s = Metamap.find m metas in
            let is_coerce = match s with CoerceToType -> true | _ -> false in
            if isConstruct evd g || not is_coerce then Some g else None
          with Not_found -> None
          with
            | Some g -> irec (mkCase (ci,p,iv,g,bl))
            | None -> mkCase (ci,irec p,iv,c,Array.map irec bl))
    | App (f,l) when EConstr.isMeta evd (strip_outer_cast evd f) ->
        let m = destMeta evd (strip_outer_cast evd f) in
        (match
          try
            let g, s = Metamap.find m metas in
            let is_coerce = match s with CoerceToType -> true | _ -> false in
            if isLambda evd g || not is_coerce then Some g else None
          with Not_found -> None
         with
           | Some g -> irec (mkApp (g,l))
           | None -> mkApp (f,Array.map irec l))
    | Meta m ->
        (try let g, s = Metamap.find m metas in
          let is_coerce = match s with CoerceToType -> true | _ -> false in
          if not is_coerce then irec g else u
         with Not_found -> u)
    | Proj (p,c) when isMeta evd c || isCast evd c && isMeta evd (pi1 (destCast evd c)) (* What if two nested casts? *) ->
      let m = try destMeta evd c with _ -> destMeta evd (pi1 (destCast evd c)) (* idem *) in
          (match
          try
            let g, s = Metamap.find m metas in
            let is_coerce = match s with CoerceToType -> true | _ -> false in
            if isConstruct evd g || not is_coerce then Some g else None
          with Not_found -> None
          with
            | Some g -> irec (mkProj (p,g))
            | None -> mkProj (p,c))
    | _ -> EConstr.map evd irec u
  in
  if Metaset.is_empty fm then (* nf_betaiota? *) b.rebus
  else irec b.rebus

let clenv_unify ?(flags=default_unify_flags ()) cv_pb t1 t2 clenv =
  { clenv with
      evd = w_unify ~flags clenv.env clenv.evd cv_pb t1 t2 }

let clenv_unify_meta_types ?(flags=default_unify_flags ()) clenv =
  { clenv with evd = w_unify_meta_types ~flags:flags clenv.env clenv.evd }

let clenv_unique_resolver_gen ?(flags=default_unify_flags ()) clenv concl =
  if isMeta clenv.evd (fst (decompose_app_vect clenv.evd (whd_nored clenv.env clenv.evd clenv.templtyp.rebus))) then
    clenv_unify CUMUL ~flags (clenv_type clenv) concl
      (clenv_unify_meta_types ~flags clenv)
  else
    clenv_unify CUMUL ~flags
      (meta_reducible_instance clenv.env clenv.evd clenv.templtyp) concl clenv

let clenv_unique_resolver ?flags clenv gl =
  let concl = Proofview.Goal.concl gl in
  clenv_unique_resolver_gen ?flags clenv concl

let adjust_meta_source evd mv = function
  | loc,Evar_kinds.VarInstance id ->
    let rec match_name c l =
      match EConstr.kind evd c, l with
      | Lambda ({binder_name=Name id},_,c), a::l when EConstr.eq_constr evd a (mkMeta mv) -> Some id
      | Lambda (_,_,c), a::l -> match_name c l
      | _ -> None in
    (* This is very ad hoc code so that an evar inherits the name of the binder
       in situations like "ex_intro (fun x => P) ?ev p" *)
    let f = function (mv',(Cltyp (_,t) | Clval (_,_,t))) ->
      if Metaset.mem mv t.freemetas then
        let f,l = decompose_app evd t.rebus in
        match EConstr.kind evd f with
        | Meta mv'' ->
          (match meta_opt_fvalue evd mv'' with
          | Some (c,_) -> match_name c.rebus l
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
  match List.duplicates qhyp_eq (List.map (fun {CAst.v=x} -> fst x) bl) with
    | NamedHyp s :: _ ->
        user_err
          (str "The variable " ++ Id.print s ++
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
    (str"No such bound variable " ++ Id.print id ++
     (if mvl == [] then str " (no bound variables at all in the expression)."
      else
        (str" (possible name" ++
         str (if List.length mvl == 1 then " is: " else "s are: ") ++
         pr_enum Id.print mvl ++ str").")))

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
          (str "Binder name \"" ++ Id.print id ++
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
          (str "Binder name \"" ++ Id.print id ++
           str"\" already defined with incompatible value.")
    | AnonHyp n ->
        anomaly
          (str "Position " ++ int n ++ str" already defined.")

let clenv_unify_binding_type clenv c t u =
  if isMeta clenv.evd (fst (decompose_app_vect clenv.evd (whd_nored clenv.env clenv.evd u))) then
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
  let c_typ = nf_betaiota clenv.env clenv.evd (clenv_get_type_of clenv c) in
  let status,clenv',c = clenv_unify_binding_type clenv c c_typ k_typ in
  { clenv' with evd = meta_assign k (c,(Conv,status)) clenv'.evd }

let clenv_match_args bl clenv =
  if List.is_empty bl then
    clenv
  else
    let mvs = clenv_independent clenv in
    check_bindings bl;
    List.fold_left
      (fun clenv {CAst.loc;v=(b,c)} ->
        let k = meta_of_binder clenv loc mvs b in
        if meta_defined clenv.evd k then
          if EConstr.eq_constr clenv.evd (fst (meta_fvalue clenv.evd k)).rebus c then clenv
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


(* This function put casts around metavariables whose type could not be
 * inferred by the refiner, that is head of applications, predicates and
 * subject of Cases.
 * Does check that the casted type is closed. Anyway, the refiner would
 * fail in this case... *)

let clenv_cast_meta clenv =
  let rec crec u =
    match EConstr.kind clenv.evd u with
      | App _ | Case _ -> crec_hd u
      | Cast (c,_,_) when isMeta clenv.evd c -> u
      | Proj (p, c) -> mkProj (p, crec_hd c)
      | _  -> EConstr.map clenv.evd crec u

  and crec_hd u =
    match EConstr.kind clenv.evd (strip_outer_cast clenv.evd u) with
      | Meta mv ->
          (try
            let b = Typing.meta_type clenv.env clenv.evd mv in
            assert (not (occur_meta clenv.evd b));
            if occur_meta clenv.evd b then u
            else mkCast (mkMeta mv, DEFAULTcast, b)
          with Not_found -> u)
      | App(f,args) -> mkApp (crec_hd f, Array.map crec args)
      | Case(ci,p,iv,c,br) ->
          mkCase (ci, crec_hd p, map_invert crec_hd iv, crec_hd c, Array.map crec br)
      | Proj (p, c) -> mkProj (p, crec_hd c)
      | _ -> u
  in
  crec

let clenv_pose_dependent_evars ?(with_evars=false) clenv =
  let dep_mvs = clenv_dependent clenv in
  let env, sigma = clenv.env, clenv.evd in
  if not (List.is_empty dep_mvs) && not with_evars then
    raise
      (RefinerError (env, sigma, UnresolvedBindings (List.map (meta_name clenv.evd) dep_mvs)));
  clenv_pose_metas_as_evars clenv dep_mvs

let clenv_refine ?(with_evars=false) ?(with_classes=true) clenv =
  Proofview.Goal.enter begin fun gl ->
  let clenv = clenv_pose_dependent_evars ~with_evars clenv in
  let evd' =
    if with_classes then
      let evd' =
        Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
          ~fail:(not with_evars) clenv.env clenv.evd
      in
      (* After an apply, all the subgoals including those dependent shelved ones are in
         the hands of the user and resolution won't be called implicitely on them. *)
      Typeclasses.make_unresolvables (fun x -> true) evd'
    else clenv.evd
  in
  let clenv = { clenv with evd = evd' } in
  Proofview.tclTHEN
    (Proofview.Unsafe.tclEVARS (Evd.clear_metas evd'))
    (refiner ~check:false EConstr.Unsafe.(to_constr (clenv_cast_meta clenv (clenv_value clenv))))
  end

open Unification

let dft = default_unify_flags

let res_pf ?with_evars ?(with_classes=true) ?(flags=dft ()) clenv =
  Proofview.Goal.enter begin fun gl ->
    let clenv = clenv_unique_resolver ~flags clenv gl in
    clenv_refine ?with_evars ~with_classes clenv
  end

(* [unifyTerms] et [unify] ne semble pas gérer les Meta, en
   particulier ne semblent pas vérifier que des instances différentes
   d'une même Meta sont compatibles. D'ailleurs le "fst" jette les metas
   provenant de w_Unify. (Utilisé seulement dans prolog.ml) *)

let fail_quick_core_unif_flags = {
  modulo_conv_on_closed_terms = Some TransparentState.full;
  use_metas_eagerly_in_conv_on_closed_terms = false;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = TransparentState.empty;
  modulo_delta_types = TransparentState.full;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true; (* ? *)
  allowed_evars = Evarsolve.AllowedEvars.all;
  restrict_conv_on_strict_subterms = false; (* ? *)
  modulo_betaiota = false;
  modulo_eta = true;
}

let fail_quick_unif_flags = {
  core_unify_flags = fail_quick_core_unif_flags;
  merge_unify_flags = fail_quick_core_unif_flags;
  subterm_unify_flags = fail_quick_core_unif_flags;
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = false
}

(* let unifyTerms m n = walking (fun wc -> fst (w_Unify CONV m n [] wc)) *)
let unify ?(flags=fail_quick_unif_flags) ?(with_ho=true) m =
  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.New.pf_env gl in
    let n = Tacmach.New.pf_concl gl in
    let sigma = clear_metas (Tacmach.New.project gl) in
    try
      let sigma = Evarutil.add_unification_pb (CONV,env,m,n) sigma in
      let flags = Unification.flags_of flags in
      let sigma = Evarconv.solve_unif_constraints_with_heuristics ~flags ~with_ho env sigma in
        Proofview.Unsafe.tclEVARSADVANCE sigma
    with e when CErrors.noncritical e ->
      let info = Exninfo.reify () in
      Proofview.tclZERO ~info e
  end

(****************************************************************)
(* Clausal environment for an application *)

let make_clenv_binding_gen hyps_only n env sigma (c,t) = function
  | ImplicitBindings largs ->
      let clause = mk_clenv_from_env env sigma n (c,t) in
      clenv_constrain_dep_args hyps_only largs clause
  | ExplicitBindings lbind ->
      let t = rename_bound_vars_as_displayed sigma Id.Set.empty [] t in
      let clause = mk_clenv_from_env env sigma n
        (c, t)
      in clenv_match_args lbind clause
  | NoBindings ->
      mk_clenv_from_env env sigma n (c,t)

let make_clenv_binding_apply env sigma n = make_clenv_binding_gen true n env sigma
let make_clenv_binding env sigma = make_clenv_binding_gen false None env sigma

(****************************************************************)
(* Pretty-print *)

let pr_clenv clenv =
  h
    (str"TEMPL: " ++ Termops.Internal.print_constr_env clenv.env clenv.evd clenv.templval.rebus ++
     str" : " ++ Termops.Internal.print_constr_env clenv.env clenv.evd clenv.templtyp.rebus ++ fnl () ++
     pr_evar_map (Some 2) clenv.env clenv.evd)

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
  let naming =
    match na with Name id -> IntroFresh id | Anonymous -> IntroAnonymous
  in
  let sigma, ev = new_evar ~future_goal:false ~typeclass_candidate:false env sigma ~naming t1 in
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
(* MD This is duplicated from `Hints` *)
let strip_params env sigma c =
  match EConstr.kind sigma c with
  | App (f, args) ->
    (match EConstr.kind sigma f with
     | Const (cst,_) ->
       (match Recordops.find_primitive_projection cst with
        | Some p ->
          let p = Projection.make p false in
          let npars = Projection.npars p in
          if Array.length args > npars then
            mkApp (mkProj (p, args.(npars)),
                   Array.sub args (npars+1) (Array.length args - (npars + 1)))
          else c
        | None -> c)
     | _ -> c)
  | _ -> c

let make_evar_clause env sigma ?len ?occs c t =
  let bound = match len with
  | None -> -1
  | Some n -> assert (0 <= n); n
  in
  (* FIXME: do the renaming online *)
  let t = rename_bound_vars_as_displayed sigma Id.Set.empty [] t in
  let rec clrec (sigma, holes) inst n t =
    if n = 0 then (sigma, holes, t)
    else match EConstr.kind sigma t with
    | Cast (t, _, _) -> clrec (sigma, holes) inst n t
    | Prod (na, t1, t2) ->
      (* Share the evar instances as we are living in the same context *)
      let inst, ctx, args, subst = match inst with
      | None ->
        (* Dummy type *)
        let ctx, _, args, subst = push_rel_context_to_named_context env sigma mkProp in
        Some (ctx, args, subst), ctx, args, subst
      | Some (ctx, args, subst) -> inst, ctx, args, subst
      in
      let sigma, hole, t2 = make_prod_evar env sigma na.binder_name t1 t2 in
      clrec (sigma, hole :: holes) inst (pred n) t2
    | LetIn (na, b, _, t) -> clrec (sigma, holes) inst n (subst1 b t)
    | _ -> (sigma, holes, t)
  in
  let (sigma, holes, t) = clrec (sigma, []) None bound t in
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
  | [id] -> str " (possible name is: " ++ Id.print id ++ str ")."
  | _ -> str " (possible names are: " ++ pr_enum Id.print mvl ++ str ")."
  in
  user_err  (str "No such bound variable " ++ Id.print id ++ expl)

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
      (str "Binder name \"" ++ Id.print id ++
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
  let (sigma, j, _trace) = Coercion.inh_conv_coerce_to ~program_mode:false true env sigma ?flags j t in
  let (ev, _) = destEvar sigma ev in
  let sigma = Evd.define ev j.Environ.uj_val sigma in
  sigma

(** This requires to look at the evar even if it is defined *)
let hole_goal h = fst (Constr.destEvar (EConstr.Unsafe.to_constr h.hole_evar))

let clenv_advance sigma clenv =
  let { cl_concl; cl_holes; cl_val; cl_concl_occs } = clenv in
  let advance h =
    let h' = whd_evar sigma h.hole_evar in
    if Constr.equal (EConstr.Unsafe.to_constr h') (EConstr.Unsafe.to_constr h.hole_evar)
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

let hole_type env sigma hole =
  let concl = Evd.evar_concl (Evd.find_undefined sigma (hole_evar sigma hole)) in
  Reductionops.nf_betaiota env sigma (Evarutil.nf_evar sigma concl) (* MD is normalizing useful here? *)

let clenv_recompute_deps env sigma ~hyps_only clause =
  let fold h holes =
    if h.hole_deps then
      (* Some subsequent term uses the hole *)
      let (ev, _) = destEvar sigma h.hole_evar in
      let is_dep hole = occur_evar sigma ev (hole_type env sigma hole) in
      let in_hyp = List.exists is_dep holes in
      let in_ccl = occur_evar sigma ev clause.cl_concl in
      let dep = if hyps_only then in_hyp && not in_ccl else in_hyp || in_ccl in
      let h = { h with hole_deps = dep } in
      h :: holes
    else
      (* The hole does not occur anywhere *)
      h :: holes
  in
  let holes = List.fold_right fold clause.cl_holes [] in
  { clause with cl_holes = holes }

let solve_evar_clause env sigma ~hyps_only clause b =
  match b with
| NoBindings -> sigma, clause
| ImplicitBindings largs ->
  let clause = if hyps_only then clenv_recompute_deps env sigma ~hyps_only clause else clause in
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
  let fold (sigma, holes) {CAst.v=(binder, c)} =
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
       make_prod_evar env sigma na.binder_name t u
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
  (* Give priority to second-order matching which avoids falling back
     to it with unfolded terms through evar_conv. *)
  let ev, l = decompose_appvect sigma hole in
  let hd, l' = decompose_appvect sigma ty in
  let is_explicit_pattern =
    if Array.length l == Array.length l' then
      try ignore(decompose_lam_n_assum sigma (Array.length l) hd); true
      with e -> not (isEvar sigma ev)
    else not (isEvar sigma ev)
  in
  (* In case the clause is not higher-order (has no occurrences selected)
     or the type we're unifying with is an explicit predicate
     applied to the right number of arguments, we favor direct
     unification. *)
  match occs with
  | Some (f, occs) when not is_explicit_pattern ->
     let (evk, subst as ev) = destEvar sigma ev in
     let sigma, ev' =
       Evardefine.evar_absorb_arguments env sigma ev (Array.to_list l) in
     let argoccs = List.map (fun _ -> Evarconv.default_occurrence_selection) (snd ev) in
     let f, occs =
       (* We are lenient here, allowing more occurrences to be specified than
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
       (* Ensure we did actually find a solution *)
       Evarconv.solve_unif_constraints_with_heuristics
         ~flags ~with_ho:true env sigma
  | _ ->
     let ho () =
       let sigma = Evarutil.add_unification_pb (CUMUL,env,hole,ty) sigma in
        Evarconv.solve_unif_constraints_with_heuristics
          ~flags ~with_ho:true env sigma
     in
     (* Try normal unification first, if that fails use heuristics + higher-order unif *)
     let open Evarsolve in
     match Evarconv.evar_conv_x flags env sigma CUMUL hole ty with
     | Success sigma ->
        (try Evarconv.solve_unif_constraints_with_heuristics
               ~flags ~with_ho:false env sigma
         with e -> ho ())
     | UnifFailure _ -> ho ()


let clenv_unify_concl env sigma flags ty clenv =
  let concl, occs = clenv.cl_concl, clenv.cl_concl_occs in
  let sigma = clenv_unify_type env sigma flags concl occs ty in
  sigma, clenv_advance sigma clenv

let holes_goals sigma holes =
  List.map (fun h -> fst (destEvar sigma h.hole_evar)) holes

let clenv_check_dep_holes with_evars env sigma ?origsigma clenv =
  let holes = clenv_dep_holes clenv in
  if not with_evars then
    let holes' =
      match origsigma with
      | None -> holes
      | Some origsigma ->
         let origevars = Evar.Map.domain (Evd.undefined_map origsigma) in
         let filter h =
           not (Evar.Set.mem (fst (destEvar sigma h.hole_evar)) (Evarutil.reachable_from_evars sigma origevars)) in
         List.filter filter holes
    in
     if not (List.is_empty holes') then
       Proofview.tclZERO
         (Logic.RefinerError (env, sigma, Logic.UnresolvedBindings
                                (List.map (fun h -> h.hole_name) holes')))
     else Proofview.tclUNIT (holes_goals sigma holes)
  else Proofview.tclUNIT (holes_goals sigma holes)


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
       let ty = hole_type env sigma h in
       let ty' = nextcl.cl_concl in
       let sigma = clenv_unify_type env sigma (flags_of flags) ty occs ty' in
       let (ev, _) = destEvar sigma h.hole_evar in
       let sigma = Evd.define ev nextcl.cl_val sigma in
       sigma, cl
  in
  let sigma, clholes =
    let nextclholes =
      List.map_filter (fun h -> hole_def sigma h) nextcl.cl_holes
    in
    List.fold_left_map (fun sigma h ->
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

let clenv_solve_clause_constraints ?(flags=dft ()) ~with_ho clenv =
  let open Proofview in
  let open Proofview.Notations in
  tclENV >>= fun env ->
  tclEVARMAP >>= fun sigma ->
    try
      let flags = flags_of flags in
      let sigma' =
        Evarconv.solve_unif_constraints_with_heuristics env ~flags ~with_ho sigma
      in Unsafe.tclEVARS sigma' <*> tclUNIT (clenv_advance sigma' clenv)
    with e -> tclZERO e

(* FIXME check if renaming hack has to stay

let rec rename_evar_concl sigma ctxt t =
  match ctxt, kind sigma t with
  | decl :: decls, Prod (na, b, t) ->
     mkProd (Context.Rel.Declaration.get_annot decl, b, rename_evar_concl sigma decls t)
  | decl :: decls, LetIn (na, b, t', t) ->
     mkLetIn (Context.Rel.Declaration.get_annot decl, b, t', rename_evar_concl sigma decls t)
  | [], _ -> t
  | _ :: _, _ -> raise (Invalid_argument "rename_evar_concl")

let rename_term env sigma t =
  let evd = ref sigma in
  let rename_branches ci tys brs =
    let rename i ty =
      let ndecls = ci.ci_cstr_ndecls.(i) in
      let ctxt, tyctx = decompose_prod_n_assum sigma ndecls ty in
      let ctxt = List.rev ctxt in
      let hd, args = decompose_app sigma (Evarutil.whd_evar !evd brs.(i)) in
      match kind sigma hd with
      | Evar (ev, args) ->
         let evi = Evd.find_undefined !evd ev in
         let concl = evar_concl evi in
         let concl' = rename_evar_concl sigma ctxt concl in
         evd := Evd.add !evd ev { evi with evar_concl = concl' }
      | _ -> ()
    in Array.iteri rename tys
  in
  let rec aux env c =
    match kind sigma c with
    | Case (ci,p,iv,c,brs) -> (* FIXME check what should be done on iv *)
       let ct = Retyping.get_type_of env sigma c in
       let ((i,u), args) =
         try Tacred.find_hnf_rectype env sigma ct
         with Not_found -> CErrors.anomaly (Pp.str "mk_casegoals") in
       let indspec = ((i, EConstr.EInstance.kind sigma u), args) in
       let (lbrty,_) = Inductiveops.type_case_branches_with_names env sigma indspec (EConstr.Unsafe.to_constr p) (EConstr.Unsafe.to_constr c) in
       let () = rename_branches ci lbrty brs in
       mkCase (ci,p,iv,aux env c,Array.map (aux env) brs)
    | _ -> map_constr_with_full_binders sigma push_rel aux env c
  in
  let t' = aux env t in
  !evd, t'

*)

let clenv_refine_gen ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true) ?origsigma
                     flags (sigma, clenv) =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Tacmach.New.pf_env gl in
  let sigma, clenv =
    try
      let sigma = Evarconv.solve_unif_constraints_with_heuristics ~flags ~with_ho:true env sigma in
      sigma, clenv_advance sigma clenv
    with _ -> sigma, clenv in
  let sigma =
    if with_classes then
      let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
        (* Don't split as this can result in typeclasses not failing due
           to initial holes not being marked as "mandatory". *)
        ~split:false ~fail:(not with_evars) env sigma
      in Typeclasses.make_unresolvables (fun ev -> Typeclasses.all_goals ev (Lazy.from_val (snd (Evd.find sigma ev).evar_source))) sigma (* MD FIXME I put this randomly *)
    else sigma
  in
  let run sigma =
    (* Declare the future goals here, as they should become subgoals of this refine. *)
    let declare_goal sigma h =
      let ev, _ = destEvar sigma h.hole_evar in
      declare_future_goal ev sigma
    in
    let sigma = List.fold_left declare_goal sigma (clenv_holes clenv) in
    let v = nf_betaiota env sigma (clenv_val clenv) in
    (* This renaming hack should really stop at 8.6 *)
    (* FIXME remove
    if Flags.version_less_or_equal Flags.Current then
      rename_term env sigma v
    else *) sigma, v
  in
  let reduce_goal gl =
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let glev = Proofview.Goal.goal gl in
    (* For compatibility: beta iota reduction *)
    let concl = Reductionops.clos_norm_flags CClosure.betaiota env sigma concl in
    let evi = Evd.find sigma glev in
    let sigma = Evd.add sigma glev { evi with evar_concl = concl } in
    let sigma = Typeclasses.make_unresolvables (fun ev -> Evar.equal ev glev) sigma in
    Proofview.Unsafe.tclEVARS sigma
  in
  Proofview.Unsafe.tclEVARS sigma <*>
    clenv_check_dep_holes with_evars env sigma ?origsigma clenv >>= (fun deps ->
  (Refine.refine ~typecheck:false run) <*>
  (if shelve_subgoals then shelve_goals deps else tclUNIT ()) <*>
    Proofview.Goal.enter reduce_goal)
  end

let clenv_unify_concl_tac flags clenv =
  Ftactic.enter begin fun gl ->
  let env = Tacmach.New.pf_env gl in
  let sigma = Tacmach.New.project gl in
  let concl = Tacmach.New.pf_concl gl in
  try let sigma, clenv = clenv_unify_concl env sigma flags concl clenv in
      Ftactic.return (sigma, clenv)
  with Evarconv.UnableToUnify (evd, reason) ->
    let ex = Pretype_errors.(PretypeError (env, evd,
        CannotUnify (concl, clenv_concl clenv, Some reason))) in
    Ftactic.lift (Proofview.tclZERO ex) end

let clenv_refine_bindings
    ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true)
    ?(flags=dft ()) ~hyps_only ~delay_bindings b ?origsigma clenv =
  let open Proofview in
  let open Proofview.Notations in
  let flags = flags_of flags in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigma, clenv, bindings =
      if delay_bindings then
        sigma, clenv, Some (None, false, b)
      else
        try let sigma, clenv = solve_evar_clause env sigma ~hyps_only clenv b in
            sigma, clenv, None
        with e -> sigma, clenv, Some (Some e, hyps_only, b)
    in
    let tac = clenv_unify_concl_tac flags clenv in
    (Unsafe.tclEVARS sigma) <*>
    (Ftactic.run tac
      (fun (sigma, clenv) ->
        try let sigma, clenv =
          match bindings with
          | Some (exn, hyps_only, b) ->
             (* Hack to make [exists 0] on [Σ x : nat, True] work, we
                use implicit bindings for a hole that's not dependent
                after unification, but reuse the typing information. *)
             solve_evar_clause env sigma ~hyps_only clenv b
          | None -> sigma, clenv_recompute_deps env sigma ~hyps_only:false clenv
        in
        clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?origsigma
                         flags (sigma, clenv)
        with e when Pretype_errors.precatchable_exception e -> Proofview.tclZERO e))
  end

let clenv_refine_no_check
      ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true)
      ?(flags=dft ()) ?origsigma clenv =
  let open Proofview.Notations in
  let flags = flags_of flags in
  Proofview.tclEVARMAP >>= fun sigma ->
  clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?origsigma
                   flags (sigma, clenv)

let clenv_refine2 ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true)
                  ?(flags=dft ()) ?origsigma clenv =
  let flags = flags_of flags in
  let tac = clenv_unify_concl_tac flags clenv in
  Ftactic.run tac
   (clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?origsigma flags)

let with_clause (c, t) kont =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let sigma, cl = Tacmach.New.pf_apply (fun env sigma c -> make_clenv_from_env env sigma c) gl (c, t) in
  Unsafe.tclEVARS sigma <*> kont cl end
