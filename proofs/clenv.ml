(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Nameops
open Termops
open Constr
open Context
open Environ
open Evd
open EConstr
open Vars
open Reductionops
open Tacred
open Pretype_errors
open Evarutil
open Unification
open Tactypes
open Logic

(******************************************************************)
(* Clausal environments *)

type meta_arg = metavariable * metavariable list option
(* List of clenv meta arguments with the submetas of the clenv it has been
   possibly chained with. We never need to chain more than two clenvs, so there
   is no need to make the type recursive. *)

type clausenv = {
  env      : env;
  evd      : evar_map;
  metas    : meta_arg list;
  templval : constr;
  metaset : Metaset.t;
  templtyp : constr freelisted;
}

let mk_clausenv env evd metas templval metaset templtyp = {
  env; evd; metas; templval; metaset; templtyp;
}

let update_clenv_evd clenv evd =
  mk_clausenv clenv.env evd clenv.metas clenv.templval clenv.metaset clenv.templtyp

let strip_params env sigma c =
  match EConstr.kind sigma c with
  | App (f, args) ->
    (match EConstr.kind sigma f with
    | Const (cst,_) ->
      (match Structures.PrimitiveProjections.find_opt cst with
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

let clenv_strip_proj_params clenv =
  let templval = strip_params clenv.env clenv.evd clenv.templval in
  mk_clausenv clenv.env clenv.evd clenv.metas templval clenv.metaset clenv.templtyp

let clenv_refresh env sigma ctx clenv =
  let evd = Evd.meta_merge (Evd.meta_list clenv.evd) (Evd.clear_metas sigma) in
  match ctx with
  | Some ctx ->
    let (subst, ctx) = UnivGen.fresh_sort_context_instance ctx in
    let emap c = Vars.subst_univs_level_constr subst c in
    let evd = Evd.merge_sort_context_set Evd.univ_flexible evd ctx in
    (* Only metas are mentioning the old universes. *)
    mk_clausenv env (Evd.map_metas emap evd) clenv.metas
      (emap clenv.templval)
      clenv.metaset
      (Evd.map_fl emap clenv.templtyp)
  | None ->
    mk_clausenv env evd clenv.metas clenv.templval clenv.metaset clenv.templtyp

let clenv_evd ce =  ce.evd
let clenv_arguments c = List.map fst c.metas

let clenv_meta_type env sigma mv =
  let ty =
    try Evd.meta_ftype sigma mv
    with Not_found -> anomaly Pp.(str "unknown meta ?" ++ str (Nameops.string_of_meta mv) ++ str ".") in
  meta_instance env sigma ty
let clenv_value clenv = meta_instance clenv.env clenv.evd { rebus = clenv.templval; freemetas = clenv.metaset }
let clenv_type clenv = meta_instance clenv.env clenv.evd clenv.templtyp

let clenv_push_prod cl =
  let typ = whd_all cl.env (clenv_evd cl) (clenv_type cl) in
  let rec clrec typ = match EConstr.kind cl.evd typ with
    | Cast (t,_,_) -> clrec t
    | Prod (na,t,u) ->
        let mv = new_meta () in
        let dep = not (noccurn (clenv_evd cl) 1 u) in
        let na' = if dep then na.binder_name else Anonymous in
        let e' = meta_declare mv t ~name:na' cl.evd in
        let concl = if dep then subst1 (mkMeta mv) u else u in
        let templval = applist (cl.templval, [mkMeta mv]) in
        let metaset = Metaset.add mv cl.metaset in
        Some (mv, dep, { templval; metaset;
          templtyp = mk_freelisted concl;
          evd = e';
          env = cl.env;
          metas = cl.metas @ [mv, None]; })
    | _ -> None
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
          clrec (e', (mv)::metas) (Option.map ((+) (-1)) n)
            (if dep then (subst1 (mkMeta mv) t2) else t2)
      | (n, LetIn (na,b,_,t)) -> clrec (e,metas) n (subst1 b t)
      | (n, _) -> (e, List.rev metas, t)
  in
  clrec (evd,[]) bound t

let mk_clenv_from_env env sigma n (c,cty) =
  let evd = clear_metas sigma in
  let (evd,args,concl) = clenv_environments evd n cty in
  let templval = mkApp (c, Array.map_of_list mkMeta args) in
  let metaset = Metaset.of_list args in
  { templval; metaset;
    templtyp = mk_freelisted concl;
    evd = evd;
    env = env;
    metas = List.map (fun mv -> mv, None) args; }

let mk_clenv_from env sigma c = mk_clenv_from_env env sigma None c
let mk_clenv_from_n env sigma n c = mk_clenv_from_env env sigma (Some n) c

(******************************************************************)

(* [mentions clenv mv0 mv1] is true if mv1 is defined and mentions
 * mv0, or if one of the free vars on mv1's freelist mentions
 * mv0 *)

let mentions sigma mv0 =
  let rec menrec mv1 =
    Int.equal mv0 mv1 ||
    let mlist =
      try match meta_opt_fvalue sigma mv1 with
      | Some (b,_) -> b.freemetas
      | None -> Metaset.empty
      with Not_found -> Metaset.empty in
    Metaset.exists menrec mlist
  in menrec

let error_incompatible_inst sigma mv  =
  let na = meta_name sigma mv in
  match na with
  | Name id ->
    user_err
      Pp.(str "An incompatible instantiation has already been found for " ++
          Id.print id)
  | _ ->
    anomaly ~label:"clenv_assign" (Pp.str "non dependent metavar already assigned.")

(* TODO: replace by clenv_unify (mkMeta mv) rhs ? *)
let clenv_assign env sigma mv rhs =
  let rhs_fls = mk_freelisted rhs in
  if Metaset.exists (mentions sigma mv) rhs_fls.freemetas then
    user_err Pp.(str "clenv_assign: circularity in unification");
  try
    begin match meta_opt_fvalue sigma mv with
    | Some (body, _) ->
      if not (EConstr.eq_constr sigma body.rebus rhs) then
        error_incompatible_inst sigma mv
      else
        sigma
    | None ->
      let st = (Conv,TypeNotProcessed) in
      meta_assign mv (rhs_fls.rebus, st) sigma
    end
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

let clenv_metas_in_type_of_meta env sigma mv =
  (mk_freelisted (meta_instance env sigma (meta_ftype sigma mv))).freemetas

let dependent_in_type_of_metas env sigma mvs =
  List.fold_right
    (fun mv -> Metaset.union (clenv_metas_in_type_of_meta env sigma mv))
    mvs Metaset.empty

let dependent_closure env sigma mvs =
  let rec aux mvs acc =
    Metaset.fold
      (fun mv deps ->
        let metas_of_meta_type = clenv_metas_in_type_of_meta env sigma mv in
        aux metas_of_meta_type (Metaset.union deps metas_of_meta_type))
      mvs acc in
  aux mvs mvs

let undefined_metas evd =
  let fold n b accu = match b with
  | Clval(_,_,typ) -> accu
  | Cltyp (_,typ)  -> n :: accu
  in
  let m = Metamap.fold fold (Evd.meta_list evd) [] in
  List.sort Int.compare m

let clenv_dependent_gen hyps_only ?(iter=true) env sigma concl =
  let all_undefined = undefined_metas sigma in
  let deps_in_concl = (mk_freelisted concl).freemetas in
  let deps_in_hyps = dependent_in_type_of_metas env sigma all_undefined in
  let deps_in_concl =
    if hyps_only && iter then dependent_closure env sigma deps_in_concl
    else deps_in_concl in
  List.filter
    (fun mv ->
      if hyps_only then
        Metaset.mem mv deps_in_hyps && not (Metaset.mem mv deps_in_concl)
      else
        Metaset.mem mv deps_in_hyps || Metaset.mem mv deps_in_concl)
    all_undefined

let clenv_missing ce = clenv_dependent_gen true ce.env ce.evd (clenv_type ce)

(******************************************************************)

let clenv_unify ?(flags=default_unify_flags ()) cv_pb t1 t2 clenv =
  update_clenv_evd clenv (w_unify ~flags clenv.env clenv.evd cv_pb t1 t2)

let clenv_unify_meta_types ?(flags=default_unify_flags ()) clenv =
  update_clenv_evd clenv (w_unify_meta_types ~flags:flags clenv.env clenv.evd)

let clenv_unique_resolver ?(flags=default_unify_flags ()) clenv concl =
  let (hd, _) = decompose_app clenv.evd (whd_nored clenv.env clenv.evd clenv.templtyp.rebus) in
  let clenv = if isMeta clenv.evd hd then clenv_unify_meta_types ~flags clenv else clenv in
  clenv_unify CUMUL ~flags (clenv_type clenv) concl clenv

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
        let f,l = decompose_app_list evd t.rebus in
        match EConstr.kind evd f with
        | Meta mv'' ->
          (match meta_opt_fvalue evd mv'' with
          | Some (c,_) -> match_name c.rebus l
          | None -> None)
        | _ -> None
      else None in
    let id = Option.default id (List.find_map f (Evd.Metamap.bindings (Evd.meta_list evd))) in
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

let clenv_pose_metas_as_evars env sigma dep_mvs =
  let rec fold sigma = function
  | [] -> sigma
  | mv::mvs ->
      let ty = clenv_meta_type env sigma mv in
      (* Postpone the evar-ization if dependent on another meta *)
      (* This assumes no cycle in the dependencies - is it correct ? *)
      if occur_meta sigma ty then fold sigma (mvs@[mv])
      else
        let src = evar_source_of_meta mv sigma in
        let src = adjust_meta_source sigma mv src in
        let (sigma, evar) = new_evar env sigma ~src ty in
        let sigma = clenv_assign env sigma mv evar in
        fold sigma mvs in
  fold sigma dep_mvs

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

let clenv_instantiate ?(flags=fchain_flags ()) ?submetas mv clenv (c, ty) =
  let clenv, c = match submetas with
  | None -> clenv, c
  | Some metas ->
    let evd = meta_merge (Metamap.of_list metas) clenv.evd in
    let clenv = update_clenv_evd clenv evd in
    let c = applist (c, List.map (fun (mv, _) -> mkMeta mv) metas) in
    let map (mv0, submetas0 as arg) =
      if Int.equal mv mv0 then
        (* we never chain more than 2 clenvs *)
        let () = assert (Option.is_empty submetas0) in
        (mv, Some (List.map fst metas))
      else arg
    in
    let metas = List.map map clenv.metas in
    { clenv with metas = metas }, c
  in
  (* unify the type of the template of [nextclenv] with the type of [mv] *)
  let clenv = clenv_unify ~flags CUMUL ty (clenv_meta_type clenv.env clenv.evd mv) clenv in
  let evd = clenv_assign clenv.env clenv.evd mv c in
  update_clenv_evd clenv evd

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
  let deps = Metaset.union (dependent_in_type_of_metas clenv.env clenv.evd mvs) ctyp_mvs in
  List.filter (fun mv -> not (Metaset.mem mv deps)) mvs

let qhyp_eq h1 h2 = match h1, h2 with
| NamedHyp n1, NamedHyp n2 -> lident_eq n1 n2
| AnonHyp i1, AnonHyp i2 -> Int.equal i1 i2
| _ -> false

let check_bindings bl =
  match List.duplicates qhyp_eq (List.map (fun {CAst.v=x} -> fst x) bl) with
    | NamedHyp s :: _ ->
        user_err ?loc:s.CAst.loc
          Pp.(str "The variable " ++ Id.print s.CAst.v ++
              str " occurs more than once in binding list.");
    | AnonHyp n :: _ ->
        user_err
          Pp.(str "The position " ++ int n ++
              str " occurs more than once in binding list.")
    | [] -> ()

let explain_no_such_bound_variable mvl {CAst.v=id;loc} =
  let open Pp in
  let expl = match mvl with
  | [] -> str "(no bound variables at all in the expression)."
  | [id] -> str "(possible name is: " ++ Id.print id ++ str ")."
  | _ -> str "(possible names are: " ++ pr_enum Id.print mvl ++ str ")."
  in
  user_err ?loc (str "No such bound variable " ++ Id.print id ++ spc () ++ expl)

let meta_with_name evd ({CAst.v=id} as lid) =
  let na = Name id in
  let fold n clb (l1, l2 as l) =
    let (na',def) = match clb with
    | Cltyp (na, _) -> (na, false)
    | Clval (na, _, _) -> (na, true)
    in
    if Name.equal na na' then if def then (n::l1,l2) else (n::l1,n::l2)
    else l
  in
  let (mvl, mvnodef) = Evd.Metamap.fold fold (Evd.meta_list evd) ([], []) in
  match List.rev mvnodef, List.rev mvl with
    | _,[]  ->
      let fold n clb l =
        let na = match clb with
          | Cltyp (na, _) -> na
          | Clval (na, _, _) -> na
        in
        if na != Anonymous then Name.get_id na :: l else l
      in
      let mvl = Evd.Metamap.fold fold (Evd.meta_list evd) [] in
      explain_no_such_bound_variable mvl lid
    | (n::_,_|_,n::_) ->
        n

let meta_of_binder clause loc mvs = function
  | NamedHyp s -> meta_with_name clause.evd s
  | AnonHyp n ->
      try List.nth mvs (n-1)
      with (Failure _|Invalid_argument _) ->
        user_err Pp.(str "No such binder.")

let error_already_defined b =
  match b with
    | NamedHyp id ->
        user_err ?loc:id.CAst.loc
          Pp.(str "Binder name \"" ++ Id.print id.CAst.v ++
              str"\" already defined with incompatible value.")
    | AnonHyp n ->
        anomaly
          Pp.(str "Position " ++ int n ++ str" already defined.")

let clenv_unify_binding_type env sigma c t u =
  if isMeta sigma (fst (decompose_app sigma (whd_nored env sigma u))) then
    (* Not enough information to know if some subtyping is needed *)
    CoerceToType, sigma, c
  else
    (* Enough information so as to try a coercion now *)
    try
      let sigma, c = w_coerce_to_type env sigma c t u in
      TypeProcessed, sigma, c
    with
      | PretypeError (_,_,ActualTypeNotCoercible (_,_,
          (NotClean _ | ConversionFailed _))) as e ->
          raise e
      | e when precatchable_exception e ->
          TypeNotProcessed, sigma, c

let clenv_assign_binding clenv k c =
  let k_typ = hnf_constr clenv.env clenv.evd (clenv_meta_type clenv.env clenv.evd k) in
  let c_typ = nf_betaiota clenv.env clenv.evd (Retyping.get_type_of clenv.env clenv.evd c) in
  let status, sigma, c = clenv_unify_binding_type clenv.env clenv.evd c c_typ k_typ in
  update_clenv_evd clenv (meta_assign k (c, (Conv, status)) sigma)

let clenv_match_args bl clenv =
  if List.is_empty bl then
    clenv
  else
    let mvs = clenv_independent clenv in
    check_bindings bl;
    List.fold_left
      (fun clenv {CAst.loc;v=(b,c)} ->
        let k = meta_of_binder clenv loc mvs b in
        match meta_opt_fvalue clenv.evd k with
        | Some (body, _) ->
          if EConstr.eq_constr clenv.evd body.rebus c then clenv
          else error_already_defined b
        | None ->
          clenv_assign_binding clenv k c)
      clenv bl

let error_not_right_number_missing_arguments n =
  user_err
    Pp.(strbrk "Not the right number of missing arguments (expected " ++
        int n ++ str ").")

let clenv_constrain_dep_args hyps_only bl clenv =
  if List.is_empty bl then
    clenv
  else
    let occlist = clenv_dependent_gen hyps_only clenv.env clenv.evd (clenv_type clenv) in
    if Int.equal (List.length occlist) (List.length bl) then
      List.fold_left2 clenv_assign_binding clenv occlist bl
    else
      if hyps_only then
        (* Tolerance for compatibility <= 8.3 *)
        let occlist' = clenv_dependent_gen hyps_only ~iter:false clenv.env clenv.evd (clenv_type clenv) in
        if Int.equal (List.length occlist') (List.length bl) then
          List.fold_left2 clenv_assign_binding clenv occlist' bl
        else
          error_not_right_number_missing_arguments (List.length occlist)
      else
        error_not_right_number_missing_arguments (List.length occlist)

let pose_dependent_evars ?(with_evars=false) env sigma concl =
  let dep_mvs = clenv_dependent_gen false env sigma concl in
  if not (List.is_empty dep_mvs) && not with_evars then
    raise
      (RefinerError (env, sigma, UnresolvedBindings (List.map (meta_name sigma) dep_mvs)));
  clenv_pose_metas_as_evars env sigma dep_mvs

let clenv_pose_dependent_evars ?with_evars clenv =
  let sigma = pose_dependent_evars ?with_evars clenv.env clenv.evd (clenv_type clenv) in
  update_clenv_evd clenv sigma

type case_node = (case_info * EInstance.t * EConstr.t array * EConstr.case_return * EConstr.case_invert * EConstr.t)

module Internal =
struct

open Pp
open Constr
open Termops
open Retyping

let error_unsupported_deep_meta () =
  user_err  (strbrk "Application of lemmas whose beta-iota normal " ++
    strbrk "form contains metavariables deep inside the term is not " ++
    strbrk "supported; try \"refine\" instead.")

type proof =
| RfHole of metavariable
| RfGround of EConstr.t
| RfApp of proof * proof list
| RfProj of Projection.t * proof

exception NonLinear

let is_ground = function
| RfGround _ -> true
| RfHole _ | RfApp _ | RfProj _ -> false

let make_proof env sigma c =
  let metas = ref Metaset.empty in
  let rec make c = match EConstr.kind sigma c with
  | Meta mv ->
    if Metaset.mem mv !metas then raise NonLinear
    else
      let () = metas := Metaset.add mv !metas in
      RfHole mv
  | App (f, args) ->
    let f = make f in
    let args = Array.map_to_list (fun c -> make c) args in
    if is_ground f && List.for_all is_ground args then RfGround c
    else RfApp (f, args)
  | Proj (p, a) ->
    let a = make a in
    if is_ground a then RfGround c else RfProj (p, a)
  | _ ->
    if occur_meta sigma c then error_unsupported_deep_meta ()
    else RfGround c
  in
  try make c
  with NonLinear -> raise (RefinerError (env, sigma, NonLinearProof c))

let rec as_constr = function
| RfHole mv -> EConstr.mkMeta mv
| RfGround c -> c
| RfApp (f, args) -> EConstr.mkApp (as_constr f, Array.map_of_list as_constr args)
| RfProj (p, c) -> EConstr.mkProj (p, as_constr c)

(* Old style mk_goal primitive *)
let mk_goal evars hyps concl =
  (* A goal created that way will not be used by refine and will not
      be shelved. It must not appear as a future_goal, so the future
      goals are restored to their initial value after the evar is
      created. *)
  let evars = Evd.push_future_goals evars in
  let inst = EConstr.identity_subst_val hyps in
  let (evars,evk) =
    Evarutil.new_pure_evar ~src:(Loc.tag Evar_kinds.GoalEvar) ~typeclass_candidate:false hyps evars concl
  in
  let _, evars = Evd.pop_future_goals evars in
  let ev = EConstr.mkEvar (evk,inst) in
  (evk, ev, evars)

let rec mk_refgoals env sigma goalacc conclty trm = match trm with
| RfGround trm ->
  let ty = Retyping.get_type_of env sigma trm in
  (goalacc, ty, sigma, trm)
| RfHole mv ->
  let conclty = match conclty with
  | None -> Typing.meta_type env sigma mv
  | Some conclty -> conclty
  in
  let conclty = nf_betaiota env sigma conclty in
  let hyps = Environ.named_context_val env in
  let (gl,ev,sigma) = mk_goal sigma hyps conclty in
  gl::goalacc, conclty, sigma, ev
| RfApp (f, l) ->
  let (acc',hdty,sigma,applicand) = match f with
  | RfGround f when Termops.is_template_polymorphic_ind env sigma f ->
    let ty =
      (* Template polymorphism of definitions and inductive types *)
      let args, _ = List.split_when (fun p -> not (is_ground p)) l in
      let args = Array.map_of_list as_constr args in
      type_of_global_reference_knowing_parameters env sigma f args
    in
    goalacc, ty, sigma, f
  | _ -> mk_refgoals env sigma goalacc None f
  in
  let ((acc'',conclty',sigma), args) = mk_arggoals env sigma acc' hdty l in
  let ans = EConstr.applist (applicand, args) in
  (acc'', conclty', sigma, ans)
| RfProj (p, c) ->
  let (acc',cty,sigma,c') = mk_refgoals env sigma goalacc None c in
  let c = EConstr.mkProj (p, c') in
  let ty = get_type_of env sigma c in
  (acc',ty,sigma,c)

and mk_arggoals env sigma goalacc funty allargs =
  let foldmap (goalacc, funty, sigma) harg =
    let t = whd_all env sigma funty in
    match EConstr.kind sigma t with
    | Prod (_, c1, b) ->
      let (acc, hargty, sigma, arg) = mk_refgoals env sigma goalacc (Some c1) harg in
      (acc, EConstr.Vars.subst1 arg b, sigma), arg
    | _ ->
      raise (RefinerError (env,sigma,CannotApply (t, as_constr harg)))
  in
  List.fold_left_map foldmap (goalacc, funty, sigma) allargs

let treat_case env sigma ci lbrty accu =
  let open EConstr in
  let fold (sigma, accu) (ctx, ty) =
    let open Context.Rel.Declaration in
    let brctx = Array.of_list (List.rev_map get_annot ctx) in
    let args = Context.Rel.instance mkRel 0 ctx in
    (* TODO: tweak this to prevent dummy β-cuts *)
    let ty = nf_betaiota env sigma (it_mkProd_or_LetIn ty ctx) in
    let hyps = Environ.named_context_val env in
    let (gl, ev, sigma) = mk_goal sigma hyps ty in
    let br' = mkApp (ev, args) in
    (sigma, gl :: accu), (brctx, br')
  in
  Array.fold_left_map fold (sigma, accu) lbrty

let std_refine env sigma cl r =
  let r = make_proof env sigma r in
  let (sgl, _, sigma, trm) = mk_refgoals env sigma [] (Some cl) r in
  (sigma, sgl, trm)

(***********************************************)
(* find appropriate names for pattern variables. Useful in the Case
   and Inversion (case_then_using et case_nodep_then_using) tactics. *)

type refiner_kind =
| Std of clbinding Metamap.t * EConstr.t
| Case of case_node * (EConstr.rel_context * EConstr.t) array

let refiner_gen is_case =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let st = Proofview.Goal.state gl in
  let cl = Proofview.Goal.concl gl in
  let (sigma, sgl, c) = match is_case with
  | Case ((ci, u, pms, p, iv, c), branches) ->
    let ((sigma, accu), lf) = treat_case env sigma ci branches [] in
    let ans = EConstr.mkCase (ci, u, pms, p, iv, c, lf) in
    (sigma, accu, ans)
  | Std (metas, r) ->
    let sigma = Evd.meta_merge metas sigma in
    std_refine env sigma cl r
  in
  let sigma = Evd.clear_metas sigma in
  let map gl = Proofview.goal_with_state gl st in
  let sgl = List.rev_map map sgl in
  let evk = Proofview.Goal.goal gl in
  (* Check that the goal itself does not appear in the refined term *)
  let _ =
    if not (Evarutil.occur_evar_upto sigma evk c) then ()
    else Pretype_errors.error_occur_check env sigma evk c
  in
  let sigma = Evd.define evk c sigma in
  Proofview.Unsafe.tclEVARS sigma <*>
  Proofview.Unsafe.tclSETGOALS sgl
  end

let refiner clenv =
  let r = clenv_value clenv in
  let metas = Evd.meta_list clenv.evd in
  refiner_gen (Std (metas, r))

end

open Unification

let dft = default_unify_flags

let res_pf ?(with_evars=false) ?(with_classes=true) ?(flags=dft ()) clenv =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let clenv = clenv_unique_resolver ~flags clenv concl in
    let sigma = pose_dependent_evars ~with_evars clenv.env clenv.evd (clenv_type clenv) in
    let sigma =
      if with_classes then
        let sigma =
          Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
            ~fail:(not with_evars) clenv.env sigma
        in
        (* After an apply, all the subgoals including those dependent shelved ones are in
          the hands of the user and resolution won't be called implicitely on them. *)
        Typeclasses.make_unresolvables (fun x -> true) sigma
      else sigma
    in
    let clenv = update_clenv_evd clenv sigma in
    let metas = Evd.meta_list clenv.evd in
    let r = clenv_value clenv in
    Proofview.tclTHEN
      (Proofview.Unsafe.tclEVARS (Evd.clear_metas sigma))
      (Internal.refiner_gen (Std (metas, r)))
  end

type case_analysis =
| RealCase of case_node
| PrimitiveEta of EConstr.t array

let build_case_analysis env sigma (ind, u) params pred indices indarg dep knd =
  let open Inductiveops in
  let open Context.Rel.Declaration in
  (* Assumes that the arguments do not contain free rels *)
  let indf = make_ind_family ((ind, EConstr.Unsafe.to_instance u), Array.map_to_list EConstr.Unsafe.to_constr params) in
  let projs = get_projections env ind in
  let relevance = Sorts.relevance_of_sort knd in

  let pnas, deparsign =
    let arsign = get_arity env indf in
    let r = Inductiveops.relevance_of_inductive_family env indf in
    let depind = build_dependent_inductive env indf in
    let deparsign = LocalAssum (make_annot Anonymous r,depind)::arsign in
    let set_names env l =
      let ident_hd env ids t na =
        let na = Namegen.named_hd env (Evd.from_env env) (EConstr.of_constr t) na in
        Namegen.next_name_away na ids
      in
      let fold d (ids, l) =
        let id = ident_hd env ids (get_type d) (get_name d) in
        (Id.Set.add id ids, set_name (Name id) d :: l)
      in
      snd (List.fold_right fold l (Id.Set.empty,[]))
    in
    let pctx =
      let deparsign = set_names env deparsign in
      if dep then deparsign
      else LocalAssum (make_annot Anonymous r, depind) :: List.tl deparsign
    in
    let pnas = Array.of_list (List.rev_map get_annot pctx) in
    pnas, deparsign
  in

  match projs with
  | None ->
    let ci = make_case_info env ind relevance RegularStyle in
    let pbody =
      mkApp
        (pred,
          if dep then Context.Rel.instance mkRel 0 deparsign
          else Context.Rel.instance mkRel 1 (List.tl deparsign)) in
    let iv =
      if Typeops.should_invert_case env ci then CaseInvert { indices = indices }
      else NoInvert
    in
    RealCase (ci, u, params, (pnas, pbody), iv, indarg)
  | Some ps ->
    let args = Array.map (fun p -> mkProj (Projection.make p true, indarg)) ps in
    PrimitiveEta args

let case_pf ?(with_evars=false) ~dep (indarg, typ) =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let sigma = clear_metas sigma in
  (* Extract inductive data from the argument. *)
  let hd, args = decompose_app sigma typ in
  (* Workaround to #5645: reduce_to_atomic_ind produces ill-typed terms *)
  let sigma, _ = Typing.checked_appvect env sigma hd args in
  let ind, u = destInd sigma hd in
  let u0 = EInstance.kind sigma u in
  let s = ESorts.kind sigma @@ Retyping.get_sort_of env sigma concl in
  let (mib, mip) = Inductive.lookup_mind_specif env ind in
  let params, indices = Array.chop mib.mind_nparams args in

  let () = Indrec.check_valid_elimination env (ind, u0) ~dep (Sorts.family s) in

  let indf =
    let params = EConstr.Unsafe.to_constr_array params in
    Inductiveops.make_ind_family ((ind, u0), Array.to_list params)
  in

  (* Extract the return clause using unification with the conclusion *)
  let typP = Inductiveops.make_arity env sigma dep indf (ESorts.make s) in
  let mvP = new_meta () in
  let sigma = meta_declare mvP typP sigma in
  let depargs = Array.append indices [|indarg|] in
  let templtyp = if dep then mkApp (mkMeta mvP, depargs) else mkApp (mkMeta mvP, indices) in
  let flags = elim_flags () in
  let sigma = w_unify_meta_types ~flags env sigma in
  let sigma = w_unify ~flags env sigma CUMUL templtyp concl in
  let pred = meta_instance env sigma (mk_freelisted (mkMeta mvP)) in

  (* Create the branch types *)
  let branches =
    let open Inductiveops in
    let constrs = get_constructors env indf in
    let get_branch cs =
      let base = mkApp (pred, EConstr.of_constr_array cs.cs_concl_realargs) in
      let argctx = EConstr.of_rel_context cs.cs_args in
      if dep then
        let argctx = Namegen.name_context env sigma argctx in
        (argctx, applist (base, [EConstr.of_constr @@ build_dependent_constructor cs]))
      else
        (argctx, base)
    in
    Array.map get_branch constrs
  in

  (* Build the case node proper *)
  let body = build_case_analysis env sigma (ind, u) params pred indices indarg dep s in

  (* After an apply, all the subgoals including those dependent shelved ones are in
    the hands of the user and resolution won't be called implicitely on them. *)
  let sigma =
    Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
      ~fail:(not with_evars) env sigma
  in
  let sigma = Typeclasses.make_unresolvables (fun x -> true) sigma in
  (* Note that the environment rel context does not matter for betaiota *)
  let rec nf_betaiota c = EConstr.map sigma nf_betaiota (whd_betaiota env sigma c) in
  (* Call the legacy refiner on the result *)
  let arg = match body with
  | RealCase (ci, u, pms, p, iv, c) ->
    let c = nf_betaiota c in
    let pms = Array.map nf_betaiota pms in
    let p = on_snd nf_betaiota p in
    Internal.Case ((ci, u, pms, p, iv, c), branches)
  | PrimitiveEta args ->
    let mv = new_meta () in
    let (ctx, t) = branches.(0) in
    let sigma = meta_declare mv (it_mkProd_or_LetIn t ctx) sigma in
    let metas = Evd.meta_list sigma in
    Internal.Std (metas, mkApp (mkMeta mv, Array.map nf_betaiota args))
  in
  Proofview.tclTHEN
    (Proofview.Unsafe.tclEVARS (Evd.clear_metas sigma))
    (Internal.refiner_gen arg)
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
let unify ?(flags=fail_quick_unif_flags) ~cv_pb m =
  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.pf_env gl in
    let n = Tacmach.pf_concl gl in
    let evd = clear_metas (Tacmach.project gl) in
    try
      let evd' = w_unify env evd cv_pb ~flags m n in
        Proofview.Unsafe.tclEVARSADVANCE evd'
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
      let clause = mk_clenv_from_env env sigma n (c, t) in clenv_match_args lbind clause
  | NoBindings ->
      mk_clenv_from_env env sigma n (c,t)

let make_clenv_binding_apply env sigma n = make_clenv_binding_gen true n env sigma
let make_clenv_binding env sigma = make_clenv_binding_gen false None env sigma

(****************************************************************)
(* Pretty-print *)

let pr_clenv clenv =
  let prc = Termops.Internal.print_constr_env clenv.env clenv.evd in
  Pp.(h (str"TEMPL: " ++ prc clenv.templval ++
         str" : " ++ prc clenv.templtyp.rebus ++ fnl () ++
         pr_evar_map (Some 2) clenv.env clenv.evd))
