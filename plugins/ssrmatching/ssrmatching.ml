(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Ltac_plugin
open Names
open Pp
open Genarg
open Context
module CoqConstr = Constr
open CoqConstr
open Libnames
open Tactics
open Termops
open Glob_term
open Util
open Evd
open Tacexpr
open Tacinterp
open Pretyping
open Ppconstr
open Printer
open Namegen
open Evar_kinds
open Constrexpr
open Constrexpr_ops

type ssrtermkind = | InParens | WithAt | NoFlag | Cpattern

let errorstrm = CErrors.user_err
let loc_error loc msg = CErrors.user_err ?loc (str msg)
let ppnl = Feedback.msg_info

(* 0 cost pp function. Active only if env variable SSRDEBUG is set *)
(* or if SsrDebug is Set                                                  *)
let pp_ref = ref (fun _ -> ())
let ssr_pp s = Feedback.msg_debug (str"SSR: "++Lazy.force s)
let _ =
  try ignore(Sys.getenv "SSRMATCHINGDEBUG"); pp_ref := ssr_pp
  with Not_found -> ()
let debug b =
  if b then pp_ref := ssr_pp else pp_ref := fun _ -> ()
let _ =
  Goptions.declare_bool_option
    { Goptions.optkey   = ["Debug";"SsrMatching"];
      Goptions.optdepr  = false;
      Goptions.optread  = (fun _ -> !pp_ref == ssr_pp);
      Goptions.optwrite = debug }
let pp s = !pp_ref s

(** Utils *)(* {{{ *****************************************************************)
let env_size env = List.length (Environ.named_context env)
let safeDestApp sigma c =
  match EConstr.kind sigma c with App (f, a) -> f, a | _ -> c, [| |]
(* Toplevel constr must be globalized twice ! *)
let glob_constr ist genv sigma t = match t, ist with
  | (_, Some ce), Some ist ->
    let vars = Id.Map.fold (fun x _ accu -> Id.Set.add x accu) ist.lfun Id.Set.empty in
    let ltacvars = { Constrintern.empty_ltac_sign with Constrintern.ltac_vars = vars } in
    Constrintern.intern_gen WithoutTypeConstraint ~ltacvars:ltacvars genv sigma ce
  | (rc, None), _ -> rc
  | (_, Some _), None -> CErrors.anomaly Pp.(str"glob_constr: term with no ist")

(* Term printing utilities functions for deciding bracketing.  *)
let pr_paren prx x = hov 1 (str "(" ++ prx x ++ str ")")
(* String lexing utilities *)
let skip_wschars s =
  let rec loop i = match s.[i] with '\n'..' ' -> loop (i + 1) | _ -> i in loop
(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let guard_term kind s i = match s.[i] with
  | '(' -> false
  | '{' | '/' | '=' -> true
  | _ -> kind = InParens
(* The call 'guard s i' should return true if the contents of s *)
(* starting at i need bracketing to avoid ambiguities.          *)
let pr_guarded guard prc c =
  let s = Pp.string_of_ppcmds (prc c) ^ "$" in
  if guard s (skip_wschars s 0) then pr_paren prc c else prc c
(* More sensible names for constr printers *)
let with_global_env_evm f x =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  f env sigma x
let prl_glob_constr = with_global_env_evm pr_lglob_constr_env
let pr_glob_constr = with_global_env_evm pr_glob_constr_env
let prl_constr_expr = pr_lconstr_expr
let pr_constr_expr = pr_constr_expr
let prl_glob_constr_and_expr env sigma = function
  | _, Some c -> prl_constr_expr env sigma c
  | c, None -> prl_glob_constr c
let pr_glob_constr_and_expr env sigma = function
  | _, Some c -> pr_constr_expr env sigma c
  | c, None -> pr_glob_constr c

(** Adding a new uninterpreted generic argument type *)
let add_genarg tag pr =
  let wit = Genarg.make0 tag in
  let tag = Geninterp.Val.create tag in
  let glob ist x = (ist, x) in
  let subst _ x = x in
  let interp ist x = Ftactic.return (Geninterp.Val.Dyn (tag, x)) in
  let gen_pr env sigma _ _ _ = pr env sigma in
  let () = Genintern.register_intern0 wit glob in
  let () = Genintern.register_subst0 wit subst in
  let () = Geninterp.register_interp0 wit interp in
  let () = Geninterp.register_val0 wit (Some (Geninterp.Val.Base tag)) in
  Pptactic.declare_extra_genarg_pprule wit gen_pr gen_pr gen_pr;
  wit

(** Constructors for constr_expr *)
let isCVar   = function { CAst.v = CRef (qid,_) } -> qualid_is_ident qid | _ -> false
let destCVar = function
  | { CAst.v = CRef (qid,_) } when qualid_is_ident qid ->
    qualid_basename qid
  | _ ->
    CErrors.anomaly (str"not a CRef.")
let isGLambda c = match DAst.get c with GLambda (Name _, _, _, _) -> true | _ -> false
let destGLambda c = match DAst.get c with GLambda (Name id, _, _, c) -> (id, c)
  | _ -> CErrors.anomaly (str "not a GLambda")
let isGHole c = match DAst.get c with GHole _ -> true | _ -> false
let mkCHole ~loc = CAst.make ?loc @@ CHole (None, IntroAnonymous, None)
let mkCLambda ?loc name ty t = CAst.make ?loc @@
   CLambdaN ([CLocalAssum([CAst.make ?loc name], Default Explicit, ty)], t)
let mkCLetIn ?loc name bo t = CAst.make ?loc @@
   CLetIn ((CAst.make ?loc name), bo, None, t)
let mkCCast ?loc t ty = CAst.make ?loc @@ CCast (t, DEFAULTcast, ty)

(** Constructors for rawconstr *)
let mkRHole = DAst.make @@ GHole (InternalHole, IntroAnonymous, None)
let mkRApp f args = if args = [] then f else DAst.make @@ GApp (f, args)
let mkRCast rc rt =  DAst.make @@ GCast (rc, DEFAULTcast, rt)
let mkRLambda n s t = DAst.make @@ GLambda (n, Explicit, s, t)

(* }}} *)

exception NoProgress

(** Unification procedures.                                *)

(* To enforce the rigidity of the rooted match we always split  *)
(* top applications, so the unification procedures operate on   *)
(* arrays of patterns and terms.                                *)
(* We perform three kinds of unification:                       *)
(*  EQ: exact conversion check                                  *)
(*  FO: first-order unification of evars, without conversion    *)
(*  HO: higher-order unification with conversion                *)
(* The subterm unification strategy is to find the first FO     *)
(* match, if possible, and the first HO match otherwise, then   *)
(* compute all the occurrences that are EQ matches for the      *)
(* relevant subterm.                                            *)
(*   Additional twists:                                         *)
(*    - If FO/HO fails then we attempt to fill evars using      *)
(*      typeclasses before raising an outright error. We also   *)
(*      fill typeclasses even after a successful match, since   *)
(*      beta-reduction and canonical instances may leave        *)
(*      undefined evars.                                        *)
(*    - We do postchecks to rule out matches that are not       *)
(*      closed or that assign to a global evar; these can be    *)
(*      disabled for rewrite or dependent family matches.       *)
(*    - We do a full FO scan before turning to HO, as the FO    *)
(*      comparison can be much faster than the HO one.          *)

let unif_EQ env sigma p c =
  let env = Environ.set_universes (Evd.universes sigma) env in
  Reductionops.is_conv env sigma p c

let unif_EQ_args env sigma pa a =
  let n = Array.length pa in
  let rec loop i = (i = n) || unif_EQ env sigma pa.(i) a.(i) && loop (i + 1) in
  loop 0

let unif_HO env ise p c =
  try Evarconv.unify_delay env ise p c
  with Evarconv.UnableToUnify(ise, err) ->
    raise Pretype_errors.(PretypeError(env,ise,CannotUnify(p,c,Some err)))

let unif_HO_args env ise0 pa i ca =
  let n = Array.length pa in
  let rec loop ise j =
    if j = n then ise else loop (unif_HO env ise pa.(j) (ca.(i + j))) (j + 1) in
  loop ise0 0

(* FO unification should boil down to calling w_unify with no_delta, but  *)
(* alas things are not so simple: w_unify does partial type-checking,     *)
(* which breaks down when the no-delta flag is on (as the Coq type system *)
(* requires full convertibility. The workaround here is to convert all    *)
(* evars into metas, since 8.2 does not TC metas. This means some lossage *)
(* for HO evars, though hopefully Miller patterns can pick up some of     *)
(* those cases, and HO matching will mop up the rest.                     *)
let flags_FO env =
  let oracle = Environ.oracle env in
  let ts = Conv_oracle.get_transp_state oracle in
  let flags =
    { (Unification.default_no_delta_unify_flags ts).Unification.core_unify_flags
      with
        Unification.modulo_conv_on_closed_terms = None;
        Unification.modulo_eta = true;
        Unification.modulo_betaiota = true;
        Unification.modulo_delta_types = ts }
  in
  { Unification.core_unify_flags = flags;
    Unification.merge_unify_flags = flags;
    Unification.subterm_unify_flags = flags;
    Unification.allow_K_in_toplevel_higher_order_unification = false;
    Unification.resolve_evars =
      (Unification.default_no_delta_unify_flags ts).Unification.resolve_evars
  }
let unif_FO env ise p c =
  Unification.w_unify env ise Reduction.CONV ~flags:(flags_FO env) p c

(* Perform evar substitution in main term and prune substitution. *)
let nf_open_term sigma0 ise c =
  let open EConstr in
  let s' = ref sigma0 in
  let rec nf c' = match EConstr.kind ise c' with
  | Evar ex ->
    let k, a = ex in let a' = List.map nf a in
    if not (Evd.mem !s' k) then
      s' := Evd.add !s' k (Evarutil.nf_evar_info ise (Evd.find ise k));
    mkEvar (k, a')
  | _ -> map ise nf c' in
  let copy_def k _ () = match Evd.evar_body (Evd.find ise k) with
  | Evar_defined c' ->
    let c' = nf c' in
    s' := Evd.define k c' !s'
  | _ -> () in
  let c' = nf c in
  let _ = Evd.fold_undefined copy_def sigma0 () in
  let changed = sigma0 != !s' in
  changed, !s', Evd.evar_universe_context ise, c'

let unif_end ?(solve_TC=true) env sigma0 ise0 pt ok =
  let ise = Evarconv.solve_unif_constraints_with_heuristics env ise0 in
  let tcs = Evd.get_typeclass_evars ise in
  let c, s, uc, t = nf_open_term sigma0 ise pt in
  let ise1 = create_evar_defs s in
  let ise1 = Evd.set_typeclass_evars ise1 (Evar.Set.filter (fun ev -> Evd.is_undefined ise1 ev) tcs) in
  let ise1 = Evd.set_universe_context ise1 uc in
  let ise2 =
    if solve_TC then Typeclasses.resolve_typeclasses ~fail:true env ise1
    else ise1 in
  if not (ok ise) then raise NoProgress else
  if ise2 == ise1 then (c, s, uc, t)
  else
    let c, s, uc', t = nf_open_term sigma0 ise2 t in
    c, s, UState.union uc uc', t

let unify_HO env sigma0 t1 t2 =
  let sigma = unif_HO env sigma0 t1 t2 in
  let _, sigma, uc, _ = unif_end ~solve_TC:false env sigma0 sigma t2 (fun _ -> true) in
  Evd.set_universe_context sigma uc

(* This is what the definition of iter_constr should be... *)
let iter_constr_LR sigma f c = match EConstr.kind sigma c with
  | Evar (k, a) -> List.iter f a
  | Cast (cc, _, t) -> f cc; f t
  | Prod (_, t, b) | Lambda (_, t, b)  -> f t; f b
  | LetIn (_, v, t, b) -> f v; f t; f b
  | App (cf, a) -> f cf; Array.iter f a
  | Case (_, _, pms, (_, p), iv, v, b) ->
    f v; Array.iter f pms; f p; iter_invert f iv; Array.iter (fun (_, c) -> f c) b
  | Fix (_, (_, t, b)) | CoFix (_, (_, t, b)) ->
    for i = 0 to Array.length t - 1 do f t.(i); f b.(i) done
  | Proj(_,a) -> f a
  | Array(_u,t,def,ty) -> Array.iter f t; f def; f ty
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _
     | Int _ | Float _) -> ()

(* The comparison used to determine which subterms matches is KEYED        *)
(* CONVERSION. This looks for convertible terms that either have the same  *)
(* same head constant as pat if pat is an application (after beta-iota),   *)
(* or start with the same constr constructor (esp. for LetIn); this is     *)
(* disregarded if the head term is let x := ... in x, and casts are always *)
(* ignored and removed).                                                   *)
(* Record projections get special treatment: in addition to the projection *)
(* constant itself, ssreflect also recognizes head constants of canonical  *)
(* projections.                                                            *)

exception NoMatch
type ssrdir = L2R | R2L
let pr_dir_side = function L2R -> str "LHS" | R2L -> str "RHS"
let inv_dir = function L2R -> R2L | R2L -> L2R


type pattern_class =
  | KpatFixed
  | KpatConst
  | KpatEvar of Evar.t
  | KpatLet
  | KpatLam
  | KpatRigid
  | KpatFlex
  | KpatProj of Constant.t

type tpattern = {
  up_k : pattern_class;
  up_FO : EConstr.t;
  up_f : EConstr.t;
  up_a : EConstr.t array;
  up_t : EConstr.t;                      (* equation proof term or matched term *)
  up_dir : ssrdir;                    (* direction of the rule *)
  up_ok : EConstr.t -> evar_map -> bool; (* progress test for rewrite *)
  }

let all_ok _ _ = true

let proj_nparams c =
  try 1 + Structures.Structure.projection_nparams c
  with Not_found -> 0

let isRigid sigma c = match EConstr.kind sigma c with
  | (Prod _ | Sort _ | Lambda _ | Case _ | Fix _ | CoFix _| Int _
    | Float _ | Array _) -> true
  | (Rel _ | Var _ | Meta _ | Evar (_, _) | Cast (_, _, _) | LetIn (_, _, _, _)
    | App (_, _) | Const (_, _) | Ind ((_, _), _) | Construct (((_, _), _), _)
    | Proj (_, _)) -> false


let hole_var = mkVar (Id.of_string "_")
let pr_constr_pat env sigma c0 =
  let rec wipe_evar c =
    if isEvar c then hole_var else map wipe_evar c in
  pr_constr_env env sigma (wipe_evar c0)

let ehole_var = EConstr.mkVar (Id.of_string "_")
let pr_econstr_pat env sigma c0 =
  let rec wipe_evar c = let open EConstr in
    if isEvar sigma c then ehole_var else map sigma wipe_evar c in
  let dummy_decl =
    let dummy_prod = mkProd (make_annot Anonymous Sorts.Relevant,mkProp,mkProp) in
    let na = make_annot (EConstr.destVar sigma ehole_var) Sorts.Relevant in
    Context.Named.Declaration.(LocalAssum (na, dummy_prod)) in
  let env = Environ.push_named dummy_decl env in
  pr_econstr_env env sigma (wipe_evar c0)

(* Turn (new) evars into metas *)
let evars_for_FO ~hack ~rigid env (ise0:evar_map) c0 =
  let open EConstr in
  let ise = ref ise0 in
  let sigma = ref ise0 in
  let nenv = env_size env + if hack then 1 else 0 in
  let rec put c = match EConstr.kind !sigma c with
  | Evar (k, a) ->
    if rigid k then map !sigma put c else
    let evi = Evd.find !sigma k in
    let dc = List.firstn (max 0 (List.length a - nenv)) (evar_filtered_context evi) in
    let abs_dc (d, c) = function
    | Context.Named.Declaration.LocalDef (x, b, t) ->
        d, mkNamedLetIn x (put b) (put t) c
    | Context.Named.Declaration.LocalAssum (x, t) ->
        mkVar x.binder_name :: d, mkNamedProd x (put t) c in
    let a, t =
      Context.Named.fold_inside abs_dc ~init:([], put evi.evar_concl) dc
    in
    let m = Evarutil.new_meta () in
    ise := meta_declare m t !ise;
    sigma := Evd.define k (applistc (mkMeta m) a) !sigma;
    put c
  | _ -> map !sigma put c in
  let c1 = put c0 in !ise, c1

(* Compile a match pattern from a term; t is the term to fill. *)
(* p_origin can be passed to obtain a better error message     *)
let mk_tpattern ?p_origin ?(hack=false) ?(ok = all_ok) ~rigid env (ise, t) dir p =
  let open EConstr in
  let k, f, a =
    let f, a = Reductionops.whd_betaiota_stack env ise p in
    match EConstr.kind ise f with
    | Const (p,_) ->
      let np = proj_nparams p in
      if np = 0 || np > List.length a then KpatConst, f, a else
      let a1, a2 = List.chop np a in KpatProj p, (applistc f a1), a2
    | Proj (p,arg) -> KpatProj (Projection.constant p), f, a
    | Var _ | Ind _ | Construct _ -> KpatFixed, f, a
    | Evar (k, _) ->
      if rigid k then KpatEvar k, f, a else
      if a <> [] then KpatFlex, f, a else
      (match p_origin with None -> CErrors.user_err Pp.(str "indeterminate pattern")
      | Some (dir, rule) ->
        errorstrm (str "indeterminate " ++ pr_dir_side dir
          ++ str " in " ++ pr_econstr_pat env ise rule))
    | LetIn (_, v, _, b) ->
      if b <> mkRel 1 then KpatLet, f, a else KpatFlex, v, a
    | Lambda _ -> KpatLam, f, a
    | _ -> KpatRigid, f, a in
  let aa = Array.of_list a in
  let ise', p' = evars_for_FO ~hack ~rigid env ise (mkApp (f, aa)) in
  ise',
  { up_k = k; up_FO = p'; up_f = f;
    up_a = aa; up_ok = ok; up_dir = dir; up_t = t}

(* Specialize a pattern after a successful match: assign a precise head *)
(* kind and arity for Proj and Flex patterns.                           *)
let ungen_upat lhs (c, sigma, uc, t) u =
  let f, a = safeDestApp sigma lhs in
  let k = match kind (EConstr.Unsafe.to_constr f) with
  | Var _ | Ind _ | Construct _ -> KpatFixed
  | Const _ -> KpatConst
  | Evar (k, _) -> if is_defined sigma k then raise NoMatch else KpatEvar k
    (* FIXME: why do we observe defined evars here? *)
  | LetIn _ -> KpatLet
  | Lambda _ -> KpatLam
  | _ -> KpatRigid in
  c, sigma, uc, {u with up_k = k; up_FO = lhs; up_f = f; up_a = a; up_t = t}

let nb_cs_proj_args ise pc f u =
  let open EConstr in
  let open Structures in
  let open ValuePattern in
  let na k =
    let open CanonicalSolution in
    let _, { cvalue_arguments } = find (Global.env()) ise (GlobRef.ConstRef pc, k) in
    List.length cvalue_arguments in
  let nargs_of_proj t = match EConstr.kind ise t with
      | App(_,args) -> Array.length args
      | Proj _ -> 0 (* if splay_app calls expand_projection, this has to be
                       the number of arguments including the projected *)
      | _ -> assert false in
  try match EConstr.kind ise f with
  | Prod _ -> na Prod_cs
  | Sort s -> na (Sort_cs (Sorts.family (ESorts.kind ise s)))
  | Const (c',_) when Constant.CanOrd.equal c' pc -> nargs_of_proj u.up_f
  | Proj (c',_) when Constant.CanOrd.equal (Names.Projection.constant c') pc -> nargs_of_proj u.up_f
  | Var _ | Ind _ | Construct _ | Const _ -> na (Const_cs (fst @@ destRef ise f))
  | _ -> -1
  with Not_found -> -1

let isEvar_k ise k f =
  match EConstr.kind ise f with Evar (k', _) -> k = k' | _ -> false

let nb_args sigma c =
  match EConstr.kind sigma c with App (_, a) -> Array.length a | _ -> 0

let mkSubArg i a =
  if i = Array.length a then a else Array.sub a 0 i
let mkSubApp f i a =
  let open EConstr in
  if i = 0 then f else mkApp (f, mkSubArg i a)

let splay_app ise =
  let rec loop c a = match EConstr.kind ise c with
  | App (f, a') -> loop f (Array.append a' a)
  | Cast (c', _, _) -> loop c' a
  | _ -> c, a in
  fun c -> match EConstr.kind ise c with
  | App (f, a) -> loop f a
  | Cast _ | Evar _ -> loop c [| |]
  | _ -> c, [| |]

let filter_upat sigma i0 f n u fpats =
  let open EConstr in
  let na = Array.length u.up_a in
  if n < na then fpats else
  let np = match u.up_k with
  | KpatConst when eq_constr_nounivs sigma u.up_f f -> na
  | KpatFixed when eq_constr_nounivs sigma u.up_f f -> na
  | KpatEvar k when isEvar_k sigma k f -> na
  | KpatLet when isLetIn sigma f -> na
  | KpatLam when isLambda sigma f -> na
  | KpatRigid when isRigid sigma f -> na
  | KpatFlex -> na
  | KpatProj pc ->
    let np = na + nb_cs_proj_args sigma pc f u in if n < np then -1 else np
  | _ -> -1 in
  if np < na then fpats else
  let () = if !i0 < np then i0 := n in (u, np) :: fpats

let eq_prim_proj sigma c t = match EConstr.kind sigma t with
  | Proj(p,_) -> Constant.CanOrd.equal (Projection.constant p) c
  | _ -> false

let filter_upat_FO sigma i0 f n u fpats =
  let open EConstr in
  let np = nb_args sigma u.up_FO in
  if n < np then fpats else
  let ok = match u.up_k with
  | KpatConst -> eq_constr_nounivs sigma u.up_f f
  | KpatFixed -> eq_constr_nounivs sigma u.up_f f
  | KpatEvar k -> isEvar_k sigma k f
  | KpatLet -> isLetIn sigma f
  | KpatLam -> isLambda sigma f
  | KpatRigid -> isRigid sigma f
  | KpatProj pc -> eq_constr sigma f (mkConst pc) || eq_prim_proj sigma pc f
  | KpatFlex -> i0 := n; true in
  if ok then begin if !i0 < np then i0 := np; (u, np) :: fpats end else fpats

exception FoundUnif of (bool * evar_map * UState.t * tpattern)
(* Note: we don't update env as we descend into the term, as the primitive *)
(* unification procedure always rejects subterms with bound variables.     *)

let dont_impact_evars_in sigma0 cl =
  let evs_in_cl = Evd.evars_of_term sigma0 cl in
  fun sigma -> Evar.Set.for_all (fun k ->
    try let _ = Evd.find_undefined sigma k in true
    with Not_found -> false) evs_in_cl

(* We are forced to duplicate code between the FO/HO matching because we    *)
(* have to work around several kludges in unify.ml:                         *)
(*  - w_unify drops into second-order unification when the pattern is an    *)
(*    application whose head is a meta.                                     *)
(*  - w_unify tries to unify types without subsumption when the pattern     *)
(*    head is an evar or meta (e.g., it fails on ?1 = nat when ?1 : Type).  *)
(*  - w_unify expands let-in (zeta conversion) eagerly, whereas we want to  *)
(*    match a head let rigidly.                                             *)
let match_upats_FO upats env sigma0 ise orig_c =
  let dont_impact_evars = dont_impact_evars_in sigma0 orig_c in
  let rec loop c =
    let f, a = splay_app ise c in let i0 = ref (-1) in
    let fpats =
      List.fold_right (filter_upat_FO ise i0 f (Array.length a)) upats [] in
    while !i0 >= 0 do
      let i = !i0 in i0 := -1;
      let c' = mkSubApp f i a in
      let one_match (u, np) =
        let open EConstr in
         let skip =
           if i <= np then i < np else
           if u.up_k == KpatFlex then begin i0 := i - 1; false end else
           begin if !i0 < np then i0 := np; true end in
         if skip || not (EConstr.Vars.closed0 ise c') then () else try
           let _ = match u.up_k with
           | KpatFlex ->
             let kludge v = mkLambda (make_annot Anonymous Sorts.Relevant, mkProp, v) in
             unif_FO env ise (kludge u.up_FO) (kludge c')
           | KpatLet ->
             let kludge vla =
               let vl, a = safeDestApp ise vla in
               let x, v, t, b = destLetIn ise vl in
               mkApp (mkLambda (x, t, b), Array.cons v a) in
             unif_FO env ise (kludge u.up_FO) (kludge c')
           | _ -> unif_FO env ise u.up_FO c' in
           let ise' = (* Unify again using HO to assign evars *)
             let p = mkApp (u.up_f, u.up_a) in
             try unif_HO env ise p c' with e when CErrors.noncritical e -> raise NoMatch in
           let lhs = mkSubApp f i a in
           let pt' = unif_end env sigma0 ise' u.up_t (u.up_ok lhs) in
           raise (FoundUnif (ungen_upat lhs pt' u))
       with FoundUnif (_, s,_,_) as sig_u when dont_impact_evars s -> raise sig_u
       | Not_found -> CErrors.anomaly (str"incomplete ise in match_upats_FO.")
       | e when CErrors.noncritical e -> () in
    List.iter one_match fpats
  done;
  iter_constr_LR ise loop f; Array.iter loop a in
  try loop orig_c with Invalid_argument _ -> CErrors.anomaly (str"IN FO.")


let match_upats_HO ~on_instance upats env sigma0 ise c =
 let dont_impact_evars = dont_impact_evars_in sigma0 c in
 let it_did_match = ref false in
 let failed_because_of_TC = ref false in
 let rec aux upats env sigma0 ise c =
  let f, a = splay_app ise c in let i0 = ref (-1) in
  let fpats =
    List.fold_right (filter_upat ise i0 f (Array.length a)) upats []
  in
  while !i0 >= 0 do
    let i = !i0 in i0 := -1;
    let one_match (u, np) =
      let skip =
        if i <= np then i < np else
        if u.up_k == KpatFlex then begin i0 := i - 1; false end else
        begin if !i0 < np then i0 := np; true end in
      if skip then () else try
        let ise' = match u.up_k with
        | KpatFixed | KpatConst -> ise
        | KpatEvar _ ->
          let open EConstr in
          let _, pka = destEvar ise u.up_f and _, ka = destEvar ise f in
          let fold ise pk k = unif_HO env ise pk k in
          List.fold_left2 fold ise pka ka
        | KpatLet ->
          let open EConstr in
          let x, v, t, b = destLetIn ise f in
          let _, pv, _, pb = destLetIn ise u.up_f in
          let ise' = unif_HO env ise pv v in
          unif_HO
            (EConstr.push_rel (Context.Rel.Declaration.LocalAssum(x, t)) env)
            ise' pb b
        | KpatFlex | KpatProj _ ->
          unif_HO env ise u.up_f (mkSubApp f (i - Array.length u.up_a) a)
        | _ -> unif_HO env ise u.up_f f in
        let ise'' = unif_HO_args env ise' u.up_a (i - Array.length u.up_a) a in
        let lhs = mkSubApp f i a in
        let pt' = unif_end env sigma0 ise'' u.up_t (u.up_ok lhs) in
        on_instance (ungen_upat lhs pt' u)
      with FoundUnif (_,s,_,_) as sig_u when dont_impact_evars s -> raise sig_u
      | NoProgress -> it_did_match := true
      | Pretype_errors.PretypeError
         (_,_,Pretype_errors.UnsatisfiableConstraints _) ->
          failed_because_of_TC:=true
      | e when CErrors.noncritical e -> () in
    List.iter one_match fpats
  done;
  iter_constr_LR ise (aux upats env sigma0 ise) f;
  Array.iter (aux upats env sigma0 ise) a
 in
 aux upats env sigma0 ise c;
 if !it_did_match then raise NoProgress;
 !failed_because_of_TC


let fixed_upat evd = function
| {up_k = KpatFlex | KpatEvar _ | KpatProj _} -> false
| {up_t = t} -> not (occur_existential evd t)

let do_once r f = match !r with Some _ -> () | None -> r := Some (f ())

let assert_done r =
  match !r with Some x -> x | None -> CErrors.anomaly (str"do_once never called.")

let assert_done_multires r =
  match !r with
  | None -> CErrors.anomaly (str"do_once never called.")
  | Some (e, n, xs) ->
      r := Some (e, n+1,xs);
      try List.nth xs n with Failure _ -> raise NoMatch

type subst = Environ.env -> EConstr.t -> EConstr.t -> int -> EConstr.t
type find_P =
  Environ.env -> EConstr.t -> int ->
  k:subst ->
     EConstr.t
type conclude = unit ->
  EConstr.t * ssrdir * (bool * Evd.evar_map * UState.t * EConstr.t)

(* upats_origin makes a better error message only            *)
let mk_tpattern_matcher ?(all_instances=false)
  ?(raise_NoMatch=false) ?upats_origin sigma0 occ (ise, upats)
=
  let nocc = ref 0 and skip_occ = ref false in
  let use_occ, occ_list = match occ with
  | Some (true, ol) -> ol = [], ol
  | Some (false, ol) -> ol <> [], ol
  | None -> false, [] in
  let max_occ = List.fold_right max occ_list 0 in
  let subst_occ =
    let occ_set = Array.make max_occ (not use_occ) in
    let _ = List.iter (fun i -> occ_set.(i - 1) <- use_occ) occ_list in
    let _ = if max_occ = 0 then skip_occ := use_occ in
    fun () -> incr nocc;
    if !nocc = max_occ then skip_occ := use_occ;
    if !nocc <= max_occ then occ_set.(!nocc - 1) else not use_occ in
  let upat_that_matched = ref None in
  let match_EQ env sigma u =
    let open EConstr in
    match u.up_k with
    | KpatLet ->
      let x, pv, t, pb = destLetIn sigma u.up_f in
      let env' =
        EConstr.push_rel (Context.Rel.Declaration.LocalAssum(x, t)) env in
      let match_let f = match EConstr.kind ise f with
      | LetIn (_, v, _, b) -> unif_EQ env sigma pv v && unif_EQ env' sigma pb b
      | _ -> false in match_let
    | KpatFixed -> fun c -> EConstr.eq_constr_nounivs sigma u.up_f c
    | KpatConst -> fun c -> EConstr.eq_constr_nounivs sigma u.up_f c
    | KpatLam -> fun c ->
       (match EConstr.kind sigma c with
       | Lambda _ -> unif_EQ env sigma u.up_f c
       | _ -> false)
    | _ -> unif_EQ env sigma u.up_f in
let p2t p = EConstr.mkApp(p.up_f,p.up_a) in
let source env = match upats_origin, upats with
  | None, [p] ->
      (if fixed_upat ise p then str"term " else str"partial term ") ++
      pr_econstr_pat env ise (p2t p) ++ spc()
  | Some (dir,rule), [p] -> str"The " ++ pr_dir_side dir ++ str" of " ++
      pr_econstr_pat env ise rule ++ fnl() ++ ws 4 ++ pr_econstr_pat env ise (p2t p) ++ fnl()
  | Some (dir,rule), _ -> str"The " ++ pr_dir_side dir ++ str" of " ++
      pr_econstr_pat env ise rule ++ spc()
  | _, [] | None, _::_::_ ->
      CErrors.anomaly (str"mk_tpattern_matcher with no upats_origin.") in
let on_instance, instances =
  let instances = ref [] in
  (fun x ->
    if all_instances then instances := !instances @ [x]
    else raise (FoundUnif x)),
  (fun () -> !instances) in
let rec uniquize = function
  | [] -> []
  | (_, sigma,_,{ up_f = f; up_a = a; up_t = t } as x) :: xs ->
    let nf_evar sigma c = EConstr.Unsafe.to_constr (Evarutil.nf_evar sigma c) in
    let equal sigma1 sigma2 c1 c2 = Constr.equal (nf_evar sigma1 c1) (nf_evar sigma2 c2) in
    let neq (_, sigma1,_,{ up_f = f1; up_a = a1; up_t = t1 }) =
      not (equal sigma sigma1 t t1 &&
           equal sigma sigma1 f f1 && CArray.for_all2 (equal sigma sigma1) a a1) in
    x :: uniquize (List.filter neq xs) in

((fun env c h ~k ->
  do_once upat_that_matched (fun () ->
    let failed_because_of_TC = ref false in
    try
      if not all_instances then match_upats_FO upats env sigma0 ise c;
      failed_because_of_TC:=match_upats_HO ~on_instance upats env sigma0 ise c;
      raise NoMatch
    with FoundUnif sigma_u -> env,0,[sigma_u]
    | (NoMatch|NoProgress) when all_instances && instances () <> [] ->
      env, 0, uniquize (instances ())
    | NoMatch when (not raise_NoMatch) ->
      if !failed_because_of_TC then
        errorstrm (source env ++ strbrk"matches but type classes inference fails")
      else
        errorstrm (source env ++ str "does not match any subterm of the goal")
    | NoProgress when (not raise_NoMatch) ->
        let dir = match upats_origin with Some (d,_) -> d | _ ->
          CErrors.anomaly (str"mk_tpattern_matcher with no upats_origin.") in
        errorstrm (str"all matches of "++ source env ++
          str"are equal to the " ++ pr_dir_side (inv_dir dir))
    | NoProgress -> raise NoMatch);
  let _, sigma, _, ({up_f = pf; up_a = pa} as u) =
    if all_instances then assert_done_multires upat_that_matched
    else List.hd (pi3(assert_done upat_that_matched)) in
(*   pp(lazy(str"sigma@tmatch=" ++ pr_evar_map None sigma)); *)
  if !skip_occ then ((*ignore(k env u.up_t 0);*) c) else
  let match_EQ = match_EQ env sigma u in
  let pn = Array.length pa in
  let rec subst_loop (env,h as acc) c' =
    if !skip_occ then c' else
    let f, a = splay_app sigma c' in
    if Array.length a >= pn && match_EQ f && unif_EQ_args env sigma pa a then
      let open EConstr in
      let a1, a2 = Array.chop (Array.length pa) a in
      let fa1 = mkApp (f, a1) in
      let f' = if subst_occ () then k env u.up_t fa1 h else fa1 in
      mkApp (f', Array.map_left (subst_loop acc) a2)
    else
      let open EConstr in
      (* TASSI: clear letin values to avoid unfolding *)
      let inc_h rd (env,h') =
        let ctx_item =
          match rd with
          | Context.Rel.Declaration.LocalAssum _ as x -> x
          | Context.Rel.Declaration.LocalDef (x,_,y) ->
              Context.Rel.Declaration.LocalAssum(x,y) in
        EConstr.push_rel ctx_item env, h' + 1 in
      let self acc c = subst_loop acc c in
      let f' = map_constr_with_binders_left_to_right env sigma inc_h self acc f in
      mkApp (f', Array.map_left (subst_loop acc) a) in
      subst_loop (env,h) c) : find_P),
((fun () ->
  let env, (c, sigma, uc, ({up_f = pf; up_a = pa} as u)) =
    match !upat_that_matched with
    | Some (env,_,x) -> env,List.hd x | None when raise_NoMatch -> raise NoMatch
    | None -> CErrors.anomaly (str"companion function never called.") in
  let p' = EConstr.mkApp (pf, pa) in
  if max_occ <= !nocc then p', u.up_dir, (c, sigma, uc, u.up_t)
  else errorstrm (str"Only " ++ int !nocc ++ str" < " ++ int max_occ ++
        str(String.plural !nocc " occurrence") ++ match upats_origin with
        | None -> str" of" ++ spc() ++ pr_econstr_pat env sigma p'
        | Some (dir,rule) -> str" of the " ++ pr_dir_side dir ++ fnl() ++
            ws 4 ++ pr_econstr_pat env sigma p' ++ fnl () ++
            str"of " ++ pr_econstr_pat env sigma rule)) : conclude)

type ('ident, 'term) ssrpattern =
  | T of 'term
  | In_T of 'term
  | X_In_T of 'ident * 'term
  | In_X_In_T of 'ident * 'term
  | E_In_X_In_T of 'term * 'ident * 'term
  | E_As_X_In_T of 'term * 'ident * 'term

let pr_pattern pr_ident pr_term = function
  | T t -> pr_term t
  | In_T t -> str "in " ++ pr_term t
  | X_In_T (x,t) -> pr_ident x ++ str " in " ++ pr_term t
  | In_X_In_T (x,t) -> str "in " ++ pr_ident x ++ str " in " ++ pr_term t
  | E_In_X_In_T (e,x,t) ->
      pr_term e ++ str " in " ++ pr_ident x ++ str " in " ++ pr_term t
  | E_As_X_In_T (e,x,t) ->
      pr_term e ++ str " as " ++ pr_ident x ++ str " in " ++ pr_term t

let pr_hole pr_constr e = pr_constr (EConstr.mkEvar e)

let pr_pattern_aux pr_constr = function
  | T t -> pr_constr t
  | In_T t -> str "in " ++ pr_constr t
  | X_In_T (x,t) -> pr_hole pr_constr x ++ str " in " ++ pr_constr t
  | In_X_In_T (x,t) -> str "in " ++ pr_hole pr_constr x ++ str " in " ++ pr_constr t
  | E_In_X_In_T (e,x,t) ->
      pr_constr e ++ str " in " ++ pr_hole pr_constr x ++ str " in " ++ pr_constr t
  | E_As_X_In_T (e,x,t) ->
      pr_constr e ++ str " as " ++ pr_hole pr_constr x ++ str " in " ++ pr_constr t
let pp_pattern env (sigma, p) =
  pr_pattern_aux (fun t -> pr_econstr_pat env sigma t) p

type cpattern =
  { kind : ssrtermkind
  ; pattern : Genintern.glob_constr_and_expr
  ; interpretation : Geninterp.interp_sign option }

let pr_term {kind; pattern; _} =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  pr_guarded (guard_term kind) (pr_glob_constr_and_expr env sigma) pattern
let prl_term {kind; pattern; _} =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  pr_guarded (guard_term kind) (prl_glob_constr_and_expr env sigma) pattern

let pr_cpattern = pr_term

let pr_pattern_w_ids = pr_pattern pr_id prl_term

let mk_term k c ist = {kind=k; pattern=(mkRHole, Some c); interpretation=ist}
let mk_lterm = mk_term NoFlag

let glob_ssrterm gs = function
  | {kind; pattern=(_, Some c); interpretation=None} ->
    let x = Tacintern.intern_constr gs c in
    {kind; pattern=(fst x, Some c); interpretation=None}
  | ct -> ct

(* ssrterm conbinators *)
let combineCG t1 t2 f g =
  let mk_ist i1 i2 = match i1, i2 with
    | None, Some i -> Some i
    | Some i, None -> Some i
    | None, None -> None
    | Some i, Some j when i == j -> Some i
    | _ -> CErrors.anomaly (Pp.str "combineCG: different ist") in
  match t1, t2 with
  | {kind=x; pattern=(t1, None); interpretation=i1}, {pattern=(t2, None); interpretation=i2} ->
    {kind=x; pattern=(g t1 t2, None); interpretation = mk_ist i1 i2}
  | {kind=x; pattern=(_, Some t1); interpretation=i1}, {pattern=(_, Some t2); interpretation=i2} ->
    {kind=x; pattern=(mkRHole, Some (f t1 t2)); interpretation = mk_ist i1 i2}
  | _, {pattern=(_, None); _} -> CErrors.anomaly (str"have: mixed C-G constr.")
  | _ -> CErrors.anomaly (str"have: mixed G-C constr.")
let loc_ofCG = function
  | {pattern = (s, None); _} -> Glob_ops.loc_of_glob_constr s
  | {pattern = (_, Some s); _} -> Constrexpr_ops.constr_loc s

(* This piece of code asserts the following notations are reserved *)
(* Reserved Notation "( a 'in' b )"        (at level 0).           *)
(* Reserved Notation "( a 'as' b )"        (at level 0).           *)
(* Reserved Notation "( a 'in' b 'in' c )" (at level 0).           *)
(* Reserved Notation "( a 'as' b 'in' c )" (at level 0).           *)
let glob_cpattern gs p =
  pp(lazy(str"globbing pattern: " ++ pr_term p));
  let glob x = (glob_ssrterm gs (mk_lterm x None)).pattern in
  let encode k s l =
    let name = Name (Id.of_string ("_ssrpat_" ^ s)) in
    {kind=k; pattern=(mkRCast mkRHole (mkRLambda name mkRHole (mkRApp mkRHole l)), None); interpretation=None} in
  let bind_in t1 t2 =
    let mkCHole = mkCHole ~loc:None in let n = Name (destCVar t1) in
    fst (glob (mkCCast mkCHole (mkCLambda n mkCHole t2))) in
  let check_var t2 = if not (isCVar t2) then
    loc_error (constr_loc t2) "Only identifiers are allowed here" in
  match p with
  | {pattern = (_, None); _} as x -> x
  | {kind=k; pattern=(v, Some t); _} as orig ->
     if k = Cpattern then glob_ssrterm gs {kind=InParens; pattern=(v, Some t); interpretation=None} else
     match t.CAst.v with
     | CNotation(_,(InConstrEntry,"( _ in _ )"), ([t1; t2], [], [], [])) ->
         (try match glob t1, glob t2 with
         | (r1, None), (r2, None) -> encode k "In" [r1;r2]
         | (r1, Some _), (r2, Some _) when isCVar t1 ->
             encode k "In" [r1; r2; bind_in t1 t2]
         | (r1, Some _), (r2, Some _) -> encode k "In" [r1; r2]
         | _ -> CErrors.anomaly (str"where are we?.")
         with _ when isCVar t1 -> encode k "In" [bind_in t1 t2])
     | CNotation(_,(InConstrEntry,"( _ in _ in _ )"), ([t1; t2; t3], [], [], [])) ->
         check_var t2; encode k "In" [fst (glob t1); bind_in t2 t3]
     | CNotation(_,(InConstrEntry,"( _ as _ )"), ([t1; t2], [], [], [])) ->
         encode k "As" [fst (glob t1); fst (glob t2)]
     | CNotation(_,(InConstrEntry,"( _ as _ in _ )"), ([t1; t2; t3], [], [], [])) ->
         check_var t2; encode k "As" [fst (glob t1); bind_in t2 t3]
     | _ -> glob_ssrterm gs orig
;;

let glob_rpattern s p =
  match p with
  | T t -> T (glob_cpattern s t)
  | In_T t -> In_T (glob_ssrterm s t)
  | X_In_T(x,t) -> X_In_T (x,glob_ssrterm s t)
  | In_X_In_T(x,t) -> In_X_In_T (x,glob_ssrterm s t)
  | E_In_X_In_T(e,x,t) -> E_In_X_In_T (glob_ssrterm s e,x,glob_ssrterm s t)
  | E_As_X_In_T(e,x,t) -> E_As_X_In_T (glob_ssrterm s e,x,glob_ssrterm s t)

let subst_ssrterm s {kind; pattern; interpretation} =
  {kind; pattern=Tacsubst.subst_glob_constr_and_expr s pattern; interpretation}

let subst_rpattern s = function
  | T t -> T (subst_ssrterm s t)
  | In_T t -> In_T (subst_ssrterm s t)
  | X_In_T(x,t) -> X_In_T (x,subst_ssrterm s t)
  | In_X_In_T(x,t) -> In_X_In_T (x,subst_ssrterm s t)
  | E_In_X_In_T(e,x,t) -> E_In_X_In_T (subst_ssrterm s e,x,subst_ssrterm s t)
  | E_As_X_In_T(e,x,t) -> E_As_X_In_T (subst_ssrterm s e,x,subst_ssrterm s t)

let interp_ssrterm ist {kind; pattern; _} = {kind; pattern; interpretation = Some ist}

let interp_rpattern s = function
  | T t -> T (interp_ssrterm s t)
  | In_T t -> In_T (interp_ssrterm s t)
  | X_In_T(x,t) -> X_In_T (interp_ssrterm s x,interp_ssrterm s t)
  | In_X_In_T(x,t) -> In_X_In_T (interp_ssrterm s x,interp_ssrterm s t)
  | E_In_X_In_T(e,x,t) ->
    E_In_X_In_T (interp_ssrterm s e,interp_ssrterm s x,interp_ssrterm s t)
  | E_As_X_In_T(e,x,t) ->
    E_As_X_In_T (interp_ssrterm s e,interp_ssrterm s x,interp_ssrterm s t)

let interp_rpattern0 ist _ _ t = interp_rpattern ist t

let tag_of_cpattern p = p.kind
let loc_of_cpattern = loc_ofCG
type occ = (bool * int list) option

type rpattern = (cpattern, cpattern) ssrpattern
let pr_rpattern = pr_pattern pr_cpattern pr_cpattern

let wit_rpatternty = add_genarg "rpatternty" (fun env sigma -> pr_pattern pr_cpattern pr_cpattern)

type pattern = Evd.evar_map * (EConstr.existential, EConstr.t) ssrpattern

let id_of_cpattern {pattern = (c1, c2); _} =
  let open CAst in
  match DAst.get c1, c2 with
  | _, Some { v = CRef (qid, _) } when qualid_is_ident qid ->
    Some (qualid_basename qid)
  | _, Some { v = CAppExpl ((qid, _), []) } when qualid_is_ident qid ->
    Some (qualid_basename qid)
  | GRef (GlobRef.VarRef x, _), None -> Some x
  | _ -> None
let id_of_Cterm t = match id_of_cpattern t with
  | Some x -> x
  | None -> loc_error (loc_of_cpattern t) "Only identifiers are allowed here"

let interp_open_constr ist env sigma gc =
  Tacinterp.interp_open_constr ist env sigma gc
let pf_intern_term env sigma {pattern = c; interpretation = ist; _} = glob_constr ist env sigma c

let interp_ssrterm ist env sigma t = interp_ssrterm ist t

let interp_term env sigma = function
  | {pattern = c; interpretation = Some ist; _} -> interp_open_constr ist env sigma c
  | _ -> errorstrm (str"interpreting a term with no ist")

let thin id sigma goal =
  let ids = Id.Set.singleton id in
  let evi = Evd.find sigma goal in
  let env = Evd.evar_filtered_env (Global.env ()) evi in
  let cl = Evd.evar_concl evi in
  let sigma = Evd.clear_metas sigma in
  let ans =
    try Some (Evarutil.clear_hyps_in_evi env sigma (Environ.named_context_val env) cl ids)
    with Evarutil.ClearDependencyError _ -> None
  in
  match ans with
  | None -> sigma
  | Some (sigma, hyps, concl) ->
    let (sigma, evk) =
      Evarutil.new_pure_evar ~src:(Loc.tag Evar_kinds.GoalEvar) ~typeclass_candidate:false hyps sigma concl
    in
    let sigma = Evd.remove_future_goal sigma evk in
    let id = Evd.evar_ident goal sigma in
    let proof = EConstr.mkEvar (evk, Evd.evar_identity_subst @@ Evd.find sigma evk) in
    let sigma = Evd.define goal proof sigma in
    match id with
    | None -> sigma
    | Some id -> Evd.rename evk id sigma

(*
let pr_ist { lfun= lfun } =
  prlist_with_sep spc
    (fun (id, Geninterp.Val.Dyn(ty,_)) ->
        pr_id id ++ str":" ++ Geninterp.Val.pr ty) (Id.Map.bindings lfun)
*)

let interp_pattern ?wit_ssrpatternarg env sigma0 red redty =
  pp(lazy(str"interpreting: " ++ pr_rpattern red));
  let xInT x y = X_In_T(x,y) and inXInT x y = In_X_In_T(x,y) in
  let inT x = In_T x and eInXInT e x t = E_In_X_In_T(e,x,t) in
  let eAsXInT e x t = E_As_X_In_T(e,x,t) in
  let mkG ?(k=NoFlag) x ist = {kind = k; pattern = (x,None); interpretation = ist } in
  let ist_of x = x.interpretation in
  let decode ({interpretation=ist; _} as t) ?reccall f g =
    try match DAst.get (pf_intern_term env sigma0 t) with
    | GCast(t, DEFAULTcast, c) when isGHole t && isGLambda c->
      let (x, c) = destGLambda c in
      f x {kind = NoFlag; pattern = (c,None); interpretation = ist}
    | GVar id
      when Option.has_some ist && let ist = Option.get ist in
           Id.Map.mem id ist.lfun &&
           not(Option.is_empty reccall) &&
           not(Option.is_empty wit_ssrpatternarg) ->
        let v = Id.Map.find id (Option.get ist).lfun in
        Option.get reccall
          (Value.cast (topwit (Option.get wit_ssrpatternarg)) v)
    | it -> g t with e when CErrors.noncritical e -> g t in
  let decodeG ist t f g = decode (mkG t ist) f g in
  let bad_enc id _ = CErrors.anomaly (str"bad encoding for pattern "++str id++str".") in
  let cleanup_XinE (h_k, _) x rp sigma =
    let to_clean, update = (* handle rename if x is already used *)
      let ctx = Environ.named_context env in
      let len = Context.Named.length ctx in
      let name = ref None in
      try ignore(Context.Named.lookup x ctx); (name, fun k ->
        if !name = None then
        let nctx = Evd.evar_context (Evd.find sigma k) in
        let nlen = Context.Named.length nctx in
        if nlen > len then begin
          name := Some (Context.Named.Declaration.get_id (List.nth nctx (nlen - len - 1)))
        end)
      with Not_found -> ref (Some x), fun _ -> () in
    let new_evars =
      let rec aux acc t = match EConstr.kind sigma t with
      | Evar (k,_) ->
          if k = h_k || List.mem k acc || Evd.mem sigma0 k then acc else
          (update k; k::acc)
      | _ -> EConstr.fold sigma aux acc t in
      aux [] rp in
    let sigma =
      List.fold_left (fun sigma e ->
        if Evd.is_defined sigma e then sigma else (* clear may be recursive *)
        if Option.is_empty !to_clean then sigma else
        let name = Option.get !to_clean in
        pp(lazy(pr_id name));
        thin name sigma e)
      sigma new_evars in
    sigma in
  let red = let rec decode_red = function
    | T {kind=k; pattern=(t,None); interpretation=ist} ->
      begin match DAst.get t with
      | GCast (c, DEFAULTcast, t)
        when isGHole c &&
          let (id, t) = destGLambda t in
          let id = Id.to_string id in let len = String.length id in
        (len > 8 && String.sub id 0 8 = "_ssrpat_") ->
        let (id, t) = destGLambda t in
        let id = Id.to_string id in let len = String.length id in
        (match String.sub id 8 (len - 8), DAst.get t with
        | "In", GApp( _, [t]) -> decodeG ist t xInT (fun x -> T x)
        | "In", GApp( _, [e; t]) -> decodeG ist t (eInXInT (mkG e ist)) (bad_enc id)
        | "In", GApp( _, [e; t; e_in_t]) ->
            decodeG ist t (eInXInT (mkG e ist))
              (fun _ -> decodeG ist e_in_t xInT (fun _ -> assert false))
        | "As", GApp(_, [e; t]) -> decodeG ist t (eAsXInT (mkG e ist)) (bad_enc id)
        | _ -> bad_enc id ())
      | _ ->
        decode ~reccall:decode_red (mkG ~k t ist) xInT (fun x -> T x)
      end
    | T t -> decode ~reccall:decode_red t xInT (fun x -> T x)
    | In_T t -> decode t inXInT inT
    | X_In_T (e,t) ->  decode t (eInXInT e) (fun x -> xInT (id_of_Cterm e) x)
    | In_X_In_T (e,t) -> inXInT (id_of_Cterm e) t
    | E_In_X_In_T (e,x,rp) -> eInXInT e (id_of_Cterm x) rp
    | E_As_X_In_T (e,x,rp) -> eAsXInT e (id_of_Cterm x) rp in
    decode_red red in
  pp(lazy(str"decoded as: " ++ pr_pattern_w_ids red));
  let red =
    match redty with
    | None -> red
    | Some (ty, ist) -> let ty = {kind=NoFlag; pattern=ty; interpretation = Some ist} in
  match red with
  | T t -> T (combineCG t ty (mkCCast ?loc:(loc_ofCG t)) mkRCast)
  | X_In_T (x,t) ->
      let gty = pf_intern_term env sigma0 ty in
      E_As_X_In_T (mkG (mkRCast mkRHole gty) (ist_of ty), x, t)
  | E_In_X_In_T (e,x,t) ->
      let ty = mkG (pf_intern_term env sigma0 ty) (ist_of ty) in
      E_In_X_In_T (combineCG e ty (mkCCast ?loc:(loc_ofCG t)) mkRCast, x, t)
  | E_As_X_In_T (e,x,t) ->
      let ty = mkG (pf_intern_term env sigma0 ty) (ist_of ty) in
      E_As_X_In_T (combineCG e ty (mkCCast ?loc:(loc_ofCG t)) mkRCast, x, t)
  | red -> red in
  pp(lazy(str"typed as: " ++ pr_pattern_w_ids red));
  let mkXLetIn ?loc x {kind; pattern=(g,c); interpretation} = match c with
  | Some b -> {kind; pattern=(g,Some (mkCLetIn ?loc x (mkCHole ~loc) b)); interpretation}
  | None -> { kind
            ; pattern = DAst.make ?loc @@ GLetIn
                  (x, DAst.make ?loc @@ GHole (BinderType x, IntroAnonymous, None), None, g), None
            ; interpretation} in
  match red with
  | T t -> let sigma, t = interp_term env sigma0 t in sigma, T t
  | In_T t -> let sigma, t = interp_term env sigma0 t in sigma, In_T t
  | X_In_T (x, rp) | In_X_In_T (x, rp) ->
    let mk x p = match red with X_In_T _ -> X_In_T(x,p) | _ -> In_X_In_T(x,p) in
    let rp = mkXLetIn (Name x) rp in
    let sigma, rp = interp_term env sigma0 rp in
    let _, h, _, rp = EConstr.destLetIn sigma rp in
    let h = EConstr.destEvar sigma h in
    let sigma = cleanup_XinE h x rp sigma in
    let rp = EConstr.Vars.subst1 (EConstr.mkEvar h) (Evarutil.nf_evar sigma rp) in
    sigma, mk h rp
  | E_In_X_In_T(e, x, rp) | E_As_X_In_T (e, x, rp) ->
    let mk e x p =
      match red with E_In_X_In_T _ ->E_In_X_In_T(e,x,p)|_->E_As_X_In_T(e,x,p) in
    let rp = mkXLetIn (Name x) rp in
    let sigma, rp = interp_term env sigma0 rp in
    let _, h, _, rp = EConstr.destLetIn sigma rp in
    let h = EConstr.destEvar sigma h in
    let sigma = cleanup_XinE h x rp sigma in
    let rp = EConstr.Vars.subst1 (EConstr.mkEvar h) (Evarutil.nf_evar sigma rp) in
    let sigma, e = interp_term env sigma e in
    sigma, mk e h rp
;;
let interp_cpattern env sigma red redty = interp_pattern env sigma (T red) redty;;
let interp_rpattern ~wit_ssrpatternarg env sigma red = interp_pattern ~wit_ssrpatternarg env sigma red None;;

let id_of_pattern sigma = function
  | _, T t -> (match EConstr.kind sigma t with Var id -> Some id | _ -> None)
  | _ -> None

(* The full occurrence set *)
let noindex = Some(false,[])

(* calls do_subst on every sub-term identified by (pattern,occ) *)
let eval_pattern ?raise_NoMatch env0 sigma0 concl0 pattern occ (do_subst : subst) =
  let rigid ev = Evd.mem sigma0 ev in
  let fs sigma x = Reductionops.nf_evar sigma x in
  let pop_evar sigma e p =
    let { Evd.evar_body = e_body } as e_def = Evd.find sigma e in
    let e_body = match e_body with Evar_defined c -> c
    | _ -> errorstrm (str "Matching the pattern " ++ pr_econstr_env env0 sigma0 p ++
          str " did not instantiate ?" ++ int (Evar.repr e) ++ spc () ++
          str "Does the variable bound by the \"in\" construct occur "++
          str "in the pattern?") in
    let sigma =
      Evd.add (Evd.remove sigma e) e {e_def with Evd.evar_body = Evar_empty} in
    sigma, e_body in
  let mk_upat_for ?hack ~rigid (sigma, t) =
    let sigma,pat= mk_tpattern ?hack ~rigid env0 (sigma, t) L2R (fs sigma t) in
    sigma, [pat] in
  match pattern with
  | None -> do_subst env0 concl0 concl0 1, UState.empty
  | Some (sigma, (T rp | In_T rp)) ->
    let rp = fs sigma rp in
    let ise = create_evar_defs sigma in
    let occ = match pattern with Some (_, T _) -> occ | _ -> noindex in
    let rp = mk_upat_for ~rigid (ise, rp) in
    let find_T, end_T = mk_tpattern_matcher ?raise_NoMatch sigma0 occ rp in
    let concl = find_T env0 concl0 1 ~k:do_subst in
    let _, _, (_, _, us, _) = end_T () in
    concl, us
  | Some (sigma, (X_In_T (hole, p) | In_X_In_T (hole, p))) ->
    let p = fs sigma p in
    let occ = match pattern with Some (_, X_In_T _) -> occ | _ -> noindex in
    let ex = fst hole in
    let hole = EConstr.mkEvar hole in
    let rp = mk_upat_for ~hack:true ~rigid (sigma, p) in
    let find_T, end_T = mk_tpattern_matcher sigma0 noindex rp in
    (* we start from sigma, so hole is considered a rigid head *)
    let holep = mk_upat_for ~rigid:(fun ev -> Evd.mem sigma ev) (sigma, hole) in
    let find_X, end_X = mk_tpattern_matcher ?raise_NoMatch sigma occ holep in
    let concl = find_T env0 concl0 1 ~k:(fun env c _ h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) c p in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h
        ~k:(fun env _ -> do_subst env e_body))) in
    let _ = end_X () in let _, _, (_, _, us, _) = end_T () in
    concl, us
  | Some (sigma, E_In_X_In_T (e, hole, p)) ->
    let p, e = fs sigma p, fs sigma e in
    let ex = fst hole in
    let hole = EConstr.mkEvar hole in
    let rp = mk_upat_for ~hack:true ~rigid (sigma, p) in
    let find_T, end_T = mk_tpattern_matcher sigma0 noindex rp in
    let holep = mk_upat_for ~rigid:(fun ev -> Evd.mem sigma ev) (sigma, hole) in
    let find_X, end_X = mk_tpattern_matcher sigma noindex holep in
    let re = mk_upat_for ~rigid (sigma, e) in
    let find_E, end_E = mk_tpattern_matcher ?raise_NoMatch sigma0 occ re in
    let concl = find_T env0 concl0 1 ~k:(fun env c _ h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) c p in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h ~k:(fun env c _ h ->
        find_E env e_body h ~k:do_subst))) in
    let _, _, (_, _, us, _) = end_E () in
    let _ = end_X () in let _ = end_T () in
    concl, us
  | Some (sigma, E_As_X_In_T (e, hole, p)) ->
    let p, e = fs sigma p, fs sigma e in
    let ex = fst hole in
    let hole = EConstr.mkEvar hole in
    let rp =
      let e_sigma = unify_HO env0 sigma hole e in
      e_sigma, fs e_sigma p in
    let rp = mk_upat_for ~hack:true ~rigid rp in
    let find_TE, end_TE = mk_tpattern_matcher sigma0 noindex rp in
    let holep = mk_upat_for ~rigid:(fun ev -> Evd.mem sigma ev) (sigma, hole) in
    let find_X, end_X = mk_tpattern_matcher sigma occ holep in
    let concl = find_TE env0 concl0 1 ~k:(fun env c _ h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) c p in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h ~k:(fun env c _ h ->
        let e_sigma = unify_HO env sigma e_body e in
        let e_body = fs e_sigma e in
        do_subst env e_body e_body h))) in
    let _ = end_X () in let _, _ , (_, _, us, _) = end_TE () in
    concl, us

let redex_of_pattern (sigma, p) = match p with
| In_T _ | In_X_In_T _ -> None
| X_In_T (e, _) -> Some (sigma, EConstr.mkEvar e)
| T e | E_As_X_In_T (e, _, _) | E_In_X_In_T (e, _, _) -> Some (sigma, e)

let redex_of_pattern_nf env p =
  let sigma, e = match redex_of_pattern p with
  | None -> CErrors.anomaly (str"pattern without redex.")
  | Some (sigma, e) -> sigma, e
  in
  Evarutil.nf_evar sigma e, Evd.evar_universe_context sigma

let fill_occ_pattern ?raise_NoMatch env sigma cl pat occ h =
  let do_make_rel, occ =
    if occ = Some(true,[]) then false, Some(false,[1]) else true, occ in
  let r = ref None in
  let find_R env c _ h' =
    let () = do_once r (fun () -> c) in
    if do_make_rel then EConstr.mkRel (h'+h-1) else c
  in
  let cl, us =
    eval_pattern ?raise_NoMatch env sigma cl (Some pat) occ find_R in
  let e = match !r with None -> fst(redex_of_pattern_nf env pat) | Some x -> x in
  (e, us), cl

let fill_rel_occ_pattern env sigma cl pat occ =
  let (e, us), cl =
    try fill_occ_pattern ~raise_NoMatch:true env sigma cl pat occ 1
    with NoMatch -> redex_of_pattern_nf env pat, cl
  in
  let sigma = Evd.merge_universe_context sigma us in
  sigma, e, cl

(* clenup interface for external use *)
let mk_tpattern ?p_origin ?ok ~rigid env sigma_t dir c =
  mk_tpattern ?p_origin ?ok ~rigid env sigma_t dir c

let eval_pattern ?raise_NoMatch env0 sigma0 concl0 pattern occ do_subst =
  fst (eval_pattern ?raise_NoMatch env0 sigma0 concl0 pattern occ do_subst)

let pf_fill_occ env concl occ sigma0 p (sigma, t) h =
 let ise = create_evar_defs sigma in
 let rigid ev = Evd.mem sigma0 ev in
 let ise, u = mk_tpattern ~rigid env (ise, t) L2R p in
 let find_U, end_U =
   mk_tpattern_matcher ~raise_NoMatch:true sigma0 occ (ise,[u]) in
 let concl = find_U env concl h ~k:(fun _ _ _ n -> EConstr.mkRel n) in
 let rdx, _, (c, sigma, uc, p) = end_U () in
 c, sigma, uc, p, concl, rdx

let fill_occ_term env sigma0 cl occ (sigma, t) =
  try
    let changed, sigma', uc, t', cl, _= pf_fill_occ env cl occ sigma0 t (sigma, t) 1 in
    if changed then CErrors.user_err Pp.(str "matching impacts evars")
    else cl, t'
  with NoMatch -> try
    let changed, sigma', uc, t' =
      unif_end env sigma0 (create_evar_defs sigma) t (fun _ -> true) in
    if changed then raise NoMatch
    else cl, t'
  with _ ->
    errorstrm (str "partial term " ++ pr_econstr_pat env sigma t
            ++ str " does not match any subterm of the goal")

let cpattern_of_id id =
  { kind= NoFlag
  ; pattern = DAst.make @@ GRef (GlobRef.VarRef  id, None), None
  ; interpretation = Some Geninterp.({ lfun = Id.Map.empty; poly = false; extra = Tacinterp.TacStore.empty })}

let is_wildcard ({pattern = (l, r); _} : cpattern) : bool = match DAst.get l, r with
  | _, Some { CAst.v = CHole _ } | GHole _, None -> true
  | _ -> false

(* "ssrpattern" *)

(** All the pattern types reuse the same dynamic toplevel tag *)
let wit_ssrpatternarg = wit_rpatternty

let interp_rpattern = interp_rpattern ~wit_ssrpatternarg

let ssrpatterntac _ist arg =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let sigma0 = Proofview.Goal.sigma gl in
  let concl0 = Proofview.Goal.concl gl in
  let env = Proofview.Goal.env gl in
  let pat = interp_rpattern env sigma0 arg in
  let (t, uc), concl_x =
    fill_occ_pattern env sigma0 concl0 pat noindex 1 in
  let sigma, tty = Typing.type_of env sigma0 t in
  let concl = EConstr.mkLetIn (make_annot (Name (Id.of_string "selected")) Sorts.Relevant, t, tty, concl_x) in
  Proofview.Unsafe.tclEVARS sigma <*>
  convert_concl ~cast:false ~check:true concl DEFAULTcast
  end

(* Register "ssrpattern" tactic *)
let () =
  let mltac _ ist =
    let arg =
      let v = Id.Map.find (Names.Id.of_string "pattern") ist.lfun in
      Value.cast (topwit wit_ssrpatternarg) v in
    ssrpatterntac ist arg in
  let name = { mltac_plugin = "coq-core.plugins.ssrmatching"; mltac_tactic = "ssrpattern"; } in
  let () = Tacenv.register_ml_tactic name [|mltac|] in
  let tac =
    CAst.make (TacFun ([Name (Id.of_string "pattern")],
      CAst.make (TacML ({ mltac_name = name; mltac_index = 0 }, [])))) in
  let obj () =
    Tacenv.register_ltac true false (Id.of_string "ssrpattern") tac in
  Mltop.declare_cache_obj obj "coq-core.plugins.ssrmatching"

let ssrinstancesof arg =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let concl = Reductionops.nf_evar sigma concl in
  let sigma0, cpat = interp_cpattern env sigma arg None in
  let pat = match cpat with T x -> x | _ -> errorstrm (str"Not supported") in
  let rigid ev = Evd.mem sigma ev in
  let etpat, tpat = mk_tpattern ~rigid env (sigma0, pat) L2R pat in
  let find, conclude =
    mk_tpattern_matcher ~all_instances:true ~raise_NoMatch:true
      sigma None (etpat,[tpat]) in
  let print env p c _ = ppnl (hov 1 (str"instance:" ++ spc() ++ pr_econstr_env env (Proofview.Goal.sigma gl) p ++ spc()
                                     ++ str "matches:" ++ spc() ++ pr_econstr_env env (Proofview.Goal.sigma gl) c)); c in
  ppnl (str"BEGIN INSTANCES");
  try
    while true do
      ignore(find env concl 1 ~k:print)
    done; raise NoMatch
  with NoMatch -> ppnl (str"END INSTANCES"); Tacticals.tclIDTAC
  end

module Internal =
struct
  let wit_rpatternty = wit_rpatternty
  let glob_rpattern = glob_rpattern
  let subst_rpattern = subst_rpattern
  let interp_rpattern = interp_rpattern0
  let pr_rpattern = pr_rpattern
  let mk_rpattern x = x
  let mk_lterm = mk_lterm
  let mk_term = mk_term
  let glob_cpattern = glob_cpattern
  let subst_ssrterm = subst_ssrterm
  let interp_ssrterm = interp_ssrterm
  let pr_ssrterm = pr_term
end

(* vim: set filetype=ocaml foldmethod=marker: *)
