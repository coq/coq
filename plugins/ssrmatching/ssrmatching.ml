(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Stdarg
open Term
module CoqConstr = Constr
open CoqConstr
open Vars
open Libnames
open Tactics
open Tacticals
open Termops
open Recordops
open Tacmach
open Glob_term
open Util
open Evd
open Tacexpr
open Tacinterp
open Pretyping
open Ppconstr
open Printer
open Globnames
open Namegen
open Decl_kinds
open Evar_kinds
open Constrexpr
open Constrexpr_ops

let errorstrm = CErrors.user_err ~hdr:"ssrmatching"
let loc_error loc msg = CErrors.user_err ?loc ~hdr:msg (str msg)
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
    { Goptions.optname  = "ssrmatching debugging";
      Goptions.optkey   = ["Debug";"SsrMatching"];
      Goptions.optdepr  = false;
      Goptions.optread  = (fun _ -> !pp_ref == ssr_pp);
      Goptions.optwrite = debug }
let pp s = !pp_ref s

(** Utils *)(* {{{ *****************************************************************)
let env_size env = List.length (Environ.named_context env)
let safeDestApp c =
  match kind c with App (f, a) -> f, a | _ -> c, [| |]
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
let guard_term ch1 s i = match s.[i] with
  | '(' -> false
  | '{' | '/' | '=' -> true
  | _ -> ch1 = '('
(* The call 'guard s i' should return true if the contents of s *)
(* starting at i need bracketing to avoid ambiguities.          *)
let pr_guarded guard prc c =
  let s = Pp.string_of_ppcmds (prc c) ^ "$" in
  if guard s (skip_wschars s 0) then pr_paren prc c else prc c
(* More sensible names for constr printers *)
let prl_glob_constr c = pr_lglob_constr_env (Global.env ()) c
let pr_glob_constr c = pr_glob_constr_env (Global.env ()) c
let prl_constr_expr = pr_lconstr_expr
let pr_constr_expr = pr_constr_expr
let prl_glob_constr_and_expr = function
  | _, Some c -> prl_constr_expr c
  | c, None -> prl_glob_constr c
let pr_glob_constr_and_expr = function
  | _, Some c -> pr_constr_expr c
  | c, None -> pr_glob_constr c
let pr_term (k, c, _) = pr_guarded (guard_term k) pr_glob_constr_and_expr c
let prl_term (k, c, _) = pr_guarded (guard_term k) prl_glob_constr_and_expr c

(** Adding a new uninterpreted generic argument type *)
let add_genarg tag pr =
  let wit = Genarg.make0 tag in
  let tag = Geninterp.Val.create tag in
  let glob ist x = (ist, x) in
  let subst _ x = x in
  let interp ist x = Ftactic.return (Geninterp.Val.Dyn (tag, x)) in
  let gen_pr _ _ _ = pr in
  let () = Genintern.register_intern0 wit glob in
  let () = Genintern.register_subst0 wit subst in
  let () = Geninterp.register_interp0 wit interp in
  let () = Geninterp.register_val0 wit (Some (Geninterp.Val.Base tag)) in
  Pptactic.declare_extra_genarg_pprule wit gen_pr gen_pr gen_pr;
  wit

(** Constructors for cast type *)
let dC t = CastConv t

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
let mkCCast ?loc t ty = CAst.make ?loc @@ CCast (t, dC ty)

(** Constructors for rawconstr *)
let mkRHole = DAst.make @@ GHole (InternalHole, IntroAnonymous, None)
let mkRApp f args = if args = [] then f else DAst.make @@ GApp (f, args)
let mkRCast rc rt =  DAst.make @@ GCast (rc, dC rt)
let mkRLambda n s t = DAst.make @@ GLambda (n, Explicit, s, t)

(* ssrterm conbinators *)
let combineCG t1 t2 f g =
 let mk_ist i1 i2 = match i1, i2 with
 | None, Some i -> Some i
 | Some i, None -> Some i
 | None, None -> None
 | Some i, Some j when i == j -> Some i
 | _ -> CErrors.anomaly (Pp.str "combineCG: different ist") in
 match t1, t2 with
 | (x, (t1, None), i1), (_, (t2, None), i2) ->
      x, (g t1 t2, None), mk_ist i1 i2
 | (x, (_, Some t1), i1), (_, (_, Some t2), i2) ->
      x, (mkRHole, Some (f t1 t2)), mk_ist i1 i2
 | _, (_, (_, None), _) -> CErrors.anomaly (str"have: mixed C-G constr.")
 | _ -> CErrors.anomaly (str"have: mixed G-C constr.")
let loc_ofCG = function
 | (_, (s, None), _) -> Glob_ops.loc_of_glob_constr s
 | (_, (_, Some s), _) -> Constrexpr_ops.constr_loc s

let mk_term k c ist = k, (mkRHole, Some c), ist
let mk_lterm = mk_term ' '

let pf_type_of gl t = let sigma, ty = pf_type_of gl t in re_sig (sig_it gl)  sigma, ty

let nf_evar sigma c =
  EConstr.Unsafe.to_constr (Evarutil.nf_evar sigma (EConstr.of_constr c))

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
  let evars = existential_opt_value0 sigma, Evd.universes sigma in
  try let _ = Reduction.conv env p ~evars c in true with _ -> false

let unif_EQ_args env sigma pa a =
  let n = Array.length pa in
  let rec loop i = (i = n) || unif_EQ env sigma pa.(i) a.(i) && loop (i + 1) in
  loop 0

let unif_HO env ise p c =
  try Evarconv.the_conv_x env p c ise
  with Evarconv.UnableToUnify(ise, err) ->
    raise Pretype_errors.(PretypeError(env,ise,CannotUnify(p,c,Some err)))

let unif_HO_args env ise0 pa i ca =
  let n = Array.length pa in
  let rec loop ise j =
    if j = n then ise else loop (unif_HO env ise (EConstr.of_constr pa.(j)) (EConstr.of_constr ca.(i + j))) (j + 1) in
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
  Unification.w_unify env ise Reduction.CONV ~flags:(flags_FO env)
    (EConstr.of_constr p) (EConstr.of_constr c)

(* Perform evar substitution in main term and prune substitution. *)
let nf_open_term sigma0 ise c =
  let c = EConstr.Unsafe.to_constr c in
  let s = ise and s' = ref sigma0 in
  let rec nf c' = match kind c' with
  | Evar ex ->
    begin try nf (existential_value0 s ex) with _ ->
    let k, a = ex in let a' = Array.map nf a in
    if not (Evd.mem !s' k) then
      s' := Evd.add !s' k (Evarutil.nf_evar_info s (Evd.find s k));
    mkEvar (k, a')
    end
  | _ -> map nf c' in
  let copy_def k evi () =
    if evar_body evi != Evd.Evar_empty then () else
    match Evd.evar_body (Evd.find s k) with
      | Evar_defined c' ->
        let c' = EConstr.of_constr (nf (EConstr.Unsafe.to_constr c')) in
        s' := Evd.define k c' !s'
    | _ -> () in
  let c' = nf c in let _ = Evd.fold copy_def sigma0 () in
  !s', Evd.evar_universe_context s, EConstr.of_constr c'

let unif_end ?(solve_TC=true) env sigma0 ise0 pt ok =
  let ise = Evarconv.solve_unif_constraints_with_heuristics env ise0 in
  let tcs = Evd.get_typeclass_evars ise in
  let s, uc, t = nf_open_term sigma0 ise pt in
  let ise1 = create_evar_defs s in
  let ise1 = Evd.set_typeclass_evars ise1 (Evar.Set.filter (fun ev -> Evd.is_undefined ise1 ev) tcs) in
  let ise1 = Evd.set_universe_context ise1 uc in
  let ise2 =
    if solve_TC then Typeclasses.resolve_typeclasses ~fail:true env ise1
    else ise1 in
  if not (ok ise) then raise NoProgress else
  if ise2 == ise1 then (s, uc, t)
  else
    let s, uc', t = nf_open_term sigma0 ise2 t in
    s, UState.union uc uc', t

let unify_HO env sigma0 t1 t2 =
  let sigma = unif_HO env sigma0 t1 t2 in
  let sigma, uc, _ = unif_end ~solve_TC:false env sigma0 sigma t2 (fun _ -> true) in
  Evd.set_universe_context sigma uc

let pf_unify_HO gl t1 t2 =
  let env, sigma0, si = pf_env gl, project gl, sig_it gl in
  let sigma = unify_HO env sigma0 t1 t2 in
  re_sig si sigma

(* This is what the definition of iter_constr should be... *)
let iter_constr_LR f c = match kind c with
  | Evar (k, a) -> Array.iter f a
  | Cast (cc, _, t) -> f cc; f t  
  | Prod (_, t, b) | Lambda (_, t, b)  -> f t; f b
  | LetIn (_, v, t, b) -> f v; f t; f b
  | App (cf, a) -> f cf; Array.iter f a
  | Case (_, p, v, b) -> f v; f p; Array.iter f b
  | Fix (_, (_, t, b)) | CoFix (_, (_, t, b)) ->
    for i = 0 to Array.length t - 1 do f t.(i); f b.(i) done
  | Proj(_,a) -> f a
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _
     | Int _) -> ()

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
  up_FO : constr;
  up_f : constr;
  up_a : constr array;
  up_t : constr;                      (* equation proof term or matched term *)
  up_dir : ssrdir;                    (* direction of the rule *)
  up_ok : constr -> evar_map -> bool; (* progress test for rewrite *)
  }

let all_ok _ _ = true

let proj_nparams c =
  try 1 + Recordops.find_projection_nparams (ConstRef c) with _ -> 0

let isRigid c = match kind c with
  | Prod _ | Sort _ | Lambda _ | Case _ | Fix _ | CoFix _ -> true
  | _ -> false

let hole_var = mkVar (Id.of_string "_")
let pr_constr_pat c0 =
  let rec wipe_evar c =
    if isEvar c then hole_var else map wipe_evar c in
  let sigma, env = Pfedit.get_current_context () in
  pr_constr_env env sigma (wipe_evar c0)

(* Turn (new) evars into metas *)
let evars_for_FO ~hack env sigma0 (ise0:evar_map) c0 =
  let ise = ref ise0 in
  let sigma = ref ise0 in
  let nenv = env_size env + if hack then 1 else 0 in
  let rec put c = match kind c with
  | Evar (k, a as ex) ->
    begin try put (existential_value0 !sigma ex)
    with NotInstantiatedEvar ->
    if Evd.mem sigma0 k then map put c else
    let evi = Evd.find !sigma k in
    let dc = List.firstn (max 0 (Array.length a - nenv)) (evar_filtered_context evi) in
    let abs_dc (d, c) = function
    | Context.Named.Declaration.LocalDef (x, b, t) ->
        d, mkNamedLetIn x (put b) (put t) c
    | Context.Named.Declaration.LocalAssum (x, t) ->
        mkVar x :: d, mkNamedProd x (put t) c in
    let a, t =
      Context.Named.fold_inside abs_dc
        ~init:([], (put @@ EConstr.Unsafe.to_constr evi.evar_concl))
        (EConstr.Unsafe.to_named_context dc) in
    let m = Evarutil.new_meta () in
    ise := meta_declare m (EConstr.of_constr t) !ise;
    sigma := Evd.define k (EConstr.of_constr (applistc (mkMeta m) a)) !sigma;
    put (existential_value0 !sigma ex)
    end
  | _ -> map put c in
  let c1 = put c0 in !ise, c1

(* Compile a match pattern from a term; t is the term to fill. *)
(* p_origin can be passed to obtain a better error message     *)
let mk_tpattern ?p_origin ?(hack=false) env sigma0 (ise, t) ok dir p =
  let k, f, a =
    let f, a = Reductionops.whd_betaiota_stack ise (EConstr.of_constr p) in
    let f = EConstr.Unsafe.to_constr f in
    let a = List.map EConstr.Unsafe.to_constr a in
    match kind f with
    | Const (p,_) ->
      let np = proj_nparams p in
      if np = 0 || np > List.length a then KpatConst, f, a else
      let a1, a2 = List.chop np a in KpatProj p, (applistc f a1), a2
    | Proj (p,arg) -> KpatProj (Projection.constant p), f, a
    | Var _ | Ind _ | Construct _ -> KpatFixed, f, a
    | Evar (k, _) ->
      if Evd.mem sigma0 k then KpatEvar k, f, a else
      if a <> [] then KpatFlex, f, a else 
      (match p_origin with None -> CErrors.user_err Pp.(str "indeterminate pattern")
      | Some (dir, rule) ->
	errorstrm (str "indeterminate " ++ pr_dir_side dir
          ++ str " in " ++ pr_constr_pat rule))
    | LetIn (_, v, _, b) ->
      if b <> mkRel 1 then KpatLet, f, a else KpatFlex, v, a
    | Lambda _ -> KpatLam, f, a
    | _ -> KpatRigid, f, a in
  let aa = Array.of_list a in
  let ise', p' = evars_for_FO ~hack env sigma0 ise (mkApp (f, aa)) in
  ise',
  { up_k = k; up_FO = p'; up_f = f; 
    up_a = aa; up_ok = ok; up_dir = dir; up_t = t}

(* Specialize a pattern after a successful match: assign a precise head *)
(* kind and arity for Proj and Flex patterns.                           *)
let ungen_upat lhs (sigma, uc, t) u =
  let f, a = safeDestApp lhs in
  let k = match kind f with
  | Var _ | Ind _ | Construct _ -> KpatFixed
  | Const _ -> KpatConst
  | Evar (k, _) -> if is_defined sigma k then raise NoMatch else KpatEvar k
  | LetIn _ -> KpatLet
  | Lambda _ -> KpatLam
  | _ -> KpatRigid in
  sigma, uc, {u with up_k = k; up_FO = lhs; up_f = f; up_a = a; up_t = t}

let nb_cs_proj_args pc f u =
  let na k =
    List.length (snd (lookup_canonical_conversion (ConstRef pc, k))).o_TCOMPS in
  let nargs_of_proj t = match kind t with
      | App(_,args) -> Array.length args
      | Proj _ -> 0 (* if splay_app calls expand_projection, this has to be
                       the number of arguments including the projected *)
      | _ -> assert false in
  try match kind f with
  | Prod _ -> na Prod_cs
  | Sort s -> na (Sort_cs (Sorts.family s))
  | Const (c',_) when Constant.equal c' pc -> nargs_of_proj u.up_f 
  | Proj (c',_) when Constant.equal (Projection.constant c') pc -> nargs_of_proj u.up_f
  | Var _ | Ind _ | Construct _ | Const _ -> na (Const_cs (global_of_constr f))
  | _ -> -1
  with Not_found -> -1

let isEvar_k k f =
  match kind f with Evar (k', _) -> k = k' | _ -> false

let nb_args c =
  match kind c with App (_, a) -> Array.length a | _ -> 0

let mkSubArg i a = if i = Array.length a then a else Array.sub a 0 i
let mkSubApp f i a = if i = 0 then f else mkApp (f, mkSubArg i a)

let splay_app ise =
  let rec loop c a = match kind c with
  | App (f, a') -> loop f (Array.append a' a)
  | Cast (c', _, _) -> loop c' a
  | Evar ex ->
    (try loop (existential_value0 ise ex) a with _ -> c, a)
  | _ -> c, a in
  fun c -> match kind c with
  | App (f, a) -> loop f a
  | Cast _ | Evar _ -> loop c [| |]
  | _ -> c, [| |]

let filter_upat i0 f n u fpats =
  let na = Array.length u.up_a in
  if n < na then fpats else
  let np = match u.up_k with
  | KpatConst when eq_constr_nounivs u.up_f f -> na
  | KpatFixed when eq_constr_nounivs u.up_f f -> na
  | KpatEvar k when isEvar_k k f -> na
  | KpatLet when isLetIn f -> na
  | KpatLam when isLambda f -> na
  | KpatRigid when isRigid f -> na
  | KpatFlex -> na
  | KpatProj pc ->
    let np = na + nb_cs_proj_args pc f u in if n < np then -1 else np
  | _ -> -1 in
  if np < na then fpats else
  let () = if !i0 < np then i0 := n in (u, np) :: fpats

let eq_prim_proj c t = match kind t with
  | Proj(p,_) -> Constant.equal (Projection.constant p) c
  | _ -> false

let filter_upat_FO i0 f n u fpats =
  let np = nb_args u.up_FO in
  if n < np then fpats else
  let ok = match u.up_k with
  | KpatConst -> eq_constr_nounivs u.up_f f
  | KpatFixed -> eq_constr_nounivs u.up_f f
  | KpatEvar k -> isEvar_k k f
  | KpatLet -> isLetIn f
  | KpatLam -> isLambda f
  | KpatRigid -> isRigid f
  | KpatProj pc -> equal f (mkConst pc) || eq_prim_proj pc f
  | KpatFlex -> i0 := n; true in
  if ok then begin if !i0 < np then i0 := np; (u, np) :: fpats end else fpats

exception FoundUnif of (evar_map * UState.t * tpattern)
(* Note: we don't update env as we descend into the term, as the primitive *)
(* unification procedure always rejects subterms with bound variables.     *)

let dont_impact_evars_in cl =
  let evs_in_cl = Evd.evars_of_term cl in
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
  let dont_impact_evars = dont_impact_evars_in orig_c in
  let rec loop c =
    let f, a = splay_app ise c in let i0 = ref (-1) in
    let fpats =
      List.fold_right (filter_upat_FO i0 f (Array.length a)) upats [] in
    while !i0 >= 0 do
      let i = !i0 in i0 := -1;
      let c' = mkSubApp f i a in
      let one_match (u, np) =
         let skip =
           if i <= np then i < np else
           if u.up_k == KpatFlex then begin i0 := i - 1; false end else
           begin if !i0 < np then i0 := np; true end in
         if skip || not (closed0 c') then () else try
           let _ = match u.up_k with
           | KpatFlex ->
             let kludge v = mkLambda (Anonymous, mkProp, v) in
             unif_FO env ise (kludge u.up_FO) (kludge c')
           | KpatLet ->
             let kludge vla =
               let vl, a = safeDestApp vla in
               let x, v, t, b = destLetIn vl in
               mkApp (mkLambda (x, t, b), Array.cons v a) in
             unif_FO env ise (kludge u.up_FO) (kludge c')
           | _ -> unif_FO env ise u.up_FO c' in
           let ise' = (* Unify again using HO to assign evars *)
             let p = mkApp (u.up_f, u.up_a) in
             try unif_HO env ise (EConstr.of_constr p) (EConstr.of_constr c') with e when CErrors.noncritical e -> raise NoMatch in
           let lhs = mkSubApp f i a in
           let pt' = unif_end env sigma0 ise' (EConstr.of_constr u.up_t) (u.up_ok lhs) in
           let pt' = pi1 pt', pi2 pt', EConstr.Unsafe.to_constr (pi3 pt') in
           raise (FoundUnif (ungen_upat lhs pt' u))
       with FoundUnif (s,_,_) as sig_u when dont_impact_evars s -> raise sig_u
       | Not_found -> CErrors.anomaly (str"incomplete ise in match_upats_FO.")
       | e when CErrors.noncritical e -> () in
    List.iter one_match fpats
  done;
  iter_constr_LR loop f; Array.iter loop a in
  try loop orig_c with Invalid_argument _ -> CErrors.anomaly (str"IN FO.")


let match_upats_HO ~on_instance upats env sigma0 ise c =
 let dont_impact_evars = dont_impact_evars_in c in
 let it_did_match = ref false in
 let failed_because_of_TC = ref false in
 let rec aux upats env sigma0 ise c =
  let f, a = splay_app ise c in let i0 = ref (-1) in
  let fpats = List.fold_right (filter_upat i0 f (Array.length a)) upats [] in
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
          let _, pka = destEvar u.up_f and _, ka = destEvar f in
          unif_HO_args env ise pka 0 ka
        | KpatLet ->
          let x, v, t, b = destLetIn f in
          let _, pv, _, pb = destLetIn u.up_f in
          let ise' = unif_HO env ise (EConstr.of_constr pv) (EConstr.of_constr v) in
          unif_HO
            (Environ.push_rel (Context.Rel.Declaration.LocalAssum(x, t)) env)
            ise' (EConstr.of_constr pb) (EConstr.of_constr b)
        | KpatFlex | KpatProj _ ->
          unif_HO env ise (EConstr.of_constr u.up_f) (EConstr.of_constr(mkSubApp f (i - Array.length u.up_a) a))
        | _ -> unif_HO env ise (EConstr.of_constr u.up_f) (EConstr.of_constr f) in
        let ise'' = unif_HO_args env ise' u.up_a (i - Array.length u.up_a) a in
        let lhs = mkSubApp f i a in
        let pt' = unif_end env sigma0 ise'' (EConstr.of_constr u.up_t) (u.up_ok lhs) in
        let pt' = pi1 pt', pi2 pt', EConstr.Unsafe.to_constr (pi3 pt') in
        on_instance (ungen_upat lhs pt' u)
      with FoundUnif (s,_,_) as sig_u when dont_impact_evars s -> raise sig_u
      | NoProgress -> it_did_match := true
      | Pretype_errors.PretypeError
         (_,_,Pretype_errors.UnsatisfiableConstraints _) ->
          failed_because_of_TC:=true
      | e when CErrors.noncritical e -> () in
    List.iter one_match fpats
  done;
  iter_constr_LR (aux upats env sigma0 ise) f;
  Array.iter (aux upats env sigma0 ise) a
 in
 aux upats env sigma0 ise c;
 if !it_did_match then raise NoProgress;
 !failed_because_of_TC


let fixed_upat evd = function
| {up_k = KpatFlex | KpatEvar _ | KpatProj _} -> false 
| {up_t = t} -> not (occur_existential evd (EConstr.of_constr t)) (** FIXME *)

let do_once r f = match !r with Some _ -> () | None -> r := Some (f ())

let assert_done r = 
  match !r with Some x -> x | None -> CErrors.anomaly (str"do_once never called.")

let assert_done_multires r = 
  match !r with
  | None -> CErrors.anomaly (str"do_once never called.")
  | Some (n, xs) ->
      r := Some (n+1,xs);
      try List.nth xs n with Failure _ -> raise NoMatch

type subst = Environ.env -> constr -> constr -> int -> constr
type find_P = 
  Environ.env -> constr -> int ->
  k:subst ->
     constr
type conclude = unit ->
  constr * ssrdir * (Evd.evar_map * UState.t * constr)

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
    match u.up_k with
    | KpatLet ->
      let x, pv, t, pb = destLetIn u.up_f in
      let env' =
        Environ.push_rel (Context.Rel.Declaration.LocalAssum(x, t)) env in
      let match_let f = match kind f with
      | LetIn (_, v, _, b) -> unif_EQ env sigma pv v && unif_EQ env' sigma pb b
      | _ -> false in match_let
    | KpatFixed -> eq_constr_nounivs u.up_f
    | KpatConst -> eq_constr_nounivs u.up_f
    | KpatLam -> fun c ->
       (match kind c with
       | Lambda _ -> unif_EQ env sigma u.up_f c
       | _ -> false)
    | _ -> unif_EQ env sigma u.up_f in
let p2t p = mkApp(p.up_f,p.up_a) in 
let source () = match upats_origin, upats with
  | None, [p] -> 
      (if fixed_upat ise p then str"term " else str"partial term ") ++
      pr_constr_pat (p2t p) ++ spc()
  | Some (dir,rule), [p] -> str"The " ++ pr_dir_side dir ++ str" of " ++ 
      pr_constr_pat rule ++ fnl() ++ ws 4 ++ pr_constr_pat (p2t p) ++ fnl()
  | Some (dir,rule), _ -> str"The " ++ pr_dir_side dir ++ str" of " ++ 
      pr_constr_pat rule ++ spc()
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
  | (sigma,_,{ up_f = f; up_a = a; up_t = t } as x) :: xs ->
    let t = nf_evar sigma t in
    let f = nf_evar sigma f in
    let a = Array.map (nf_evar sigma) a in
    let neq (sigma1,_,{ up_f = f1; up_a = a1; up_t = t1 }) =
      let t1 = nf_evar sigma1 t1 in
      let f1 = nf_evar sigma1 f1 in
      let a1 = Array.map (nf_evar sigma1) a1 in
      not (equal t t1 &&
           equal f f1 && CArray.for_all2 equal a a1) in
    x :: uniquize (List.filter neq xs) in

((fun env c h ~k -> 
  do_once upat_that_matched (fun () -> 
    let failed_because_of_TC = ref false in
    try
      if not all_instances then match_upats_FO upats env sigma0 ise c;
      failed_because_of_TC:=match_upats_HO ~on_instance upats env sigma0 ise c;
      raise NoMatch
    with FoundUnif sigma_u -> 0,[sigma_u]
    | (NoMatch|NoProgress) when all_instances && instances () <> [] ->
      0, uniquize (instances ())
    | NoMatch when (not raise_NoMatch) ->
      if !failed_because_of_TC then
        errorstrm (source ()++strbrk"matches but type classes inference fails")
      else
        errorstrm (source () ++ str "does not match any subterm of the goal")
    | NoProgress when (not raise_NoMatch) ->
        let dir = match upats_origin with Some (d,_) -> d | _ ->
          CErrors.anomaly (str"mk_tpattern_matcher with no upats_origin.") in
        errorstrm (str"all matches of "++source()++
          str"are equal to the " ++ pr_dir_side (inv_dir dir))
    | NoProgress -> raise NoMatch);
  let sigma, _, ({up_f = pf; up_a = pa} as u) =
    if all_instances then assert_done_multires upat_that_matched
    else List.hd (snd(assert_done upat_that_matched)) in
(*   pp(lazy(str"sigma@tmatch=" ++ pr_evar_map None sigma)); *)
  if !skip_occ then ((*ignore(k env u.up_t 0);*) c) else
  let match_EQ = match_EQ env sigma u in
  let pn = Array.length pa in
  let rec subst_loop (env,h as acc) c' =
    if !skip_occ then c' else
    let f, a = splay_app sigma c' in
    if Array.length a >= pn && match_EQ f && unif_EQ_args env sigma pa a then
      let a1, a2 = Array.chop (Array.length pa) a in
      let fa1 = mkApp (f, a1) in
      let f' = if subst_occ () then k env u.up_t fa1 h else fa1 in
      mkApp (f', Array.map_left (subst_loop acc) a2)
    else
      (* TASSI: clear letin values to avoid unfolding *)
      let inc_h rd (env,h') =
        let ctx_item =
          match rd with
          | Context.Rel.Declaration.LocalAssum _ as x -> x
          | Context.Rel.Declaration.LocalDef (x,_,y) ->
              Context.Rel.Declaration.LocalAssum(x,y) in
        EConstr.push_rel ctx_item env, h' + 1 in
      let self acc c = EConstr.of_constr (subst_loop acc (EConstr.Unsafe.to_constr c)) in
      let f = EConstr.of_constr f in
      let f' = map_constr_with_binders_left_to_right sigma inc_h self acc f in
      let f' = EConstr.Unsafe.to_constr f' in
      mkApp (f', Array.map_left (subst_loop acc) a) in
  subst_loop (env,h) c) : find_P),
((fun () ->
  let sigma, uc, ({up_f = pf; up_a = pa} as u) =
    match !upat_that_matched with
    | Some (_,x) -> List.hd x | None when raise_NoMatch -> raise NoMatch
    | None -> CErrors.anomaly (str"companion function never called.") in
  let p' = mkApp (pf, pa) in
  if max_occ <= !nocc then p', u.up_dir, (sigma, uc, u.up_t)
  else errorstrm (str"Only " ++ int !nocc ++ str" < " ++ int max_occ ++
        str(String.plural !nocc " occurrence") ++ match upats_origin with
        | None -> str" of" ++ spc() ++ pr_constr_pat p'
        | Some (dir,rule) -> str" of the " ++ pr_dir_side dir ++ fnl() ++
            ws 4 ++ pr_constr_pat p' ++ fnl () ++ 
            str"of " ++ pr_constr_pat rule)) : conclude)

type ('ident, 'term) ssrpattern = 
  | T of 'term
  | In_T of 'term
  | X_In_T of 'ident * 'term     
  | In_X_In_T of 'ident * 'term     
  | E_In_X_In_T of 'term * 'ident * 'term     
  | E_As_X_In_T of 'term * 'ident * 'term     
        
let pr_pattern = function
  | T t -> prl_term t
  | In_T t -> str "in " ++ prl_term t
  | X_In_T (x,t) -> prl_term x ++ str " in " ++ prl_term t
  | In_X_In_T (x,t) -> str "in " ++ prl_term x ++ str " in " ++ prl_term t
  | E_In_X_In_T (e,x,t) ->
      prl_term e ++ str " in " ++ prl_term x ++ str " in " ++ prl_term t
  | E_As_X_In_T (e,x,t) ->
      prl_term e ++ str " as " ++ prl_term x ++ str " in " ++ prl_term t

let pr_pattern_w_ids = function
  | T t -> prl_term t
  | In_T t -> str "in " ++ prl_term t
  | X_In_T (x,t) -> pr_id x ++ str " in " ++ prl_term t
  | In_X_In_T (x,t) -> str "in " ++ pr_id x ++ str " in " ++ prl_term t
  | E_In_X_In_T (e,x,t) ->
      prl_term e ++ str " in " ++ pr_id x ++ str " in " ++ prl_term t
  | E_As_X_In_T (e,x,t) ->
      prl_term e ++ str " as " ++ pr_id x ++ str " in " ++ prl_term t

let pr_pattern_aux pr_constr = function
  | T t -> pr_constr t
  | In_T t -> str "in " ++ pr_constr t
  | X_In_T (x,t) -> pr_constr x ++ str " in " ++ pr_constr t
  | In_X_In_T (x,t) -> str "in " ++ pr_constr x ++ str " in " ++ pr_constr t
  | E_In_X_In_T (e,x,t) ->
      pr_constr e ++ str " in " ++ pr_constr x ++ str " in " ++ pr_constr t
  | E_As_X_In_T (e,x,t) ->
      pr_constr e ++ str " as " ++ pr_constr x ++ str " in " ++ pr_constr t
let pp_pattern (sigma, p) =
  pr_pattern_aux (fun t -> pr_constr_pat (EConstr.Unsafe.to_constr (pi3 (nf_open_term sigma sigma (EConstr.of_constr t))))) p
let pr_cpattern = pr_term

let wit_rpatternty = add_genarg "rpatternty" pr_pattern

let glob_ssrterm gs = function
  | k, (_, Some c), None ->
      let x = Tacintern.intern_constr gs c in
      k, (fst x, Some c), None
  | ct -> ct

(* This piece of code asserts the following notations are reserved *)
(* Reserved Notation "( a 'in' b )"        (at level 0).           *)
(* Reserved Notation "( a 'as' b )"        (at level 0).           *)
(* Reserved Notation "( a 'in' b 'in' c )" (at level 0).           *)
(* Reserved Notation "( a 'as' b 'in' c )" (at level 0).           *)
let glob_cpattern gs p =
  pp(lazy(str"globbing pattern: " ++ pr_term p));
  let glob x = pi2 (glob_ssrterm gs (mk_lterm x None)) in
  let encode k s l =
    let name = Name (Id.of_string ("_ssrpat_" ^ s)) in
    k, (mkRCast mkRHole (mkRLambda name mkRHole (mkRApp mkRHole l)), None), None in
  let bind_in t1 t2 =
    let mkCHole = mkCHole ~loc:None in let n = Name (destCVar t1) in
    fst (glob (mkCCast mkCHole (mkCLambda n mkCHole t2))) in
  let check_var t2 = if not (isCVar t2) then
    loc_error (constr_loc t2) "Only identifiers are allowed here" in
  match p with
  | _, (_, None), _ as x -> x
  | k, (v, Some t), _ as orig ->
     if k = 'x' then glob_ssrterm gs ('(', (v, Some t), None) else
     match t.CAst.v with
     | CNotation((InConstrEntrySomeLevel,"( _ in _ )"), ([t1; t2], [], [], [])) ->
         (try match glob t1, glob t2 with
         | (r1, None), (r2, None) -> encode k "In" [r1;r2]
         | (r1, Some _), (r2, Some _) when isCVar t1 ->
             encode k "In" [r1; r2; bind_in t1 t2]
         | (r1, Some _), (r2, Some _) -> encode k "In" [r1; r2]
         | _ -> CErrors.anomaly (str"where are we?.")
         with _ when isCVar t1 -> encode k "In" [bind_in t1 t2])
     | CNotation((InConstrEntrySomeLevel,"( _ in _ in _ )"), ([t1; t2; t3], [], [], [])) ->
         check_var t2; encode k "In" [fst (glob t1); bind_in t2 t3]
     | CNotation((InConstrEntrySomeLevel,"( _ as _ )"), ([t1; t2], [], [], [])) ->
         encode k "As" [fst (glob t1); fst (glob t2)]
     | CNotation((InConstrEntrySomeLevel,"( _ as _ in _ )"), ([t1; t2; t3], [], [], [])) ->
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

let subst_ssrterm s (k, c, ist) =
  k, Tacsubst.subst_glob_constr_and_expr s c, ist

let subst_rpattern s = function
  | T t -> T (subst_ssrterm s t)
  | In_T t -> In_T (subst_ssrterm s t)
  | X_In_T(x,t) -> X_In_T (x,subst_ssrterm s t)
  | In_X_In_T(x,t) -> In_X_In_T (x,subst_ssrterm s t)
  | E_In_X_In_T(e,x,t) -> E_In_X_In_T (subst_ssrterm s e,x,subst_ssrterm s t)
  | E_As_X_In_T(e,x,t) -> E_As_X_In_T (subst_ssrterm s e,x,subst_ssrterm s t)

let interp_ssrterm ist (k,t,_) = k, t, Some ist

let interp_rpattern s = function
  | T t -> T (interp_ssrterm s t)
  | In_T t -> In_T (interp_ssrterm s t)
  | X_In_T(x,t) -> X_In_T (interp_ssrterm s x,interp_ssrterm s t)
  | In_X_In_T(x,t) -> In_X_In_T (interp_ssrterm s x,interp_ssrterm s t)
  | E_In_X_In_T(e,x,t) ->
      E_In_X_In_T (interp_ssrterm s e,interp_ssrterm s x,interp_ssrterm s t)
  | E_As_X_In_T(e,x,t) ->
      E_As_X_In_T (interp_ssrterm s e,interp_ssrterm s x,interp_ssrterm s t)

let interp_rpattern0 ist gl t = Tacmach.project gl, interp_rpattern ist t

type cpattern = char * Genintern.glob_constr_and_expr * Geninterp.interp_sign option
let tag_of_cpattern = pi1
let loc_of_cpattern = loc_ofCG
let cpattern_of_term (c, t) ist = c, t, Some ist
type occ = (bool * int list) option

type rpattern = (cpattern, cpattern) ssrpattern

type pattern = Evd.evar_map * (constr, constr) ssrpattern

let id_of_cpattern (_, (c1, c2), _) =
  let open CAst in
  match DAst.get c1, c2 with
  | _, Some { v = CRef (qid, _) } when qualid_is_ident qid ->
    Some (qualid_basename qid)
  | _, Some { v = CAppExpl ((_, qid, _), []) } when qualid_is_ident qid ->
    Some (qualid_basename qid)
  | GRef (VarRef x, _), None -> Some x
  | _ -> None
let id_of_Cterm t = match id_of_cpattern t with
  | Some x -> x
  | None -> loc_error (loc_of_cpattern t) "Only identifiers are allowed here"

let of_ftactic ftac gl =
  let r = ref None in
  let tac = Ftactic.run ftac (fun ans -> r := Some ans; Proofview.tclUNIT ()) in
  let tac = Proofview.V82.of_tactic tac in
  let { sigma = sigma } = tac gl in
  let ans = match !r with
  | None -> assert false (* If the tactic failed we should not reach this point *)
  | Some ans -> ans
  in
  (sigma, ans)

let interp_wit wit ist gl x = 
  let globarg = in_gen (glbwit wit) x in
  let arg = interp_genarg ist globarg in
  let (sigma, arg) = of_ftactic arg gl in
  sigma, Value.cast (topwit wit) arg
let interp_open_constr ist gl gc =
  interp_wit wit_open_constr ist gl gc
let pf_intern_term gl (_, c, ist) = glob_constr ist (pf_env gl) (project gl) c

let interp_ssrterm ist gl t = Tacmach.project gl, interp_ssrterm ist t

let interp_term gl = function
  | (_, c, Some ist) ->
      on_snd EConstr.Unsafe.to_constr (interp_open_constr ist gl c)
  | _ -> errorstrm (str"interpreting a term with no ist")

let thin id sigma goal =
  let ids = Id.Set.singleton id in
  let env = Goal.V82.env sigma goal in
  let cl = Goal.V82.concl sigma goal in
  let sigma = Evd.clear_metas sigma in
  let ans =
    try Some (Evarutil.clear_hyps_in_evi env sigma (Environ.named_context_val env) cl ids)
    with Evarutil.ClearDependencyError _ -> None
  in
  match ans with
  | None -> sigma
  | Some (sigma, hyps, concl) ->
    let (gl,ev,sigma) = Goal.V82.mk_goal sigma hyps concl in
    let sigma = Goal.V82.partial_solution_to env sigma goal gl ev in
    sigma

(*
let pr_ist { lfun= lfun } =
  prlist_with_sep spc
    (fun (id, Geninterp.Val.Dyn(ty,_)) ->
        pr_id id ++ str":" ++ Geninterp.Val.pr ty) (Id.Map.bindings lfun)
*)

let interp_pattern ?wit_ssrpatternarg gl red redty =
  pp(lazy(str"interpreting: " ++ pr_pattern red));
  let xInT x y = X_In_T(x,y) and inXInT x y = In_X_In_T(x,y) in
  let inT x = In_T x and eInXInT e x t = E_In_X_In_T(e,x,t) in
  let eAsXInT e x t = E_As_X_In_T(e,x,t) in
  let mkG ?(k=' ') x ist = k,(x,None), ist in
  let ist_of (_,_,ist) = ist in
  let decode (_,_,ist as t) ?reccall f g =
    try match DAst.get (pf_intern_term gl t) with
    | GCast(t,CastConv c) when isGHole t && isGLambda c->
      let (x, c) = destGLambda c in
      f x (' ',(c,None),ist)
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
  let cleanup_XinE h x rp sigma =
    let h_k = match kind h with Evar (k,_) -> k | _ -> assert false in
    let to_clean, update = (* handle rename if x is already used *)
      let ctx = pf_hyps gl in
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
    let sigma0 = project gl in
    let new_evars =
      let rec aux acc t = match kind t with
      | Evar (k,_) ->
          if k = h_k || List.mem k acc || Evd.mem sigma0 k then acc else
          (update k; k::acc)
      | _ -> CoqConstr.fold aux acc t in 
      aux [] (nf_evar sigma rp) in
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
    | T(k,(t,None),ist) ->
      begin match DAst.get t with
      | GCast (c,CastConv t)
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
    | Some (ty, ist) -> let ty = ' ', ty, Some ist in
  match red with
  | T t -> T (combineCG t ty (mkCCast ?loc:(loc_ofCG t)) mkRCast)
  | X_In_T (x,t) ->
      let gty = pf_intern_term gl ty in
      E_As_X_In_T (mkG (mkRCast mkRHole gty) (ist_of ty), x, t)
  | E_In_X_In_T (e,x,t) ->
      let ty = mkG (pf_intern_term gl ty) (ist_of ty) in
      E_In_X_In_T (combineCG e ty (mkCCast ?loc:(loc_ofCG t)) mkRCast, x, t)
  | E_As_X_In_T (e,x,t) ->
      let ty = mkG (pf_intern_term gl ty) (ist_of ty) in
      E_As_X_In_T (combineCG e ty (mkCCast ?loc:(loc_ofCG t)) mkRCast, x, t)
  | red -> red in
  pp(lazy(str"typed as: " ++ pr_pattern_w_ids red));
  let mkXLetIn ?loc x (a,(g,c),ist) = match c with
  | Some b -> a,(g,Some (mkCLetIn ?loc x (mkCHole ~loc) b)), ist
  | None -> a,(DAst.make ?loc @@ GLetIn (x, DAst.make ?loc @@ GHole (BinderType x, IntroAnonymous, None), None, g), None), ist in
  match red with
  | T t -> let sigma, t = interp_term gl t in sigma, T t
  | In_T t -> let sigma, t = interp_term gl t in sigma, In_T t
  | X_In_T (x, rp) | In_X_In_T (x, rp) ->
    let mk x p = match red with X_In_T _ -> X_In_T(x,p) | _ -> In_X_In_T(x,p) in
    let rp = mkXLetIn (Name x) rp in
    let sigma, rp = interp_term gl rp in
    let _, h, _, rp = destLetIn rp in
    let sigma = cleanup_XinE h x rp sigma in
    let rp = subst1 h (nf_evar sigma rp) in
    sigma, mk h rp
  | E_In_X_In_T(e, x, rp) | E_As_X_In_T (e, x, rp) ->
    let mk e x p =
      match red with E_In_X_In_T _ ->E_In_X_In_T(e,x,p)|_->E_As_X_In_T(e,x,p) in
    let rp = mkXLetIn (Name x) rp in
    let sigma, rp = interp_term gl rp in
    let _, h, _, rp = destLetIn rp in
    let sigma = cleanup_XinE h x rp sigma in
    let rp = subst1 h (nf_evar sigma rp) in
    let sigma, e = interp_term (re_sig (sig_it gl) sigma) e in
    sigma, mk e h rp
;;
let interp_cpattern gl red redty = interp_pattern gl (T red) redty;;
let interp_rpattern ~wit_ssrpatternarg gl red = interp_pattern ~wit_ssrpatternarg gl red None;;

let id_of_pattern = function
  | _, T t -> (match kind t with Var id -> Some id | _ -> None)
  | _ -> None

(* The full occurrence set *)
let noindex = Some(false,[])

(* calls do_subst on every sub-term identified by (pattern,occ) *)
let eval_pattern ?raise_NoMatch env0 sigma0 concl0 pattern occ do_subst =
  let fs sigma x = nf_evar sigma x in
  let pop_evar sigma e p =
    let { Evd.evar_body = e_body } as e_def = Evd.find sigma e in
    let e_body = match e_body with Evar_defined c -> EConstr.Unsafe.to_constr c
    | _ -> errorstrm (str "Matching the pattern " ++ pr_constr_env env0 sigma0 p ++
          str " did not instantiate ?" ++ int (Evar.repr e) ++ spc () ++
          str "Does the variable bound by the \"in\" construct occur "++
          str "in the pattern?") in
    let sigma = 
      Evd.add (Evd.remove sigma e) e {e_def with Evd.evar_body = Evar_empty} in
    sigma, e_body in
  let ex_value hole =
    match kind hole with Evar (e,_) -> e | _ -> assert false in
  let mk_upat_for ?hack env sigma0 (sigma, t) ?(p=t) ok =
    let sigma,pat= mk_tpattern ?hack env sigma0 (sigma,p) ok L2R (fs sigma t) in
    sigma, [pat] in
  match pattern with
  | None -> do_subst env0 concl0 concl0 1, UState.empty
  | Some (sigma, (T rp | In_T rp)) -> 
    let rp = fs sigma rp in
    let ise = create_evar_defs sigma in
    let occ = match pattern with Some (_, T _) -> occ | _ -> noindex in
    let rp = mk_upat_for env0 sigma0 (ise, rp) all_ok in
    let find_T, end_T = mk_tpattern_matcher ?raise_NoMatch sigma0 occ rp in
    let concl = find_T env0 concl0 1 ~k:do_subst in
    let _, _, (_, us, _) = end_T () in
    concl, us
  | Some (sigma, (X_In_T (hole, p) | In_X_In_T (hole, p))) ->
    let p = fs sigma p in
    let occ = match pattern with Some (_, X_In_T _) -> occ | _ -> noindex in
    let ex = ex_value hole in
    let rp = mk_upat_for ~hack:true env0 sigma0 (sigma, p) all_ok in
    let find_T, end_T = mk_tpattern_matcher sigma0 noindex rp in
    (* we start from sigma, so hole is considered a rigid head *)
    let holep = mk_upat_for env0 sigma (sigma, hole) all_ok in
    let find_X, end_X = mk_tpattern_matcher ?raise_NoMatch sigma occ holep in
    let concl = find_T env0 concl0 1 ~k:(fun env c _ h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) (EConstr.of_constr c) (EConstr.of_constr p) in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h 
        ~k:(fun env _ -> do_subst env e_body))) in
    let _ = end_X () in let _, _, (_, us, _) = end_T () in
    concl, us
  | Some (sigma, E_In_X_In_T (e, hole, p)) ->
    let p, e = fs sigma p, fs sigma e in
    let ex = ex_value hole in
    let rp = mk_upat_for ~hack:true env0 sigma0 (sigma, p) all_ok in
    let find_T, end_T = mk_tpattern_matcher sigma0 noindex rp in
    let holep = mk_upat_for env0 sigma (sigma, hole) all_ok in
    let find_X, end_X = mk_tpattern_matcher sigma noindex holep in
    let re = mk_upat_for env0 sigma0 (sigma, e) all_ok in
    let find_E, end_E = mk_tpattern_matcher ?raise_NoMatch sigma0 occ re in
    let concl = find_T env0 concl0 1 ~k:(fun env c _ h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) (EConstr.of_constr c) (EConstr.of_constr p) in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h ~k:(fun env c _ h ->
        find_E env e_body h ~k:do_subst))) in
    let _,_,(_,us,_) = end_E () in
    let _ = end_X () in let _ = end_T () in
    concl, us
  | Some (sigma, E_As_X_In_T (e, hole, p)) ->
    let p, e = fs sigma p, fs sigma e in
    let ex = ex_value hole in
    let rp = 
      let e_sigma = unify_HO env0 sigma (EConstr.of_constr hole) (EConstr.of_constr e) in
      e_sigma, fs e_sigma p in
    let rp = mk_upat_for ~hack:true env0 sigma0 rp all_ok in
    let find_TE, end_TE = mk_tpattern_matcher sigma0 noindex rp in
    let holep = mk_upat_for env0 sigma (sigma, hole) all_ok in
    let find_X, end_X = mk_tpattern_matcher sigma occ holep in
    let concl = find_TE env0 concl0 1 ~k:(fun env c _ h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) (EConstr.of_constr c) (EConstr.of_constr p) in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h ~k:(fun env c _ h ->
        let e_sigma = unify_HO env sigma (EConstr.of_constr e_body) (EConstr.of_constr e) in
        let e_body = fs e_sigma e in
        do_subst env e_body e_body h))) in
    let _ = end_X () in let _,_,(_,us,_) = end_TE () in
    concl, us
;;

let redex_of_pattern ?(resolve_typeclasses=false) env (sigma, p) =
  let e = match p with
  | In_T _ | In_X_In_T _ -> CErrors.anomaly (str"pattern without redex.")
  | T e | X_In_T (e, _) | E_As_X_In_T (e, _, _) | E_In_X_In_T (e, _, _) -> e in
  let sigma =
    if not resolve_typeclasses then sigma
    else Typeclasses.resolve_typeclasses ~fail:false env sigma in
  nf_evar sigma e, Evd.evar_universe_context sigma

let fill_occ_pattern ?raise_NoMatch env sigma cl pat occ h =
  let do_make_rel, occ =
    if occ = Some(true,[]) then false, Some(false,[1]) else true, occ in
  let find_R, conclude =
    let r = ref None in
    (fun env c _ h' ->
       do_once r (fun () -> c);
       if do_make_rel then mkRel (h'+h-1) else c),
    (fun _ -> if !r = None then fst(redex_of_pattern env pat)
                           else assert_done r) in
  let cl, us =
    eval_pattern ?raise_NoMatch env sigma cl (Some pat) occ find_R in
  let e = conclude cl in
  (e, us), cl
;;

(* clenup interface for external use *)
let mk_tpattern ?p_origin env sigma0 sigma_t f dir c = 
  mk_tpattern ?p_origin env sigma0 sigma_t f dir c
;;

let eval_pattern ?raise_NoMatch env0 sigma0 concl0 pattern occ do_subst =
  fst (eval_pattern ?raise_NoMatch env0 sigma0 concl0 pattern occ do_subst)
;;

let pf_fill_occ env concl occ sigma0 p (sigma, t) ok h =
 let p = EConstr.Unsafe.to_constr p in
 let concl = EConstr.Unsafe.to_constr concl in
 let ise = create_evar_defs sigma in
 let ise, u = mk_tpattern env sigma0 (ise,EConstr.Unsafe.to_constr t) ok L2R p in
 let find_U, end_U =
   mk_tpattern_matcher ~raise_NoMatch:true sigma0 occ (ise,[u]) in
 let concl = find_U env concl h ~k:(fun _ _ _ -> mkRel) in
 let rdx, _, (sigma, uc, p) = end_U () in
 sigma, uc, EConstr.of_constr p, EConstr.of_constr concl, EConstr.of_constr rdx

let fill_occ_term env cl occ sigma0 (sigma, t) =
  try
    let sigma',uc,t',cl,_= pf_fill_occ env cl occ sigma0 t (sigma, t) all_ok 1 in
    if sigma' != sigma0 then CErrors.user_err Pp.(str "matching impacts evars")
    else cl, (Evd.merge_universe_context sigma' uc, t')
  with NoMatch -> try
    let sigma', uc, t' =
      unif_end env sigma0 (create_evar_defs sigma) t (fun _ -> true) in
    if sigma' != sigma0 then raise NoMatch
    else cl, (Evd.merge_universe_context sigma' uc, t')
  with _ ->
    errorstrm (str "partial term " ++ pr_constr_pat (EConstr.Unsafe.to_constr t)
            ++ str " does not match any subterm of the goal")

let pf_fill_occ_term gl occ t =
  let sigma0 = project gl and env = pf_env gl and concl = pf_concl gl in
  let cl,(_,t) = fill_occ_term env concl occ sigma0 t in
  cl, t

let cpattern_of_id id =
  ' ', (DAst.make @@ GRef (VarRef  id, None), None), Some Geninterp.({ lfun = Id.Map.empty; extra = Tacinterp.TacStore.empty })

let is_wildcard ((_, (l, r), _) : cpattern) : bool = match DAst.get l, r with
  | _, Some { CAst.v = CHole _ } | GHole _, None -> true
  | _ -> false

(* "ssrpattern" *)

let pr_rpattern = pr_pattern
  
let pf_merge_uc uc gl =
  re_sig (sig_it gl) (Evd.merge_universe_context (project gl) uc)

let pf_unsafe_merge_uc uc gl =
  re_sig (sig_it gl) (Evd.set_universe_context (project gl) uc)

(** All the pattern types reuse the same dynamic toplevel tag *)
let wit_ssrpatternarg = wit_rpatternty

let interp_rpattern = interp_rpattern ~wit_ssrpatternarg

let ssrpatterntac _ist arg gl =
  let pat = interp_rpattern gl arg in
  let sigma0 = project gl in
  let concl0 = pf_concl gl in
  let concl0 = EConstr.Unsafe.to_constr concl0 in
  let (t, uc), concl_x =
    fill_occ_pattern (pf_env gl) sigma0 concl0 pat noindex 1 in
  let t = EConstr.of_constr t in
  let concl_x = EConstr.of_constr concl_x in
  let gl, tty = pf_type_of gl t in
  let concl = EConstr.mkLetIn (Name (Id.of_string "selected"), t, tty, concl_x) in
  Proofview.V82.of_tactic (convert_concl concl DEFAULTcast) gl

(* Register "ssrpattern" tactic *)
let () =
  let mltac _ ist =
    let arg =
      let v = Id.Map.find (Names.Id.of_string "pattern") ist.lfun in
      Value.cast (topwit wit_ssrpatternarg) v in
    Proofview.V82.tactic (ssrpatterntac ist arg) in
  let name = { mltac_plugin = "ssrmatching_plugin"; mltac_tactic = "ssrpattern"; } in
  let () = Tacenv.register_ml_tactic name [|mltac|] in
  let tac =
    TacFun ([Name (Id.of_string "pattern")],
      TacML (CAst.make ({ mltac_name = name; mltac_index = 0 }, []))) in
  let obj () =
    Tacenv.register_ltac true false (Id.of_string "ssrpattern") tac in
  Mltop.declare_cache_obj obj "ssrmatching_plugin"

let ssrinstancesof arg gl =
  let ok rhs lhs ise = true in
(*   not (equal lhs (Evarutil.nf_evar ise rhs)) in *)
  let env, sigma, concl = pf_env gl, project gl, pf_concl gl in
  let concl = EConstr.Unsafe.to_constr concl in
  let sigma0, cpat = interp_cpattern gl arg None in
  let pat = match cpat with T x -> x | _ -> errorstrm (str"Not supported") in
  let etpat, tpat = mk_tpattern env sigma (sigma0,pat) (ok pat) L2R pat in
  let find, conclude =
    mk_tpattern_matcher ~all_instances:true ~raise_NoMatch:true
      sigma None (etpat,[tpat]) in
  let print env p c _ = ppnl (hov 1 (str"instance:" ++ spc() ++ pr_constr_env (pf_env gl) (gl.sigma) p ++ spc()
                                     ++ str "matches:" ++ spc() ++ pr_constr_env (pf_env gl) (gl.sigma)  c)); c in
  ppnl (str"BEGIN INSTANCES");
  try
    while true do
      ignore(find env concl 1 ~k:print)
    done; raise NoMatch
  with NoMatch -> ppnl (str"END INSTANCES"); tclIDTAC gl

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
