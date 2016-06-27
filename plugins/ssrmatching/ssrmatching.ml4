(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.freeze () ;;

(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "grammar/grammar.cma" i*)

open Names
open Pp
open Pcoq
open Genarg
open Constrarg
open Term
open Vars
open Topconstr
open Libnames
open Tactics
open Tacticals
open Termops
open Namegen
open Recordops
open Tacmach
open Coqlib
open Glob_term
open Util
open Evd
open Extend
open Goptions
open Tacexpr
open Proofview.Notations
open Tacinterp
open Pretyping
open Constr
open Tactic
open Extraargs
open Ppconstr
open Printer

open Globnames
open Misctypes
open Decl_kinds
open Evar_kinds
open Constrexpr
open Constrexpr_ops
open Notation_term
open Notation_ops
open Locus
open Locusops

DECLARE PLUGIN "ssrmatching_plugin"

type loc = Loc.t
let dummy_loc = Loc.ghost
let errorstrm = CErrors.errorlabstrm "ssrmatching"
let loc_error loc msg = CErrors.user_err_loc (loc, msg, str msg)
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
    { Goptions.optsync  = false;
      Goptions.optname  = "ssrmatching debugging";
      Goptions.optkey   = ["Debug";"SsrMatching"];
      Goptions.optdepr  = false;
      Goptions.optread  = (fun _ -> !pp_ref == ssr_pp);
      Goptions.optwrite = debug }
let pp s = !pp_ref s

(** Utils {{{ *****************************************************************)
let env_size env = List.length (Environ.named_context env)
let safeDestApp c =
  match kind_of_term c with App (f, a) -> f, a | _ -> c, [| |]
let get_index = function ArgArg i -> i | _ ->
  CErrors.anomaly (str"Uninterpreted index")
(* Toplevel constr must be globalized twice ! *)
let glob_constr ist genv = function
  | _, Some ce ->
    let vars = Id.Map.fold (fun x _ accu -> Id.Set.add x accu) ist.lfun Id.Set.empty in
    let ltacvars = { Constrintern.empty_ltac_sign with Constrintern.ltac_vars = vars } in
    Constrintern.intern_gen WithoutTypeConstraint ~ltacvars:ltacvars genv ce
  | rc, None -> rc

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
  msg_with Format.str_formatter (prc c);
  let s = Format.flush_str_formatter () ^ "$" in
  if guard s (skip_wschars s 0) then pr_paren prc c else prc c
(* More sensible names for constr printers *)
let pr_constr = pr_constr
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
let pr_term (k, c) = pr_guarded (guard_term k) pr_glob_constr_and_expr c
let prl_term (k, c) = pr_guarded (guard_term k) prl_glob_constr_and_expr c

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
let isCVar = function CRef (Ident _, _) -> true | _ -> false
let destCVar = function CRef (Ident (_, id), _) -> id | _ ->
  CErrors.anomaly (str"not a CRef")
let mkCHole loc = CHole (loc, None, IntroAnonymous, None)
let mkCLambda loc name ty t = 
   CLambdaN (loc, [[loc, name], Default Explicit, ty], t)
let mkCLetIn loc name bo t = 
   CLetIn (loc, (loc, name), bo, t)
let mkCCast loc t ty = CCast (loc,t, dC ty)
(** Constructors for rawconstr *)
let mkRHole = GHole (dummy_loc, InternalHole, IntroAnonymous, None)
let mkRApp f args = if args = [] then f else GApp (dummy_loc, f, args)
let mkRCast rc rt =  GCast (dummy_loc, rc, dC rt)
let mkRLambda n s t = GLambda (dummy_loc, n, Explicit, s, t)

(* ssrterm conbinators *)
let combineCG t1 t2 f g = match t1, t2 with
 | (x, (t1, None)), (_, (t2, None)) -> x, (g t1 t2, None)
 | (x, (_, Some t1)), (_, (_, Some t2)) -> x, (mkRHole, Some (f t1 t2))
 | _, (_, (_, None)) -> CErrors.anomaly (str"have: mixed C-G constr")
 | _ -> CErrors.anomaly (str"have: mixed G-C constr")
let loc_ofCG = function
 | (_, (s, None)) -> Glob_ops.loc_of_glob_constr s
 | (_, (_, Some s)) -> Constrexpr_ops.constr_loc s

let mk_term k c = k, (mkRHole, Some c)
let mk_lterm = mk_term ' '

let pf_type_of gl t = let sigma, ty = pf_type_of gl t in re_sig (sig_it gl)  sigma, ty

(* }}} *)

(** Profiling {{{ *************************************************************)
type profiler = { 
  profile : 'a 'b. ('a -> 'b) -> 'a -> 'b;
  reset : unit -> unit;
  print : unit -> unit }
let profile_now = ref false
let something_profiled = ref false
let profilers = ref []
let add_profiler f = profilers := f :: !profilers;;
let profile b =
  profile_now := b;
  if b then List.iter (fun f -> f.reset ()) !profilers;
  if not b then List.iter (fun f -> f.print ()) !profilers
;;
let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "ssrmatching profiling";
      Goptions.optkey   = ["SsrMatchingProfiling"];
      Goptions.optread  = (fun _ -> !profile_now);
      Goptions.optdepr  = false;
      Goptions.optwrite = profile }
let () =
  let prof_total = 
    let init = ref 0.0 in { 
    profile = (fun f x -> assert false);
    reset = (fun () -> init := Unix.gettimeofday ());
    print = (fun () -> if !something_profiled then
        prerr_endline 
           (Printf.sprintf "!! %-39s %10d %9.4f %9.4f %9.4f"
           "total" 0 (Unix.gettimeofday() -. !init) 0.0 0.0)) } in
  let prof_legenda = {
    profile = (fun f x -> assert false);
    reset = (fun () -> ());
    print = (fun () -> if !something_profiled then begin
        prerr_endline 
           (Printf.sprintf "!! %39s ---------- --------- --------- ---------" 
           (String.make 39 '-'));
        prerr_endline 
           (Printf.sprintf "!! %-39s %10s %9s %9s %9s" 
           "function" "#calls" "total" "max" "average") end) } in
  add_profiler prof_legenda;
  add_profiler prof_total
;;

let mk_profiler s =
  let total, calls, max = ref 0.0, ref 0, ref 0.0 in
  let reset () = total := 0.0; calls := 0; max := 0.0 in
  let profile f x =
    if not !profile_now then f x else
    let before = Unix.gettimeofday () in
    try
      incr calls;
      let res = f x in
      let after = Unix.gettimeofday () in
      let delta = after -. before in
      total := !total +. delta;
      if delta > !max then max := delta;
      res
    with exc ->
      let after = Unix.gettimeofday () in
      let delta = after -. before in
      total := !total +. delta;
      if delta > !max then max := delta;
      raise exc in
  let print () =
     if !calls <> 0 then begin
       something_profiled := true;
       prerr_endline
         (Printf.sprintf "!! %-39s %10d %9.4f %9.4f %9.4f" 
         s !calls !total !max (!total /. (float_of_int !calls))) end in
  let prof = { profile = profile; reset = reset; print = print } in
  add_profiler prof;
  prof
;;
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
  let evars = existential_opt_value sigma, Evd.universes sigma in 
  try let _ = Reduction.conv env p ~evars c in true with _ -> false

let unif_EQ_args env sigma pa a =
  let n = Array.length pa in
  let rec loop i = (i = n) || unif_EQ env sigma pa.(i) a.(i) && loop (i + 1) in
  loop 0

let prof_unif_eq_args = mk_profiler "unif_EQ_args";;
let unif_EQ_args env sigma pa a =
  prof_unif_eq_args.profile (unif_EQ_args env sigma pa) a 
;;

let unif_HO env ise p c = Evarconv.the_conv_x env p c ise

let unif_HOtype env ise p c = Evarconv.the_conv_x_leq env p c ise

let unif_HO_args env ise0 pa i ca =
  let n = Array.length pa in
  let rec loop ise j =
    if j = n then ise else loop (unif_HO env ise pa.(j) ca.(i + j)) (j + 1) in
  loop ise0 0

(* FO unification should boil down to calling w_unify with no_delta, but  *)
(* alas things are not so simple: w_unify does partial type-checking,     *)
(* which breaks down when the no-delta flag is on (as the Coq type system *)
(* requires full convertibility. The workaround here is to convert all    *)
(* evars into metas, since 8.2 does not TC metas. This means some lossage *)
(* for HO evars, though hopefully Miller patterns can pick up some of     *)
(* those cases, and HO matching will mop up the rest.                     *)
let flags_FO =
  let flags =
    { (Unification.default_no_delta_unify_flags ()).Unification.core_unify_flags
      with
        Unification.modulo_conv_on_closed_terms = None;
        Unification.modulo_eta = true;
        Unification.modulo_betaiota = true;
        Unification.modulo_delta_types = full_transparent_state}
  in
  { Unification.core_unify_flags = flags;
    Unification.merge_unify_flags = flags;
    Unification.subterm_unify_flags = flags;
    Unification.allow_K_in_toplevel_higher_order_unification = false;
    Unification.resolve_evars =
      (Unification.default_no_delta_unify_flags ()).Unification.resolve_evars
  }
let unif_FO env ise p c =
  Unification.w_unify env ise Reduction.CONV ~flags:flags_FO p c

(* Perform evar substitution in main term and prune substitution. *)
let nf_open_term sigma0 ise c =
  let s = ise and s' = ref sigma0 in
  let rec nf c' = match kind_of_term c' with
  | Evar ex ->
    begin try nf (existential_value s ex) with _ ->
    let k, a = ex in let a' = Array.map nf a in
    if not (Evd.mem !s' k) then
      s' := Evd.add !s' k (Evarutil.nf_evar_info s (Evd.find s k));
    mkEvar (k, a')
    end
  | _ -> map_constr nf c' in
  let copy_def k evi () =
    if evar_body evi != Evd.Evar_empty then () else
    match Evd.evar_body (Evd.find s k) with
    | Evar_defined c' -> s' := Evd.define k (nf c') !s'
    | _ -> () in
  let c' = nf c in let _ = Evd.fold copy_def sigma0 () in
  !s', Evd.evar_universe_context s, c'

let unif_end env sigma0 ise0 pt ok =
  let ise = Evarconv.consider_remaining_unif_problems env ise0 in
  let s, uc, t = nf_open_term sigma0 ise pt in
  let ise1 = create_evar_defs s in
  let ise1 = Evd.set_universe_context ise1 uc in
  let ise2 = Typeclasses.resolve_typeclasses ~fail:true env ise1 in
  if not (ok ise) then raise NoProgress else
  if ise2 == ise1 then (s, uc, t)
  else
    let s, uc', t = nf_open_term sigma0 ise2 t in
    s, Evd.union_evar_universe_context uc uc', t

let pf_unif_HO gl sigma pt p c =
  let env = pf_env gl in
  let ise = unif_HO env (create_evar_defs sigma) p c in
  unif_end env (project gl) ise pt (fun _ -> true)

let unify_HO env sigma0 t1 t2 =
  let sigma = unif_HO env sigma0 t1 t2 in
  let sigma, uc, _ = unif_end env sigma0 sigma t2 (fun _ -> true) in
  Evd.set_universe_context sigma uc

let pf_unify_HO gl t1 t2 =
  let env, sigma0, si = pf_env gl, project gl, sig_it gl in
  let sigma = unify_HO env sigma0 t1 t2 in
  re_sig si sigma

(* This is what the definition of iter_constr should be... *)
let iter_constr_LR f c = match kind_of_term c with
  | Evar (k, a) -> Array.iter f a
  | Cast (cc, _, t) -> f cc; f t  
  | Prod (_, t, b) | Lambda (_, t, b)  -> f t; f b
  | LetIn (_, v, t, b) -> f v; f t; f b
  | App (cf, a) -> f cf; Array.iter f a
  | Case (_, p, v, b) -> f v; f p; Array.iter f b
  | Fix (_, (_, t, b)) | CoFix (_, (_, t, b)) ->
    for i = 0 to Array.length t - 1 do f t.(i); f b.(i) done
  | _ -> ()

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
  | KpatEvar of existential_key
  | KpatLet
  | KpatLam
  | KpatRigid
  | KpatFlex
  | KpatProj of constant

type tpattern = {
  up_k : pattern_class;
  up_FO : constr;
  up_f : constr;
  up_a : constr array;
  up_t : constr;                      (* equation proof term or matched term *)
  up_dir : ssrdir;                    (* direction of the rule *)
  up_ok : constr -> evar_map -> bool; (* progess test for rewrite *)
  }

let all_ok _ _ = true

let proj_nparams c =
  try 1 + Recordops.find_projection_nparams (ConstRef c) with _ -> 0

let isFixed c = match kind_of_term c with
  | Var _ | Ind _ | Construct _ | Const _ -> true
  | _ -> false

let isRigid c = match kind_of_term c with
  | Prod _ | Sort _ | Lambda _ | Case _ | Fix _ | CoFix _ -> true
  | _ -> false

exception UndefPat

let hole_var = mkVar (id_of_string "_")
let pr_constr_pat c0 =
  let rec wipe_evar c =
    if isEvar c then hole_var else map_constr wipe_evar c in
  pr_constr (wipe_evar c0)

(* Turn (new) evars into metas *)
let evars_for_FO ~hack env sigma0 (ise0:evar_map) c0 =
  let ise = ref ise0 in
  let sigma = ref ise0 in
  let nenv = env_size env + if hack then 1 else 0 in
  let rec put c = match kind_of_term c with
  | Evar (k, a as ex) ->
    begin try put (existential_value !sigma ex)
    with NotInstantiatedEvar ->
    if Evd.mem sigma0 k then map_constr put c else
    let evi = Evd.find !sigma k in
    let dc = List.firstn (max 0 (Array.length a - nenv)) (evar_filtered_context evi) in
    let abs_dc (d, c) = function
    | Context.Named.Declaration.LocalDef (x, b, t) ->
        d, mkNamedLetIn x (put b) (put t) c
    | Context.Named.Declaration.LocalAssum (x, t) ->
        mkVar x :: d, mkNamedProd x (put t) c in
    let a, t =
      Context.Named.fold_inside abs_dc ~init:([], (put evi.evar_concl)) dc in
    let m = Evarutil.new_meta () in
    ise := meta_declare m t !ise;
    sigma := Evd.define k (applist (mkMeta m, a)) !sigma;
    put (existential_value !sigma ex)
    end
  | _ -> map_constr put c in
  let c1 = put c0 in !ise, c1

(* Compile a match pattern from a term; t is the term to fill. *)
(* p_origin can be passed to obtain a better error message     *)
let mk_tpattern ?p_origin ?(hack=false) env sigma0 (ise, t) ok dir p =
  let k, f, a =
    let f, a = Reductionops.whd_betaiota_stack ise p in
    match kind_of_term f with
    | Const (p,_) ->
      let np = proj_nparams p in
      if np = 0 || np > List.length a then KpatConst, f, a else
      let a1, a2 = List.chop np a in KpatProj p, applist(f, a1), a2
    | Var _ | Ind _ | Construct _ -> KpatFixed, f, a
    | Evar (k, _) ->
      if Evd.mem sigma0 k then KpatEvar k, f, a else
      if a <> [] then KpatFlex, f, a else 
      (match p_origin with None -> CErrors.error "indeterminate pattern"
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
  let k = match kind_of_term f with
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
  try match kind_of_term f with
  | Prod _ -> na Prod_cs
  | Sort s -> na (Sort_cs (family_of_sort s))
  | Const (c',_) when Constant.equal c' pc -> Array.length (snd (destApp u.up_f))
  | Var _ | Ind _ | Construct _ | Const _ -> na (Const_cs (global_of_constr f))
  | _ -> -1
  with Not_found -> -1

let isEvar_k k f =
  match kind_of_term f with Evar (k', _) -> k = k' | _ -> false

let nb_args c =
  match kind_of_term c with App (_, a) -> Array.length a | _ -> 0

let mkSubArg i a = if i = Array.length a then a else Array.sub a 0 i
let mkSubApp f i a = if i = 0 then f else mkApp (f, mkSubArg i a)

let splay_app ise =
  let rec loop c a = match kind_of_term c with
  | App (f, a') -> loop f (Array.append a' a)
  | Cast (c', _, _) -> loop c' a
  | Evar ex ->
    (try loop (existential_value ise ex) a with _ -> c, a)
  | _ -> c, a in
  fun c -> match kind_of_term c with
  | App (f, a) -> loop f a
  | Cast _ | Evar _ -> loop c [| |]
  | _ -> c, [| |]

let filter_upat i0 f n u fpats =
  let na = Array.length u.up_a in
  if n < na then fpats else
  let np = match u.up_k with
  | KpatConst when Term.eq_constr u.up_f f -> na
  | KpatFixed when Term.eq_constr u.up_f f -> na 
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

let filter_upat_FO i0 f n u fpats =
  let np = nb_args u.up_FO in
  if n < np then fpats else
  let ok = match u.up_k with
  | KpatConst -> Term.eq_constr u.up_f f 
  | KpatFixed -> Term.eq_constr u.up_f f 
  | KpatEvar k -> isEvar_k k f
  | KpatLet -> isLetIn f
  | KpatLam -> isLambda f
  | KpatRigid -> isRigid f
  | KpatProj pc -> Term.eq_constr f (mkConst pc)
  | KpatFlex -> i0 := n; true in
  if ok then begin if !i0 < np then i0 := np; (u, np) :: fpats end else fpats

exception FoundUnif of (evar_map * evar_universe_context * tpattern)
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
             try unif_HO env ise p c' with _ -> raise NoMatch in
           let lhs = mkSubApp f i a in
           let pt' = unif_end env sigma0 ise' u.up_t (u.up_ok lhs) in
           raise (FoundUnif (ungen_upat lhs pt' u))
       with FoundUnif (s,_,_) as sig_u when dont_impact_evars s -> raise sig_u
       | Not_found -> CErrors.anomaly (str"incomplete ise in match_upats_FO")
       | _ -> () in
    List.iter one_match fpats
  done;
  iter_constr_LR loop f; Array.iter loop a in
  try loop orig_c with Invalid_argument _ -> CErrors.anomaly (str"IN FO")

let prof_FO = mk_profiler "match_upats_FO";;
let match_upats_FO upats env sigma0 ise c =
  prof_FO.profile (match_upats_FO upats env sigma0) ise c
;;


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
          let ise' = unif_HO env ise pv v in
          unif_HO
            (Environ.push_rel (Context.Rel.Declaration.LocalAssum(x, t)) env)
            ise' pb b
        | KpatFlex | KpatProj _ ->
          unif_HO env ise u.up_f (mkSubApp f (i - Array.length u.up_a) a)
        | _ -> unif_HO env ise u.up_f f in
        let ise'' = unif_HO_args env ise' u.up_a (i - Array.length u.up_a) a in
        let lhs = mkSubApp f i a in
        let pt' = unif_end env sigma0 ise'' u.up_t (u.up_ok lhs) in
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

let prof_HO = mk_profiler "match_upats_HO";;
let match_upats_HO ~on_instance upats env sigma0 ise c =
  prof_HO.profile (match_upats_HO ~on_instance upats env sigma0) ise c
;;


let fixed_upat = function
| {up_k = KpatFlex | KpatEvar _ | KpatProj _} -> false 
| {up_t = t} -> not (occur_existential t)

let do_once r f = match !r with Some _ -> () | None -> r := Some (f ())

let assert_done r = 
  match !r with Some x -> x | None -> CErrors.anomaly (str"do_once never called")

let assert_done_multires r = 
  match !r with
  | None -> CErrors.anomaly (str"do_once never called")
  | Some (n, xs) ->
      r := Some (n+1,xs);
      try List.nth xs n with Failure _ -> raise NoMatch

type subst = Environ.env -> Term.constr -> Term.constr -> int -> Term.constr
type find_P = 
  Environ.env -> Term.constr -> int ->
  k:subst ->
     Term.constr
type conclude = unit ->
  Term.constr * ssrdir * (Evd.evar_map * Evd.evar_universe_context * Term.constr)

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
      let match_let f = match kind_of_term f with
      | LetIn (_, v, _, b) -> unif_EQ env sigma pv v && unif_EQ env' sigma pb b
      | _ -> false in match_let
    | KpatFixed -> Term.eq_constr u.up_f
    | KpatConst -> Term.eq_constr u.up_f
    | KpatLam -> fun c ->
       (match kind_of_term c with
       | Lambda _ -> unif_EQ env sigma u.up_f c
       | _ -> false)
    | _ -> unif_EQ env sigma u.up_f in
let p2t p = mkApp(p.up_f,p.up_a) in 
let source () = match upats_origin, upats with
  | None, [p] -> 
      (if fixed_upat p then str"term " else str"partial term ") ++ 
      pr_constr_pat (p2t p) ++ spc()
  | Some (dir,rule), [p] -> str"The " ++ pr_dir_side dir ++ str" of " ++ 
      pr_constr_pat rule ++ fnl() ++ ws 4 ++ pr_constr_pat (p2t p) ++ fnl()
  | Some (dir,rule), _ -> str"The " ++ pr_dir_side dir ++ str" of " ++ 
      pr_constr_pat rule ++ spc()
  | _, [] | None, _::_::_ ->
      CErrors.anomaly (str"mk_tpattern_matcher with no upats_origin") in
let on_instance, instances =
  let instances = ref [] in
  (fun x ->
    if all_instances then instances := !instances @ [x]
    else raise (FoundUnif x)),
  (fun () -> !instances) in
let rec uniquize = function
  | [] -> []
  | (sigma,_,{ up_f = f; up_a = a; up_t = t } as x) :: xs ->
    let t = Reductionops.nf_evar sigma t in
    let f = Reductionops.nf_evar sigma f in
    let a = Array.map (Reductionops.nf_evar sigma) a in
    let neq (sigma1,_,{ up_f = f1; up_a = a1; up_t = t1 }) =
      let t1 = Reductionops.nf_evar sigma1 t1 in
      let f1 = Reductionops.nf_evar sigma1 f1 in
      let a1 = Array.map (Reductionops.nf_evar sigma1) a1 in
      not (Term.eq_constr t t1 &&
           Term.eq_constr f f1 && CArray.for_all2 Term.eq_constr a a1) in
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
          CErrors.anomaly (str"mk_tpattern_matcher with no upats_origin") in
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
        Environ.push_rel ctx_item env, h' + 1 in
      let f' = map_constr_with_binders_left_to_right inc_h subst_loop acc f in
      mkApp (f', Array.map_left (subst_loop acc) a) in
  subst_loop (env,h) c) : find_P),
((fun () ->
  let sigma, uc, ({up_f = pf; up_a = pa} as u) =
    match !upat_that_matched with
    | Some (_,x) -> List.hd x | None when raise_NoMatch -> raise NoMatch
    | None -> CErrors.anomaly (str"companion function never called") in
  let p' = mkApp (pf, pa) in
  if max_occ <= !nocc then p', u.up_dir, (sigma, uc, u.up_t)
  else errorstrm (str"Only " ++ int !nocc ++ str" < " ++ int max_occ ++
        str(String.plural !nocc " occurence") ++ match upats_origin with
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
  pr_pattern_aux (fun t -> pr_constr_pat (pi3 (nf_open_term sigma sigma t))) p
let pr_cpattern = pr_term
let pr_rpattern _ _ _ = pr_pattern

let pr_option f = function None -> mt() | Some x -> f x
let pr_ssrpattern _ _ _ = pr_option pr_pattern
let pr_pattern_squarep = pr_option (fun r -> str "[" ++ pr_pattern r ++ str "]")
let pr_ssrpattern_squarep _ _ _ = pr_pattern_squarep
let pr_pattern_roundp = pr_option (fun r -> str "(" ++ pr_pattern r ++ str ")")
let pr_ssrpattern_roundp  _ _ _ = pr_pattern_roundp

let wit_rpatternty = add_genarg "rpatternty" pr_pattern

let glob_ssrterm gs = function
  | k, (_, Some c) as x -> k, 
      let x = Tacintern.intern_constr gs c in
      fst x, Some c
  | ct -> ct

let glob_rpattern s p =
  match p with
  | T t -> T (glob_ssrterm s t)
  | In_T t -> In_T (glob_ssrterm s t)
  | X_In_T(x,t) -> X_In_T (x,glob_ssrterm s t)
  | In_X_In_T(x,t) -> In_X_In_T (x,glob_ssrterm s t)
  | E_In_X_In_T(e,x,t) -> E_In_X_In_T (glob_ssrterm s e,x,glob_ssrterm s t)
  | E_As_X_In_T(e,x,t) -> E_As_X_In_T (glob_ssrterm s e,x,glob_ssrterm s t)

let subst_ssrterm s (k, c) = k, Tacsubst.subst_glob_constr_and_expr s c

let subst_rpattern s = function
  | T t -> T (subst_ssrterm s t)
  | In_T t -> In_T (subst_ssrterm s t)
  | X_In_T(x,t) -> X_In_T (x,subst_ssrterm s t)
  | In_X_In_T(x,t) -> In_X_In_T (x,subst_ssrterm s t)
  | E_In_X_In_T(e,x,t) -> E_In_X_In_T (subst_ssrterm s e,x,subst_ssrterm s t)
  | E_As_X_In_T(e,x,t) -> E_As_X_In_T (subst_ssrterm s e,x,subst_ssrterm s t)

ARGUMENT EXTEND rpattern
  TYPED AS rpatternty
  PRINTED BY pr_rpattern
  GLOBALIZED BY glob_rpattern
  SUBSTITUTED BY subst_rpattern
  | [ lconstr(c) ] -> [ T (mk_lterm c) ]
  | [ "in" lconstr(c) ] -> [ In_T (mk_lterm c) ]
  | [ lconstr(x) "in" lconstr(c) ] -> 
    [ X_In_T (mk_lterm x, mk_lterm c) ]
  | [ "in" lconstr(x) "in" lconstr(c) ] -> 
    [ In_X_In_T (mk_lterm x, mk_lterm c) ]
  | [ lconstr(e) "in" lconstr(x) "in" lconstr(c) ] -> 
    [ E_In_X_In_T (mk_lterm e, mk_lterm x, mk_lterm c) ]
  | [ lconstr(e) "as" lconstr(x) "in" lconstr(c) ] -> 
    [ E_As_X_In_T (mk_lterm e, mk_lterm x, mk_lterm c) ]
END



type cpattern = char * glob_constr_and_expr
let tag_of_cpattern = fst
let loc_of_cpattern = loc_ofCG
let cpattern_of_term t = t
type occ = (bool * int list) option

type rpattern = (cpattern, cpattern) ssrpattern
let pr_rpattern = pr_pattern

type pattern = Evd.evar_map * (Term.constr, Term.constr) ssrpattern


let id_of_cpattern = function
  | _,(_,Some (CRef (Ident (_, x), _))) -> Some x
  | _,(_,Some (CAppExpl (_, (_, Ident (_, x), _), []))) -> Some x
  | _,(GRef (_, VarRef x, _) ,None) -> Some x
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
  | None -> assert false (** If the tactic failed we should not reach this point *)
  | Some ans -> ans
  in
  (sigma, ans)

let interp_wit wit ist gl x = 
  let globarg = in_gen (glbwit wit) x in
  let arg = interp_genarg ist globarg in
  let (sigma, arg) = of_ftactic arg gl in
  sigma, Value.cast (topwit wit) arg
let interp_constr = interp_wit wit_constr
let interp_open_constr ist gl gc =
  interp_wit wit_open_constr ist gl gc
let pf_intern_term ist gl (_, c) = glob_constr ist (pf_env gl) c
let interp_term ist gl (_, c) = (interp_open_constr ist gl c)
let pr_ssrterm _ _ _ = pr_term
let input_ssrtermkind strm = match Compat.get_tok (stream_nth 0 strm) with
  | Tok.KEYWORD "(" -> '('
  | Tok.KEYWORD "@" -> '@'
  | _ -> ' '
let ssrtermkind = Gram.Entry.of_parser "ssrtermkind" input_ssrtermkind

(* This piece of code asserts the following notations are reserved *)
(* Reserved Notation "( a 'in' b )"        (at level 0).           *)
(* Reserved Notation "( a 'as' b )"        (at level 0).           *)
(* Reserved Notation "( a 'in' b 'in' c )" (at level 0).           *)
(* Reserved Notation "( a 'as' b 'in' c )" (at level 0).           *)
let glob_cpattern gs p =
  pp(lazy(str"globbing pattern: " ++ pr_term p));
  let glob x = snd (glob_ssrterm gs (mk_lterm x)) in
  let encode k s l =
    let name = Name (id_of_string ("_ssrpat_" ^ s)) in
    k, (mkRCast mkRHole (mkRLambda name mkRHole (mkRApp mkRHole l)), None) in
  let bind_in t1 t2 =
    let d = dummy_loc in let n = Name (destCVar t1) in
    fst (glob (mkCCast d (mkCHole d) (mkCLambda d n (mkCHole d) t2))) in
  let check_var t2 = if not (isCVar t2) then
    loc_error (constr_loc t2) "Only identifiers are allowed here" in
  match p with
  | _, (_, None) as x -> x
  | k, (v, Some t) as orig ->
     if k = 'x' then glob_ssrterm gs ('(', (v, Some t)) else
     match t with
     | CNotation(_, "( _ in _ )", ([t1; t2], [], [])) ->
         (try match glob t1, glob t2 with
         | (r1, None), (r2, None) -> encode k "In" [r1;r2]
         | (r1, Some _), (r2, Some _) when isCVar t1 ->
             encode k "In" [r1; r2; bind_in t1 t2]
         | (r1, Some _), (r2, Some _) -> encode k "In" [r1; r2]
         | _ -> CErrors.anomaly (str"where are we?")
         with _ when isCVar t1 -> encode k "In" [bind_in t1 t2])
     | CNotation(_, "( _ in _ in _ )", ([t1; t2; t3], [], [])) ->
         check_var t2; encode k "In" [fst (glob t1); bind_in t2 t3]
     | CNotation(_, "( _ as _ )", ([t1; t2], [], [])) ->
         encode k "As" [fst (glob t1); fst (glob t2)]
     | CNotation(_, "( _ as _ in _ )", ([t1; t2; t3], [], [])) ->
         check_var t2; encode k "As" [fst (glob t1); bind_in t2 t3]
     | _ -> glob_ssrterm gs orig
;;

let interp_ssrterm _ gl t = Tacmach.project gl, t

ARGUMENT EXTEND cpattern
     PRINTED BY pr_ssrterm
     INTERPRETED BY interp_ssrterm
     GLOBALIZED BY glob_cpattern SUBSTITUTED BY subst_ssrterm
     RAW_PRINTED BY pr_ssrterm
     GLOB_PRINTED BY pr_ssrterm
| [ "Qed" constr(c) ] -> [ mk_lterm c ]
END

let (!@) = Compat.to_coqloc

GEXTEND Gram
  GLOBAL: cpattern;
  cpattern: [[ k = ssrtermkind; c = constr ->
    let pattern = mk_term k c in
    if loc_ofCG pattern <> !@loc && k = '(' then mk_term 'x' c else pattern ]];
END

ARGUMENT EXTEND lcpattern
     TYPED AS cpattern
     PRINTED BY pr_ssrterm
     INTERPRETED BY interp_ssrterm
     GLOBALIZED BY glob_cpattern SUBSTITUTED BY subst_ssrterm
     RAW_PRINTED BY pr_ssrterm
     GLOB_PRINTED BY pr_ssrterm
| [ "Qed" lconstr(c) ] -> [ mk_lterm c ]
END

GEXTEND Gram
  GLOBAL: lcpattern;
  lcpattern: [[ k = ssrtermkind; c = lconstr ->
    let pattern = mk_term k c in
    if loc_ofCG pattern <> !@loc && k = '(' then mk_term 'x' c else pattern ]];
END

let thin id sigma goal =
  let ids = Id.Set.singleton id in
  let env = Goal.V82.env sigma goal in
  let cl = Goal.V82.concl sigma goal in
  let evdref = ref (Evd.clear_metas sigma) in
  let ans =
    try Some (Evarutil.clear_hyps_in_evi env evdref (Environ.named_context_val env) cl ids)
    with Evarutil.ClearDependencyError _ -> None
  in
  match ans with
  | None -> sigma
  | Some (hyps, concl) ->
    let sigma = !evdref in
    let (gl,ev,sigma) = Goal.V82.mk_goal sigma hyps concl (Goal.V82.extra sigma goal) in
    let sigma = Goal.V82.partial_solution_to sigma goal gl ev in
    sigma

let pr_ist { lfun= lfun } =
  prlist_with_sep spc
    (fun (id, Geninterp.Val.Dyn(ty,_)) ->
        pr_id id ++ str":" ++ Geninterp.Val.pr ty) (Id.Map.bindings lfun)

let interp_pattern ?wit_ssrpatternarg ist gl red redty =
  pp(lazy(str"interpreting: " ++ pr_pattern red));
  pp(lazy(str" in ist: " ++ pr_ist ist));
  let xInT x y = X_In_T(x,y) and inXInT x y = In_X_In_T(x,y) in
  let inT x = In_T x and eInXInT e x t = E_In_X_In_T(e,x,t) in
  let eAsXInT e x t = E_As_X_In_T(e,x,t) in
  let mkG ?(k=' ') x = k,(x,None) in
  let decode ist t ?reccall f g =
    try match (pf_intern_term ist gl t) with
    | GCast(_,GHole _,CastConv(GLambda(_,Name x,_,_,c))) -> f x (' ',(c,None))
    | GVar(_,id)
      when Id.Map.mem id ist.lfun &&
           not(Option.is_empty reccall) &&
           not(Option.is_empty wit_ssrpatternarg) ->
        let v = Id.Map.find id ist.lfun in
        Option.get reccall
          (Value.cast (topwit (Option.get wit_ssrpatternarg)) v)
    | it -> g t with e when CErrors.noncritical e -> g t in
  let decodeG t f g = decode ist (mkG t) f g in
  let bad_enc id _ = CErrors.anomaly (str"bad encoding for pattern "++str id) in
  let cleanup_XinE h x rp sigma =
    let h_k = match kind_of_term h with Evar (k,_) -> k | _ -> assert false in
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
      let rec aux acc t = match kind_of_term t with
      | Evar (k,_) ->
          if k = h_k || List.mem k acc || Evd.mem sigma0 k then acc else
          (update k; k::acc)
      | _ -> fold_constr aux acc t in 
      aux [] (Evarutil.nf_evar sigma rp) in
    let sigma = 
      List.fold_left (fun sigma e ->
        if Evd.is_defined sigma e then sigma else (* clear may be recursive *)
        if Option.is_empty !to_clean then sigma else
        let name = Option.get !to_clean in
        pp(lazy(pr_id name));
        thin name sigma e)
      sigma new_evars in
    sigma in
  let red = let rec decode_red (ist,red) = match red with
    | T(k,(GCast (_,GHole _,(CastConv(GLambda (_,Name id,_,_,t)))),None))
        when let id = string_of_id id in let len = String.length id in
        (len > 8 && String.sub id 0 8 = "_ssrpat_") ->
        let id = string_of_id id in let len = String.length id in
        (match String.sub id 8 (len - 8), t with
        | "In", GApp(_, _, [t]) -> decodeG t xInT (fun x -> T x)
        | "In", GApp(_, _, [e; t]) -> decodeG t (eInXInT (mkG e)) (bad_enc id)
        | "In", GApp(_, _, [e; t; e_in_t]) ->
            decodeG t (eInXInT (mkG e))
              (fun _ -> decodeG e_in_t xInT (fun _ -> assert false))
        | "As", GApp(_, _, [e; t]) -> decodeG t (eAsXInT (mkG e)) (bad_enc id)
        | _ -> bad_enc id ())
    | T t -> decode ist ~reccall:decode_red t xInT (fun x -> T x)
    | In_T t -> decode ist t inXInT inT
    | X_In_T (e,t) -> decode ist t (eInXInT e) (fun x -> xInT (id_of_Cterm e) x)
    | In_X_In_T (e,t) -> inXInT (id_of_Cterm e) t
    | E_In_X_In_T (e,x,rp) -> eInXInT e (id_of_Cterm x) rp
    | E_As_X_In_T (e,x,rp) -> eAsXInT e (id_of_Cterm x) rp in
    decode_red (ist,red) in
  pp(lazy(str"decoded as: " ++ pr_pattern_w_ids red));
  let red = match redty with None -> red | Some ty -> let ty = ' ', ty in
  match red with
  | T t -> T (combineCG t ty (mkCCast (loc_ofCG t)) mkRCast)
  | X_In_T (x,t) ->
      let ty = pf_intern_term ist gl ty in
      E_As_X_In_T (mkG (mkRCast mkRHole ty), x, t)
  | E_In_X_In_T (e,x,t) ->
      let ty = mkG (pf_intern_term ist gl ty) in
      E_In_X_In_T (combineCG e ty (mkCCast (loc_ofCG t)) mkRCast, x, t)
  | E_As_X_In_T (e,x,t) ->
      let ty = mkG (pf_intern_term ist gl ty) in
      E_As_X_In_T (combineCG e ty (mkCCast (loc_ofCG t)) mkRCast, x, t)
  | red -> red in
  pp(lazy(str"typed as: " ++ pr_pattern_w_ids red));
  let mkXLetIn loc x (a,(g,c)) = match c with
  | Some b -> a,(g,Some (mkCLetIn loc x (mkCHole loc) b))
  | None -> a,(GLetIn (loc,x,(GHole (loc, BinderType x, IntroAnonymous, None)), g), None) in
  match red with
  | T t -> let sigma, t = interp_term ist gl t in sigma, T t
  | In_T t -> let sigma, t = interp_term ist gl t in sigma, In_T t
  | X_In_T (x, rp) | In_X_In_T (x, rp) ->
    let mk x p = match red with X_In_T _ -> X_In_T(x,p) | _ -> In_X_In_T(x,p) in
    let rp = mkXLetIn dummy_loc (Name x) rp in
    let sigma, rp = interp_term ist gl rp in
    let _, h, _, rp = destLetIn rp in
    let sigma = cleanup_XinE h x rp sigma in
    let rp = subst1 h (Evarutil.nf_evar sigma rp) in
    sigma, mk h rp
  | E_In_X_In_T(e, x, rp) | E_As_X_In_T (e, x, rp) ->
    let mk e x p =
      match red with E_In_X_In_T _ ->E_In_X_In_T(e,x,p)|_->E_As_X_In_T(e,x,p) in
    let rp = mkXLetIn dummy_loc (Name x) rp in
    let sigma, rp = interp_term ist gl rp in
    let _, h, _, rp = destLetIn rp in
    let sigma = cleanup_XinE h x rp sigma in
    let rp = subst1 h (Evarutil.nf_evar sigma rp) in
    let sigma, e = interp_term ist (re_sig (sig_it gl) sigma) e in
    sigma, mk e h rp
;;
let interp_cpattern ist gl red redty = interp_pattern ist gl (T red) redty;;
let interp_rpattern ~wit_ssrpatternarg ist gl red = interp_pattern ~wit_ssrpatternarg ist gl red None;;

let id_of_pattern = function
  | _, T t -> (match kind_of_term t with Var id -> Some id | _ -> None)
  | _ -> None

(* The full occurrence set *)
let noindex = Some(false,[])

(* calls do_subst on every sub-term identified by (pattern,occ) *)
let eval_pattern ?raise_NoMatch env0 sigma0 concl0 pattern occ do_subst =
  let fs sigma x = Reductionops.nf_evar sigma x in
  let pop_evar sigma e p =
    let { Evd.evar_body = e_body } as e_def = Evd.find sigma e in
    let e_body = match e_body with Evar_defined c -> c
    | _ -> errorstrm (str "Matching the pattern " ++ pr_constr p ++
          str " did not instantiate ?" ++ int (Evar.repr e) ++ spc () ++
          str "Does the variable bound by the \"in\" construct occur "++
          str "in the pattern?") in
    let sigma = 
      Evd.add (Evd.remove sigma e) e {e_def with Evd.evar_body = Evar_empty} in
    sigma, e_body in
  let ex_value hole =
    match kind_of_term hole with Evar (e,_) -> e | _ -> assert false in
  let mk_upat_for ?hack env sigma0 (sigma, t) ?(p=t) ok =
    let sigma,pat= mk_tpattern ?hack env sigma0 (sigma,p) ok L2R (fs sigma t) in
    sigma, [pat] in
  match pattern with
  | None -> do_subst env0 concl0 concl0 1
  | Some (sigma, (T rp | In_T rp)) -> 
    let rp = fs sigma rp in
    let ise = create_evar_defs sigma in
    let occ = match pattern with Some (_, T _) -> occ | _ -> noindex in
    let rp = mk_upat_for env0 sigma0 (ise, rp) all_ok in
    let find_T, end_T = mk_tpattern_matcher ?raise_NoMatch sigma0 occ rp in
    let concl = find_T env0 concl0 1 do_subst in
    let _ = end_T () in
    concl
  | Some (sigma, (X_In_T (hole, p) | In_X_In_T (hole, p))) ->
    let p = fs sigma p in
    let occ = match pattern with Some (_, X_In_T _) -> occ | _ -> noindex in
    let ex = ex_value hole in
    let rp = mk_upat_for ~hack:true env0 sigma0 (sigma, p) all_ok in
    let find_T, end_T = mk_tpattern_matcher sigma0 noindex rp in
    (* we start from sigma, so hole is considered a rigid head *)
    let holep = mk_upat_for env0 sigma (sigma, hole) all_ok in
    let find_X, end_X = mk_tpattern_matcher ?raise_NoMatch sigma occ holep in
    let concl = find_T env0 concl0 1 (fun env c _ h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) c p in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h 
        (fun env _ -> do_subst env e_body))) in
    let _ = end_X () in let _ = end_T () in 
    concl
  | Some (sigma, E_In_X_In_T (e, hole, p)) ->
    let p, e = fs sigma p, fs sigma e in
    let ex = ex_value hole in
    let rp = mk_upat_for ~hack:true env0 sigma0 (sigma, p) all_ok in
    let find_T, end_T = mk_tpattern_matcher sigma0 noindex rp in
    let holep = mk_upat_for env0 sigma (sigma, hole) all_ok in
    let find_X, end_X = mk_tpattern_matcher sigma noindex holep in
    let re = mk_upat_for env0 sigma0 (sigma, e) all_ok in
    let find_E, end_E = mk_tpattern_matcher ?raise_NoMatch sigma0 occ re in
    let concl = find_T env0 concl0 1 (fun env c _ h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) c p in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h (fun env c _ h ->
        find_E env e_body h do_subst))) in
    let _ = end_E () in let _ = end_X () in let _ = end_T () in
    concl
  | Some (sigma, E_As_X_In_T (e, hole, p)) ->
    let p, e = fs sigma p, fs sigma e in
    let ex = ex_value hole in
    let rp = 
      let e_sigma = unify_HO env0 sigma hole e in
      e_sigma, fs e_sigma p in
    let rp = mk_upat_for ~hack:true env0 sigma0 rp all_ok in
    let find_TE, end_TE = mk_tpattern_matcher sigma0 noindex rp in
    let holep = mk_upat_for env0 sigma (sigma, hole) all_ok in
    let find_X, end_X = mk_tpattern_matcher sigma occ holep in
    let concl = find_TE env0 concl0 1 (fun env c _ h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) c p in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h (fun env c _ h ->
        let e_sigma = unify_HO env sigma e_body e in
        let e_body = fs e_sigma e in
        do_subst env e_body e_body h))) in
    let _ = end_X () in let _ = end_TE () in
    concl
;;

let redex_of_pattern ?(resolve_typeclasses=false) env (sigma, p) =
  let e = match p with
  | In_T _ | In_X_In_T _ -> CErrors.anomaly (str"pattern without redex")
  | T e | X_In_T (e, _) | E_As_X_In_T (e, _, _) | E_In_X_In_T (e, _, _) -> e in
  let sigma =
    if not resolve_typeclasses then sigma
    else Typeclasses.resolve_typeclasses ~fail:false env sigma in
  Reductionops.nf_evar sigma e, Evd.evar_universe_context sigma

let fill_occ_pattern ?raise_NoMatch env sigma cl pat occ h =
  let do_make_rel, occ =
    if occ = Some(true,[]) then false, Some(false,[1]) else true, occ in
  let find_R, conclude =
    let r = ref None in
    (fun env c _ h' ->
       do_once r (fun () -> c, Evd.empty_evar_universe_context);
       if do_make_rel then mkRel (h'+h-1) else c),
    (fun _ -> if !r = None then redex_of_pattern env pat else assert_done r) in
  let cl = eval_pattern ?raise_NoMatch env sigma cl (Some pat) occ find_R in
  let e = conclude cl in
  e, cl
;;

(* clenup interface for external use *)
let mk_tpattern ?p_origin env sigma0 sigma_t f dir c = 
  mk_tpattern ?p_origin env sigma0 sigma_t f dir c
;;

let pf_fill_occ env concl occ sigma0 p (sigma, t) ok h =
 let ise = create_evar_defs sigma in
 let ise, u = mk_tpattern env sigma0 (ise,t) ok L2R p in
 let find_U, end_U =
   mk_tpattern_matcher ~raise_NoMatch:true sigma0 occ (ise,[u]) in
 let concl = find_U env concl h (fun _ _ _ -> mkRel) in
 let rdx, _, (sigma, uc, p) = end_U () in
 sigma, uc, p, concl, rdx

let fill_occ_term env cl occ sigma0 (sigma, t) =
  try
    let sigma',uc,t',cl,_= pf_fill_occ env cl occ sigma0 t (sigma, t) all_ok 1 in
    if sigma' != sigma0 then CErrors.error "matching impacts evars"
    else cl, (Evd.merge_universe_context sigma' uc, t')
  with NoMatch -> try
    let sigma', uc, t' =
      unif_end env sigma0 (create_evar_defs sigma) t (fun _ -> true) in
    if sigma' != sigma0 then raise NoMatch
    else cl, (Evd.merge_universe_context sigma' uc, t')
  with _ ->
    errorstrm (str "partial term " ++ pr_constr_pat t
            ++ str " does not match any subterm of the goal")

let pf_fill_occ_term gl occ t =
  let sigma0 = project gl and env = pf_env gl and concl = pf_concl gl in
  let cl,(_,t) = fill_occ_term env concl occ sigma0 t in
  cl, t

let cpattern_of_id id = ' ', (GRef (dummy_loc, VarRef  id, None), None)

let is_wildcard = function
  | _,(_,Some (CHole _)|GHole _,None) -> true
  | _ -> false

(* "ssrpattern" *)
let pr_ssrpatternarg _ _ _ (_,cpat) = pr_rpattern cpat
let pr_ssrpatternarg_glob _ _ _ cpat = pr_rpattern cpat
let interp_ssrpatternarg ist gl p = project gl, (ist, p)

ARGUMENT EXTEND ssrpatternarg
  PRINTED BY pr_ssrpatternarg
  INTERPRETED BY interp_ssrpatternarg
  GLOBALIZED BY glob_rpattern
  RAW_PRINTED BY pr_ssrpatternarg_glob
  GLOB_PRINTED BY pr_ssrpatternarg_glob
| [ rpattern(pat) ] -> [ pat ]
END
  
let pf_merge_uc uc gl =
  re_sig (sig_it gl) (Evd.merge_universe_context (project gl) uc)

let pf_unsafe_merge_uc uc gl =
  re_sig (sig_it gl) (Evd.set_universe_context (project gl) uc)

let interp_rpattern ist gl red = interp_rpattern ~wit_ssrpatternarg ist gl red

let ssrpatterntac _ist (arg_ist,arg) gl =
  let pat = interp_rpattern arg_ist gl arg in
  let sigma0 = project gl in
  let concl0 = pf_concl gl in
  let (t, uc), concl_x =
    fill_occ_pattern (Global.env()) sigma0 concl0 pat noindex 1 in
  let gl, tty = pf_type_of gl t in
  let concl = mkLetIn (Name (id_of_string "selected"), t, tty, concl_x) in
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
    TacFun ([Some (Id.of_string "pattern")],
      TacML (Loc.ghost, { mltac_name = name; mltac_index = 0 }, [])) in
  let obj () =
    Tacenv.register_ltac true false (Id.of_string "ssrpattern") tac in
  Mltop.declare_cache_obj obj "ssrmatching_plugin"

let ssrinstancesof ist arg gl =
  let ok rhs lhs ise = true in
(*   not (Term.eq_constr lhs (Evarutil.nf_evar ise rhs)) in *)
  let env, sigma, concl = pf_env gl, project gl, pf_concl gl in
  let sigma0, cpat = interp_cpattern ist gl arg None in
  let pat = match cpat with T x -> x | _ -> errorstrm (str"Not supported") in
  let etpat, tpat = mk_tpattern env sigma (sigma0,pat) (ok pat) L2R pat in
  let find, conclude =
    mk_tpattern_matcher ~all_instances:true ~raise_NoMatch:true
      sigma None (etpat,[tpat]) in
  let print env p c _ = ppnl (hov 1 (str"instance:" ++ spc() ++ pr_constr p ++ spc() ++ str "matches:" ++ spc() ++ pr_constr c)); c in
  ppnl (str"BEGIN INSTANCES");
  try
    while true do
      ignore(find env concl 1 ~k:print)
    done; raise NoMatch
  with NoMatch -> ppnl (str"END INSTANCES"); tclIDTAC gl

TACTIC EXTEND ssrinstoftpat
| [ "ssrinstancesoftpat" cpattern(arg) ] -> [ Proofview.V82.tactic (ssrinstancesof ist arg) ]
END

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.unfreeze frozen_lexer ;;

(* vim: set filetype=ocaml foldmethod=marker: *)
