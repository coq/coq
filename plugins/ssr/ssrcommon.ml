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

open Util
open Names
open Evd
open Term
open Constr
open Context
open Termops
open Printer
open Locusops

open Ltac_plugin
open Proofview.Notations
open Libnames
open Ssrmatching_plugin
open Ssrmatching
open Ssrast
open Ssrprinters

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.get_keyword_state () ;;

let errorstrm x = CErrors.user_err x

let allocc = Some(false,[])

(** Bound assumption argument *)

(* The Ltac API does have a type for assumptions but it is level-dependent *)
(* and therefore impractical to use for complex arguments, so we substitute *)
(* our own to have a uniform representation. Also, we refuse to intern     *)
(* idents that match global/section constants, since this would lead to    *)
(* fragile Ltac scripts.                                                   *)

let hyp_id (SsrHyp (_, id)) = id

let hyp_err ?loc msg id =
  CErrors.user_err ?loc Pp.(str msg ++ Id.print id)

let not_section_id id = not (Termops.is_section_variable (Global.env ()) id)

let hyps_ids = List.map hyp_id

let rec check_hyps_uniq ids = function
  | SsrHyp (loc, id) :: _ when List.mem id ids ->
    hyp_err ?loc "Duplicate assumption " id
  | SsrHyp (_, id) :: hyps -> check_hyps_uniq (id :: ids) hyps
  | [] -> ()

let rec pf_check_hyps_uniq ids = function
  | SsrHyp (loc, id) :: _ when List.mem id ids ->
    Tacticals.tclZEROMSG ?loc Pp.(str "Duplicate assumption " ++ Id.print id)
  | SsrHyp (_, id) :: hyps -> pf_check_hyps_uniq (id :: ids) hyps
  | [] -> Proofview.tclUNIT ()

let check_hyp_exists hyps (SsrHyp(_, id)) =
  try ignore(Context.Named.lookup id hyps)
  with Not_found -> errorstrm Pp.(str"No assumption is named " ++ Id.print id)

let test_hyp_exists hyps (SsrHyp(_, id)) =
  try ignore(Context.Named.lookup id hyps); true
  with Not_found -> false

let hoik f = function Hyp x -> f x | Id x -> f x
let hoi_id = hoik hyp_id

let mk_hint tac = false, [Some tac]
let mk_orhint tacs = true, tacs
let nullhint = true, []
let nohint = false, []

open Pp

let errorstrm x = CErrors.user_err x
let anomaly s = CErrors.anomaly (str s)

(* Tentative patch from util.ml *)

let array_fold_right_from n f v a =
  let rec fold n =
    if n >= Array.length v then a else f v.(n) (fold (succ n))
  in
  fold n

let array_app_tl v l =
  if Array.length v = 0 then invalid_arg "array_app_tl";
  array_fold_right_from 1 (fun e l -> e::l) v l

let array_list_of_tl v =
  if Array.length v = 0 then invalid_arg "array_list_of_tl";
  array_fold_right_from 1 (fun e l -> e::l) v []

(* end patch *)

let option_assert_get o msg =
  match o with
  | None -> CErrors.anomaly msg
  | Some x -> x


(** Constructors for rawconstr *)
open Glob_term

let mkRHole = DAst.make @@ GHole (Evar_kinds.InternalHole, Namegen.IntroAnonymous, None)

let rec mkRHoles n = if n > 0 then mkRHole :: mkRHoles (n - 1) else []
let rec isRHoles cl = match cl with
| [] -> true
| c :: l -> match DAst.get c with GHole _ -> isRHoles l | _ -> false
let mkRApp f args = if args = [] then f else DAst.make @@ GApp (f, args)
let mkRVar id = DAst.make @@ GRef (GlobRef.VarRef id,None)
let mkRltacVar id = DAst.make @@ GVar (id)
let mkRCast rc rt =  DAst.make @@ GCast (rc, DEFAULTcast, rt)
let mkRType =  DAst.make @@ GSort (UAnonymous {rigid=true})
let mkRProp =  DAst.make @@ GSort (UNamed [GProp,0])
let mkRArrow rt1 rt2 = DAst.make @@ GProd (Anonymous, Explicit, rt1, rt2)
let mkRConstruct c = DAst.make @@ GRef (GlobRef.ConstructRef c,None)
let mkRInd mind = DAst.make @@ GRef (GlobRef.IndRef mind,None)
let mkRLambda n s t = DAst.make @@ GLambda (n, Explicit, s, t)

let rec mkRnat n =
  if n <= 0 then DAst.make @@ GRef (Coqlib.lib_ref "num.nat.O", None) else
  mkRApp (DAst.make @@ GRef (Coqlib.lib_ref "num.nat.S", None)) [mkRnat (n - 1)]

let glob_constr ist genv = function
  | _, Some ce ->
    let vars = Id.Map.fold (fun x _ accu -> Id.Set.add x accu) ist.Tacinterp.lfun Id.Set.empty in
    let ltacvars = {
      Constrintern.empty_ltac_sign with Constrintern.ltac_vars = vars } in
    Constrintern.intern_gen Pretyping.WithoutTypeConstraint ~ltacvars genv Evd.(from_env genv) ce
  | rc, None -> rc

let intern_term ist env (_, c) = glob_constr ist env c

(* Estimate a bound on the number of arguments of a raw constr. *)
(* This is not perfect, because the unifier may fail to         *)
(* typecheck the partial application, so we use a minimum of 5. *)
(* Also, we don't handle delayed or iterated coercions to       *)
(* FUNCLASS, which is probably just as well since these can     *)
(* lead to infinite arities.                                    *)

let splay_open_constr env (sigma, c) =
  let t = Retyping.get_type_of env sigma c in
  Reductionops.splay_prod env sigma t

let isAppInd env sigma c =
  let c = Reductionops.clos_whd_flags CClosure.all env sigma c in
  let c, _ = decompose_app_vect sigma c in
  EConstr.isInd sigma c

(** Generic argument-based globbing/typing utilities *)

let interp_refine env sigma ist ~concl rc =
  let constrvars = Tacinterp.extract_ltac_constr_values ist env in
  let vars = { Glob_ops.empty_lvar with
    Ltac_pretype.ltac_constrs = constrvars; ltac_genargs = ist.Tacinterp.lfun
  } in
  let kind = Pretyping.OfType concl in
  let flags = Pretyping.{
    use_coercions = true;
    use_typeclasses = UseTC;
    solve_unification_constraints = true;
    fail_evar = false;
    expand_evars = true;
    program_mode = false;
    polymorphic = false;
  }
  in
  let sigma, c = Pretyping.understand_ltac flags env sigma vars kind rc in
(*   ppdebug(lazy(str"sigma@interp_refine=" ++ pr_evar_map None sigma)); *)
  debug_ssr (fun () -> str"c@interp_refine=" ++ Printer.pr_econstr_env env sigma c);
  (sigma, c)


let interp_open_constr env sigma ist gc =
  let (sigma, (c, _)) = Tacinterp.interp_open_constr_with_bindings ist env sigma (gc, Tactypes.NoBindings) in
  (sigma, c)

let interp_term env sigma ist (_, c) = interp_open_constr env sigma ist c

let interp_hyp ist env sigma (SsrHyp (loc, id)) =
  let id' = Tacinterp.interp_hyp ist env sigma CAst.(make ?loc id) in
  if not_section_id id' then SsrHyp (loc, id') else
  hyp_err ?loc "Can't clear section hypothesis " id'

let interp_hyps ist env sigma ghyps =
  let hyps = List.map (interp_hyp ist env sigma) ghyps in
  check_hyps_uniq [] hyps; hyps

(* Old terms *)
let mk_term k c = k, (mkRHole, Some c)
let mk_lterm c = mk_term NoFlag c

(* New terms *)

let mk_ast_closure_term a t = {
  annotation = a;
  body = t;
  interp_env = None;
  glob_env = None;
}

let glob_ast_closure_term (ist : Genintern.glob_sign) t =
  let ist = {
    ast_ltacvars = ist.Genintern.ltacvars;
    ast_intern_sign = ist.Genintern.intern_sign;
    ast_extra = ist.Genintern.extra;
  } in
  { t with glob_env = Some ist }
let subst_ast_closure_term (_s : Mod_subst.substitution) t =
  (* _s makes sense only for glob constr *)
  t
let interp_ast_closure_term (ist : Geninterp.interp_sign) env sigma t =
  (* sigma is only useful if we want to interp *now*, later we have
   * a potentially different gl.sigma *)
  { t with interp_env = Some ist }

let ssrterm_of_ast_closure_term { body; annotation } =
  let c = match annotation with
    | `Parens -> InParens
    | `At -> WithAt
    | _ -> NoFlag in
  mk_term c body

let ssrdgens_of_parsed_dgens = function
  | [], clr -> { dgens = []; gens = []; clr }
  | [gens], clr -> { dgens = []; gens; clr }
  | [dgens;gens], clr -> { dgens; gens; clr }
  | _ -> assert false


let nbargs_open_constr env oc =
  let pl, _ = splay_open_constr env oc in List.length pl

let pf_nbargs env sigma c = nbargs_open_constr env (sigma, c)

let internal_names = ref []
let add_internal_name pt = internal_names := pt :: !internal_names
let is_internal_name s = List.exists (fun p -> p s) !internal_names

let mk_internal_id s =
  let s' = Printf.sprintf "_%s_" s in
  let s' = String.map (fun c -> if c = ' ' then '_' else c) s' in
  add_internal_name ((=) s'); Id.of_string s'

let same_prefix s t n =
  let rec loop i = i = n || s.[i] = t.[i] && loop (i + 1) in loop 0

let skip_digits s =
  let n = String.length s in
  let rec loop i = if i < n && is_digit s.[i] then loop (i + 1) else i in loop

let mk_tagged_id t i = Id.of_string (Printf.sprintf "%s%d_" t i)
let is_tagged t s =
  let n = String.length s - 1 and m = String.length t in
  m < n && s.[n] = '_' && same_prefix s t m && skip_digits s m = n

let evar_tag = "_evar_"
let _ = add_internal_name (is_tagged evar_tag)
let mk_evar_name n = Name (mk_tagged_id evar_tag n)

let ssr_anon_hyp = "Hyp"

let wildcard_tag = "_the_"
let wildcard_post = "_wildcard_"
let has_wildcard_tag s =
  let n = String.length s in let m = String.length wildcard_tag in
  let m' = String.length wildcard_post in
  n < m + m' + 2 && same_prefix s wildcard_tag m &&
  String.sub s (n - m') m' = wildcard_post &&
  skip_digits s m = n - m' - 2
let _ = add_internal_name has_wildcard_tag

let discharged_tag = "_discharged_"
let mk_discharged_id id =
  Id.of_string (Printf.sprintf "%s%s_" discharged_tag (Id.to_string id))
let has_discharged_tag s =
  let m = String.length discharged_tag and n = String.length s - 1 in
  m < n && s.[n] = '_' && same_prefix s discharged_tag m
let _ = add_internal_name has_discharged_tag
let is_discharged_id id = has_discharged_tag (Id.to_string id)

let max_suffix m (t, j0 as tj0) id  =
  let s = Id.to_string id in let n = String.length s - 1 in
  let dn = String.length t - 1 - n in let i0 = j0 - dn in
  if not (i0 >= m && s.[n] = '_' && same_prefix s t m) then tj0 else
  let rec loop i =
    if i < i0 && s.[i] = '0' then loop (i + 1) else
    if (if i < i0 then skip_digits s i = n else le_s_t i) then s, i else tj0
  and le_s_t i =
    let ds = s.[i] and dt = t.[i + dn] in
    if ds = dt then i = n || le_s_t (i + 1) else
    dt < ds && skip_digits s i = n in
  loop m

(** creates a fresh (w.r.t. `gl_ids` and internal names) inaccessible name of the form _tXX_ *)
let mk_anon_id t gl_ids =
  let m, si0, id0 =
    let s = ref (Printf.sprintf  "_%s_" t) in
    if is_internal_name !s then s := "_" ^ !s;
    let n = String.length !s - 1 in
    let rec loop i j =
      let d = !s.[i] in if not (is_digit d) then i + 1, j else
      loop (i - 1) (if d = '0' then j else i) in
    let m, j = loop (n - 1) n in m, (!s, j), Id.of_string_soft !s in
  if not (List.mem id0 gl_ids) then id0 else
  let s, i = List.fold_left (max_suffix m) si0 gl_ids in
  let open Bytes in
  let s = of_string s in
  let n = length s - 1 in
  let rec loop i =
    if get s i = '9' then (set s i '0'; loop (i - 1)) else
    if i < m then (set s n '0'; set s m '1'; cat s (of_string "_")) else
    (set s i (Char.chr (Char.code (get s i) + 1)); s) in
  Id.of_string_soft (Bytes.to_string (loop (n - 1)))

let convert_concl_no_check t = Tactics.convert_concl ~cast:false ~check:false t DEFAULTcast
let convert_concl ~check t = Tactics.convert_concl ~cast:false ~check t DEFAULTcast

(* Reduction that preserves the Prod/Let spine of the "in" tactical. *)

let inc_safe n = if n = 0 then n else n + 1
let rec safe_depth s c = match EConstr.kind s c with
| LetIn ({binder_name=Name x}, _, _, c') when is_discharged_id x -> safe_depth s c' + 1
| LetIn (_, _, _, c') | Prod (_, _, c') -> inc_safe (safe_depth s c')
| _ -> 0

let red_safe (r : Reductionops.reduction_function) e s c0 =
  let rec red_to e c n = match EConstr.kind s c with
  | Prod (x, t, c') when n > 0 ->
    let t' = r e s t in let e' = EConstr.push_rel (RelDecl.LocalAssum (x, t')) e in
    EConstr.mkProd (x, t', red_to e' c' (n - 1))
  | LetIn (x, b, t, c') when n > 0 ->
    let t' = r e s t in let e' = EConstr.push_rel (RelDecl.LocalAssum (x, t')) e in
    EConstr.mkLetIn (x, r e s b, t', red_to e' c' (n - 1))
  | _ -> r e s c in
  red_to e c0 (safe_depth s c0)

let is_id_constr sigma c = match EConstr.kind sigma c with
  | Lambda(_,_,c) when EConstr.isRel sigma c -> 1 = EConstr.destRel sigma c
  | _ -> false

let red_product_skip_id env sigma c = match EConstr.kind sigma c with
  | App(hd,args) when Array.length args = 1 && is_id_constr sigma hd -> args.(0)
  | _ -> try Tacred.red_product env sigma c with _ -> c

let ssrevaltac ist gtac = Tacinterp.tactic_of_value ist gtac

(** Open term to lambda-term coercion  *)(* {{{ ************************************)

(* This operation takes a goal gl and an open term (sigma, t), and   *)
(* returns a term t' where all the new evars in sigma are abstracted *)
(* with the mkAbs argument, i.e., for mkAbs = mkLambda then there is *)
(* some duplicate-free array args of evars of sigma such that the    *)
(* term mkApp (t', args) is convertible to t.                        *)
(* This makes a useful shorthand for local definitions in proofs,    *)
(* i.e., pose succ := _ + 1 means pose succ := fun n : nat => n + 1, *)
(* and, in context of the 4CT library, pose mid := maps id means *)
(*    pose mid := fun d : detaSet => @maps d d (@id (datum d))       *)
(* Note that this facility does not extend to set, which tries       *)
(* instead to fill holes by matching a goal subterm.                 *)
(* The argument to "have" et al. uses product abstraction, e.g.      *)
(*    have Hmid: forall s, (maps id s) = s.                          *)
(* stands for                                                        *)
(*    have Hmid: forall (d : dataSet) (s : seq d), (maps id s) = s.  *)
(* We also use this feature for rewrite rules, so that, e.g.,        *)
(*   rewrite: (plus_assoc _ 3).                                      *)
(* will execute as                                                   *)
(*   rewrite (fun n => plus_assoc n 3)                               *)
(* i.e., it will rewrite some subterm .. + (3 + ..) to .. + 3 + ...  *)
(* The convention is also used for the argument of the congr tactic, *)
(* e.g., congr (x + _ * 1).                                          *)

(* Replace new evars with lambda variables, retaining local dependencies *)
(* but stripping global ones. We use the variable names to encode the    *)
(* the number of dependencies, so that the transformation is reversible. *)

let env_size env = List.length (Environ.named_context env)

let resolve_typeclasses env sigma ~where ~fail =
  let filter =
    let evset = Evarutil.undefined_evars_of_term sigma where in
    fun k _ -> Evar.Set.mem k evset in
  Typeclasses.resolve_typeclasses ~filter ~fail env sigma

let abs_evars env sigma0 ?(rigid = []) (sigma, c0) =
  let c0 = Evarutil.nf_evar sigma c0 in
  let sigma0, ucst = sigma0, Evd.evar_universe_context sigma in
  let nenv = env_size env in
  let abs_evar n k =
    let open EConstr in
    let evi = Evd.find sigma k in
    let concl = evi.evar_concl in
    let dc = CList.firstn n (evar_filtered_context evi) in
    let abs_dc c = function
    | NamedDecl.LocalDef (x,b,t) -> mkNamedLetIn x b t (mkArrow t x.binder_relevance c)
    | NamedDecl.LocalAssum (x,t) -> mkNamedProd x t c in
    let t = Context.Named.fold_inside abs_dc ~init:concl dc in
    Evarutil.nf_evar sigma t in
  let rec put evlist c = match EConstr.kind sigma c with
  | Evar (k, a) ->
    if List.mem_assoc k evlist || Evd.mem sigma0 k || List.mem k rigid then evlist else
    let n = max 0 (List.length a - nenv) in
    let t = abs_evar n k in (k, (n, t)) :: put evlist t
  | _ -> EConstr.fold sigma put evlist c in
  let evlist = put [] c0 in
  if List.is_empty evlist then
    c0, [], ucst
  else
    let open EConstr in
    let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n, _)) :: evl -> if k = k' then i, n else lookup k (i + 1) evl in
    let rec get i c = match EConstr.kind sigma c with
    | Evar (ev, a) ->
      let j, n = lookup ev i evlist in
      if j = 0 then EConstr.map sigma (get i) c else if n = 0 then mkRel j else
      let a = Array.of_list a in
      mkApp (mkRel j, Array.init n (fun k -> get i a.(n - 1 - k)))
    | _ -> EConstr.map_with_binders sigma ((+) 1) get i c in
    let rec loop c i = function
    | (_, (n, t)) :: evl ->
      loop (mkLambda (make_annot (mk_evar_name n) Sorts.Relevant, get (i - 1) t, c)) (i - 1) evl
    | [] -> c in
    loop (get 1 c0) 1 evlist, List.map fst evlist, ucst

(* As before but if (?i : T(?j)) and (?j : P : Prop), then the lambda for i
 * looks like (fun evar_i : (forall pi : P. T(pi))) thanks to "loopP" and all
 * occurrences of evar_i are replaced by (evar_i evar_j) thanks to "app".
 *
 * If P can be solved by ssrautoprop (that defaults to trivial), then
 * the corresponding lambda looks like (fun evar_i : T(c)) where c is
 * the solution found by ssrautoprop.
 *)
let ssrautoprop_tac = ref (Proofview.Goal.enter (fun gl -> assert false))

(* Thanks to Arnaud Spiwack for this snippet *)
let call_on_evar env sigma tac e =
  try
    let tac = Proofview.Unsafe.tclSETGOALS [Proofview.with_empty_state e] <*> tac in
    let _, init = Proofview.init sigma [] in
    let name = Names.Id.of_string "legacy_pe" in
    let (_, final, _, _) = Proofview.apply ~name ~poly:false env tac init in
    let (gs, final) = Proofview.proofview final in
    let () = if (gs <> []) then errorstrm (str "Should we tell the user?") in
    final
  with Logic_monad.TacticFailure e as src ->
    let (_, info) = Exninfo.capture src in
    Exninfo.iraise (e, info)

open Pp
let pp _ = () (* FIXME *)
module Intset = Evar.Set

let abs_evars_pirrel env sigma0 (sigma, c0) =
  pp(lazy(str"==PF_ABS_EVARS_PIRREL=="));
  pp(lazy(str"c0= " ++ Printer.pr_econstr_env env sigma c0));
  let c0 = Evarutil.nf_evar sigma0 (Evarutil.nf_evar sigma c0) in
  let nenv = env_size env in
  let abs_evar n k =
    let open EConstr in
    let evi = Evd.find sigma k in
    let concl = evi.evar_concl in
    let dc = CList.firstn n (evar_filtered_context evi) in
    let abs_dc c = function
    | NamedDecl.LocalDef (x,b,t) -> mkNamedLetIn x b t (mkArrow t x.binder_relevance c)
    | NamedDecl.LocalAssum (x,t) -> mkNamedProd x t c in
    let t = Context.Named.fold_inside abs_dc ~init:concl dc in
    Evarutil.nf_evar sigma0 (Evarutil.nf_evar sigma t) in
  let rec put evlist c = match EConstr.kind sigma c with
  | Evar (k, a) ->
    if List.mem_assoc k evlist || Evd.mem sigma0 k then evlist else
    let n = max 0 (List.length a - nenv) in
    let k_ty =
      Retyping.get_sort_family_of
        env sigma (Evd.evar_concl (Evd.find sigma k)) in
    let is_prop = k_ty = InProp in
    let t = abs_evar n k in (k, (n, t, is_prop)) :: put evlist t
  | _ -> EConstr.fold sigma put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0 else
  let pr_constr t = Printer.pr_econstr_env env sigma (Reductionops.nf_beta env sigma0 t) in
  pp(lazy(str"evlist=" ++ pr_list (fun () -> str";")
    (fun (k,_) -> Evar.print k) evlist));
  let evplist =
    let depev = List.fold_left (fun evs (_,(_,t,_)) ->
        Intset.union evs (Evarutil.undefined_evars_of_term sigma t)) Intset.empty evlist in
    List.filter (fun (i,(_,_,b)) -> b && Intset.mem i depev) evlist in
  let evlist, evplist, sigma =
    if evplist = [] then evlist, [], sigma else
    List.fold_left (fun (ev, evp, sigma) (i, (_,t,_) as p) ->
      try
        let sigma = call_on_evar env sigma !ssrautoprop_tac i in
        List.filter (fun (j,_) -> j <> i) ev, evp, sigma
      with _ -> ev, p::evp, sigma) (evlist, [], sigma) (List.rev evplist) in
  let c0 = Evarutil.nf_evar sigma c0 in
  let evlist =
    List.map (fun (x,(y,t,z)) -> x,(y,Evarutil.nf_evar sigma t,z)) evlist in
  let evplist =
    List.map (fun (x,(y,t,z)) -> x,(y,Evarutil.nf_evar sigma t,z)) evplist in
  pp(lazy(str"c0= " ++ pr_constr c0));
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n,_,_)) :: evl -> if k = k' then i,n else lookup k (i + 1) evl in
  let open EConstr in
  let rec get evlist i c = match EConstr.kind sigma c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then EConstr.map sigma (get evlist i) c else if n = 0 then mkRel j else
    let a = Array.of_list a in
    mkApp (mkRel j, Array.init n (fun k -> get evlist i a.(n - 1 - k)))
  | _ -> EConstr.map_with_binders sigma ((+) 1) (get evlist) i c in
  let rec app extra_args i c = match decompose_app sigma c with
  | hd, args when isRel sigma hd && destRel sigma hd = i ->
      let j = destRel sigma hd in
      mkApp (mkRel j, Array.of_list (List.map (Vars.lift (i-1)) extra_args @ args))
  | _ -> EConstr.map_with_binders sigma ((+) 1) (app extra_args) i c in
  let rec loopP evlist c i = function
  | (_, (n, t, _)) :: evl ->
    let t = get evlist (i - 1) t in
    let n = Name (Id.of_string (ssr_anon_hyp ^ string_of_int n)) in
    loopP evlist (mkProd (make_annot n Sorts.Relevant, t, c)) (i - 1) evl
  | [] -> c in
  let rec loop c i = function
  | (_, (n, t, _)) :: evl ->
    let evs = Evarutil.undefined_evars_of_term sigma t in
    let t_evplist = List.filter (fun (k,_) -> Intset.mem k evs) evplist in
    let t = loopP t_evplist (get t_evplist 1 t) 1 t_evplist in
    let t = get evlist (i - 1) t in
    let extra_args =
      List.map (fun (k,_) -> mkRel (fst (lookup k i evlist)))
        (List.rev t_evplist) in
    let c = if extra_args = [] then c else app extra_args 1 c in
    loop (mkLambda (make_annot (mk_evar_name n) Sorts.Relevant, t, c)) (i - 1) evl
  | [] -> c in
  let res = loop (get evlist 1 c0) 1 evlist in
  pp(lazy(str"res= " ++ pr_constr res));
  List.length evlist, res

(* Strip all non-essential dependencies from an abstracted term, generating *)
(* standard names for the abstracted holes.                                 *)

let nb_evar_deps = function
  | Name id ->
    let s = Id.to_string id in
    if not (is_tagged evar_tag s) then 0 else
    let m = String.length evar_tag in
    (try int_of_string (String.sub s m (String.length s - 1 - m)) with _ -> 0)
  | _ -> 0

let type_id env sigma t = Id.of_string (Namegen.hdchar env sigma t)
let pfe_type_relevance_of env sigma t =
  let sigma, ty = Typing.type_of env sigma t in
  sigma, ty, Retyping.relevance_of_term env sigma t

let abs_cterm env sigma n c0 =
  let open EConstr in
  if n <= 0 then c0 else
  let noargs = [|0|] in
  let eva = Array.make n noargs in
  let rec strip i c = match EConstr.kind sigma c with
  | App (f, a) when isRel sigma f ->
    let j = i - destRel sigma f in
    if j >= n || eva.(j) = noargs then mkApp (f, Array.map (strip i) a) else
    let dp = eva.(j) in
    let nd = Array.length dp - 1 in
    let mkarg k = strip i a.(if k < nd then dp.(k + 1) - j else k + dp.(0)) in
    mkApp (f, Array.init (Array.length a - dp.(0)) mkarg)
  | _ -> EConstr.map_with_binders sigma ((+) 1) strip i c in
  let rec strip_ndeps j i c = match EConstr.kind sigma c with
  | Prod (x, t, c1) when i < j ->
    let dl, c2 = strip_ndeps j (i + 1) c1 in
    if Vars.noccurn sigma 1 c2 then dl, Vars.lift (-1) c2 else
    i :: dl, mkProd (x, strip i t, c2)
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c1' = destProd sigma c1 in
    let dl, c2 = strip_ndeps j (i + 1) c1' in
    if Vars.noccurn sigma 1 c2 then dl, Vars.lift (-1) c2 else
    i :: dl, mkLetIn (x, strip i b, strip i t, c2)
  | _ -> [], strip i c in
  let rec strip_evars i c = match EConstr.kind sigma c with
    | Lambda (x, t1, c1) when i < n ->
      let na = nb_evar_deps x.binder_name in
      let dl, t2 = strip_ndeps (i + na) i t1 in
      let na' = List.length dl in
      eva.(i) <- Array.of_list (na - na' :: dl);
      let x' =
        if na' = 0 then Name (type_id env sigma t2) else mk_evar_name na' in
      mkLambda ({x with binder_name=x'}, t2, strip_evars (i + 1) c1)
(*      if noccurn 1 c2 then lift (-1) c2 else
      mkLambda (Name (pf_type_id gl t2), t2, c2) *)
    | _ -> strip i c in
  strip_evars 0 c0

(* }}} *)

let rec constr_name sigma c = match EConstr.kind sigma c with
  | Var id -> Name id
  | Cast (c', _, _) -> constr_name sigma c'
  | Const (cn,_) -> Name (Label.to_id (Constant.label cn))
  | App (c', _) -> constr_name sigma c'
  | _ -> Anonymous

let pf_mkprod env sigma c ?(name=constr_name sigma c) cl =
  let sigma, t, r = pfe_type_relevance_of env sigma c in
  if name <> Anonymous || EConstr.Vars.noccurn sigma 1 cl then
    sigma, EConstr.mkProd (make_annot name r, t, cl)
  else
    sigma, EConstr.mkProd (make_annot (Name (type_id env sigma t)) r, t, cl)

(** look up a name in the ssreflect internals module *)
let ssrdirpath = DirPath.make [Id.of_string "ssreflect"]
let ssrqid name = Libnames.make_qualid ssrdirpath (Id.of_string name)
let mkSsrRef name =
  let qn = Format.sprintf "plugins.ssreflect.%s" name in
  if Coqlib.has_ref qn then Coqlib.lib_ref qn else
  CErrors.user_err Pp.(str "Small scale reflection library not loaded (" ++ str name ++ str ")")
let mkSsrRRef name = (DAst.make @@ GRef (mkSsrRef name,None)), None
let mkSsrConst env sigma name =
  EConstr.fresh_global env sigma (mkSsrRef name)

let mkProt env sigma t c =
  let sigma, prot = mkSsrConst env sigma "protect_term" in
  sigma, EConstr.mkApp (prot, [|t; c|])

let mkEtaApp c n imin =
  let open EConstr in
  if n = 0 then c else
  let nargs, mkarg =
    if n < 0 then -n, (fun i -> mkRel (imin + i)) else
    let imax = imin + n - 1 in n, (fun i -> mkRel (imax - i)) in
  mkApp (c, Array.init nargs mkarg)

let mkRefl env sigma t c =
  let (sigma, refl) = EConstr.fresh_global env sigma Coqlib.(lib_ref "core.eq.refl") in
  sigma, EConstr.mkApp (refl, [|t; c|])

let discharge_hyp (id', (id, mode)) =
  let open EConstr in
  let open Tacmach in
  Proofview.Goal.enter begin fun gl ->
  let cl' = Vars.subst_var id (Tacmach.pf_concl gl) in
  let decl = pf_get_hyp id gl in
  match decl, mode with
  | NamedDecl.LocalAssum _, _ | NamedDecl.LocalDef _, "(" ->
    let id' = {(NamedDecl.get_annot decl) with binder_name = Name id'} in
    Tactics.apply_type ~typecheck:true
                               (mkProd (id', NamedDecl.get_type decl, cl')) [mkVar id]
  | NamedDecl.LocalDef (_, v, t), _ ->
    let id' = {(NamedDecl.get_annot decl) with binder_name = Name id'} in
    convert_concl ~check:true (mkLetIn (id', v, t, cl'))
  end

let view_error s gv =
  Tacticals.tclZEROMSG (str ("Cannot " ^ s ^ " view ") ++ pr_term gv)


open Locus
(****************************** tactics ***********************************)

let rewritetac ?(under=false) dir c =
  (* Due to the new optional arg ?tac, application shouldn't be too partial *)
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun _ ->
      Equality.general_rewrite ~where:None ~l2r:(dir = L2R) AllOccurrences ~freeze:true ~dep:false ~with_evars:false (c, Tactypes.NoBindings) <*>
        if under then Proofview.cycle 1 else Proofview.tclUNIT ()
  end

(**********************`:********* hooks ************************************)

type name_hint = (int * EConstr.types array) option ref

let abs_ssrterm ?(resolve_typeclasses=false) ist env sigma t =
  let sigma0 = sigma in
  let sigma, ct = interp_term env sigma ist t in
  let t =
    if not resolve_typeclasses then (sigma, ct)
    else
       let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
       sigma, Evarutil.nf_evar sigma ct in
  let c, abstracted_away, ucst = abs_evars env sigma0 t in
  let n = List.length abstracted_away in
  let t = abs_cterm env sigma0 n c in
  let sigma = Evd.merge_universe_context sigma0 ucst in
  sigma, t, n

let top_id = mk_internal_id "top assumption"

let ssr_n_tac seed n =
  Proofview.Goal.enter begin fun gl ->
  let name = if n = -1 then seed else ("ssr" ^ seed ^ string_of_int n) in
  let fail msg = CErrors.user_err (Pp.str msg) in
  let tacname =
    try Tacenv.locate_tactic (Libnames.qualid_of_ident (Id.of_string name))
    with Not_found -> try Tacenv.locate_tactic (ssrqid name)
    with Not_found ->
      if n = -1 then fail "The ssreflect library was not loaded"
      else fail ("The tactic "^name^" was not found") in
  let tacexpr = Tacexpr.Reference (ArgArg (Loc.tag @@ tacname)) in
  Tacinterp.eval_tactic @@ CAst.make (Tacexpr.TacArg tacexpr)
  end

let donetac n = ssr_n_tac "done" n

open Constrexpr
open Util

(** Constructors for constr_expr *)
let mkCProp loc = CAst.make ?loc @@ CSort (UNamed [CProp,0])
let mkCType loc = CAst.make ?loc @@ CSort (UAnonymous {rigid=true})
let mkCVar ?loc id = CAst.make ?loc @@ CRef (qualid_of_ident ?loc id, None)
let rec mkCHoles ?loc n =
  if n <= 0 then [] else (CAst.make ?loc @@ CHole (None, Namegen.IntroAnonymous, None)) :: mkCHoles ?loc (n - 1)
let mkCHole loc = CAst.make ?loc @@ CHole (None, Namegen.IntroAnonymous, None)
let mkCLambda ?loc name ty t =  CAst.make ?loc @@
   CLambdaN ([CLocalAssum([CAst.make ?loc name], Default Explicit, ty)], t)
let mkCArrow ?loc ty t = CAst.make ?loc @@
   CProdN ([CLocalAssum([CAst.make Anonymous], Default Explicit, ty)], t)
let mkCCast ?loc t ty = CAst.make ?loc @@ CCast (t, DEFAULTcast, ty)

let rec isCHoles = function { CAst.v = CHole _ } :: cl -> isCHoles cl | cl -> cl = []
let rec isCxHoles = function ({ CAst.v = CHole _ }, None) :: ch -> isCxHoles ch | _ -> false

let pf_interp_ty ?(resolve_typeclasses=false) env sigma0 ist ty =
   let n_binders = ref 0 in
   let ty = match ty with
   | a, (t, None) ->
    let rec force_type ty = DAst.(map (function
     | GProd (x, k, s, t) -> incr n_binders; GProd (x, k, s, force_type t)
     | GLetIn (x, v, oty, t) -> incr n_binders; GLetIn (x, v, oty, force_type t)
     | _ -> DAst.get (mkRCast ty mkRType))) ty in
     a, (force_type t, None)
   | _, (_, Some ty) ->
    let rec force_type ty = CAst.(map (function
     | CProdN (abs, t) ->
       n_binders := !n_binders + List.length (List.flatten (List.map (function CLocalAssum (nal,_,_) -> nal | CLocalDef (na,_,_) -> [na] | CLocalPattern _ -> (* We count a 'pat for 1; TO BE CHECKED *) [CAst.make Name.Anonymous]) abs));
       CProdN (abs, force_type t)
     | CLetIn (n, v, oty, t) -> incr n_binders; CLetIn (n, v, oty, force_type t)
     | _ -> (mkCCast ty (mkCType None)).v)) ty in
     mk_term NoFlag (force_type ty) in
   let strip_cast (sigma, t) =
     let open EConstr in
     let rec aux t = match kind_of_type sigma t with
     | CastType (t, ty) when !n_binders = 0 && isSort sigma ty -> t
     | ProdType(n,s,t) -> decr n_binders; mkProd (n, s, aux t)
     | LetInType(n,v,ty,t) -> decr n_binders; mkLetIn (n, v, ty, aux t)
     | _ -> anomaly "pf_interp_ty: ssr Type cast deleted by typecheck" in
     sigma, aux t in
   let sigma, cty as ty = strip_cast (interp_term env sigma0 ist ty) in
   let ty =
     if not resolve_typeclasses then ty
     else
       let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
       sigma, Evarutil.nf_evar sigma cty in
   let c, evs, ucst = abs_evars env sigma0 ty in
   let n = List.length evs in
   let lam_c = abs_cterm env sigma0 n c in
   let ctx, c = EConstr.decompose_lam_n_assum sigma n lam_c in
   let sigma0 = Evd.merge_universe_context sigma0 ucst in
   sigma0, n, EConstr.it_mkProd_or_LetIn c ctx, lam_c

(* TASSI: given (c : ty), generates (c ??? : ty[???/...]) with m evars *)
exception NotEnoughProducts
let saturate ?(beta=false) ?(bi_types=false) env sigma c ?(ty=Retyping.get_type_of env sigma c) m
=
  let rec loop ty args sigma n =
  let open EConstr in
  if n = 0 then
    let args = List.rev args in
     (if beta then Reductionops.whd_beta env sigma else fun x -> x)
      (EConstr.mkApp (c, Array.of_list (List.map pi2 args))), ty, args, sigma
  else match kind_of_type sigma ty with
  | ProdType (_, src, tgt) ->
      let sigma = create_evar_defs sigma in
      let argty = if bi_types then Reductionops.nf_betaiota env sigma src else src in
      let (sigma, x) = Evarutil.new_evar env sigma argty in
      loop (EConstr.Vars.subst1 x tgt) ((m - n,x,argty) :: args) sigma (n-1)
  | CastType (t, _) -> loop t args sigma n
  | LetInType (_, v, _, t) -> loop (EConstr.Vars.subst1 v t) args sigma n
  | SortType _ -> assert false
  | AtomicType _ ->
      let ty =  (* FIXME *)
        (Reductionops.whd_all env sigma) ty in
      match kind_of_type sigma ty with
      | ProdType _ -> loop ty args sigma n
      | _ -> raise NotEnoughProducts
  in
   loop ty [] sigma m

let dependent_apply_error =
  try CErrors.user_err (Pp.str "Could not fill dependent hole in \"apply\"")
  with err -> err

(* TASSI: Sometimes Coq's apply fails. According to my experience it may be
 * related to goals that are products and with beta redexes. In that case it
 * guesses the wrong number of implicit arguments for your lemma. What follows
 * is just like apply, but with a user-provided number n of implicits.
 *
 * Refine.refine function that handles type classes and evars but fails to
 * handle "dependently typed higher order evars".
 *
 * Refiner.refiner that does not handle metas with a non ground type but works
 * with dependently typed higher order metas. *)
let applyn ~with_evars ?beta ?(with_shelve=false) ?(first_goes_last=false) n t =
  if with_evars then
    let refine =
      Proofview.Goal.enter begin fun gl ->
      Refine.refine ~typecheck:false begin fun sigma ->
      let env = Proofview.Goal.env gl in
      let concl = Proofview.Goal.concl gl in
      let t, ty, args, sigma = saturate ?beta ~bi_types:true env sigma t n in
      let sigma = unify_HO env sigma ty concl in
      (* Set our own set of goals. In theory saturate generates them in the
         right order, so we could just return sigma directly, but explicit is
         better than implicit. *)
      let sigma = Evd.push_future_goals (snd @@ Evd.pop_future_goals sigma) in
      let fold sigma (_, e, _) = match EConstr.kind sigma e with
      | Evar (evk, _) -> Evd.declare_future_goal evk sigma
      | _ -> sigma
      in
      let sigma = List.fold_left fold sigma args in
      (sigma, t)
      end
      end
    in
    Tacticals.tclTHENLIST [
      refine;
      Proofview.(if with_shelve then shelve_unifiable else tclUNIT ());
      Proofview.(if first_goes_last then cycle 1 else tclUNIT ())
    ]
  else
    Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let t, sigma = if n = 0 then t, sigma else
      let rec loop sigma bo args = function (* saturate with metas *)
        | 0 -> EConstr.mkApp (t, Array.of_list (List.rev args)), sigma
        | n -> match EConstr.kind sigma bo with
          | Lambda (_, ty, bo) ->
              if not (EConstr.Vars.closed0 sigma ty) then
                raise dependent_apply_error;
              let m = Evarutil.new_meta () in
              loop (meta_declare m ty sigma) bo ((EConstr.mkMeta m)::args) (n-1)
          | _ -> assert false
      in loop sigma t [] n in
    pp(lazy(str"Refiner.refiner " ++ Printer.pr_econstr_env env sigma t));
    Tacticals.tclTHENLIST [
      Logic.refiner ~check:false EConstr.Unsafe.(to_constr t);
      Proofview.(if first_goes_last then cycle 1 else tclUNIT ())
    ]
  end

let refine_with ?(first_goes_last=false) ?beta ?(with_evars=true) oc =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let uct = Evd.evar_universe_context (fst oc) in
  let n, oc = abs_evars_pirrel env sigma oc in
  Proofview.Unsafe.tclEVARS (Evd.set_universe_context sigma uct) <*>
  Proofview.tclORELSE (applyn ~with_evars ~first_goes_last ~with_shelve:true ?beta n oc)
    (fun _ -> Proofview.tclZERO dependent_apply_error)
  end

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.set_keyword_state frozen_lexer ;;

(** Basic tactics *)

let rec fst_prod red tac = Proofview.Goal.enter begin fun gl ->
  let concl = Proofview.Goal.concl gl in
  match EConstr.kind (Proofview.Goal.sigma gl) concl with
  | Prod (id,_,tgt) | LetIn(id,_,_,tgt) -> tac id.binder_name
  | _ -> if red then Tacticals.tclZEROMSG (str"No product even after head-reduction.")
         else Tacticals.tclTHEN Tactics.hnf_in_concl (fst_prod true tac)
end

let introid ?(orig=ref Anonymous) name =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let g = Proofview.Goal.concl gl in
   match EConstr.kind sigma g with
   | App (hd, _) when EConstr.isLambda sigma hd ->
      convert_concl_no_check (Reductionops.whd_beta env sigma g)
   | _ -> Tacticals.tclIDTAC
  end <*>
    (fst_prod false (fun id -> orig := id; Tactics.intro_mustbe_force name))

let anontac decl =
  Proofview.Goal.enter begin fun gl ->
  let id =  match RelDecl.get_name decl with
  | Name id ->
    if is_discharged_id id then id else mk_anon_id (Id.to_string id) (Tacmach.pf_ids_of_hyps gl)
  | _ -> mk_anon_id ssr_anon_hyp (Tacmach.pf_ids_of_hyps gl) in
  introid id
  end

let rec intro_anon () =
  let open Tacmach in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let d = List.hd (fst (EConstr.decompose_prod_n_assum (project gl) 1 (pf_concl gl))) in
  Proofview.tclORELSE (anontac d)
    (fun (err0, info) -> Proofview.tclORELSE
        (Tactics.red_in_concl <*> intro_anon ()) (fun _ -> Proofview.tclZERO ~info err0))
  end

let intro_anon = intro_anon ()

let is_pf_var sigma c =
  EConstr.isVar sigma c && not_section_id (EConstr.destVar sigma c)

let hyp_of_var sigma v = SsrHyp (Loc.tag @@ EConstr.destVar sigma v)

let interp_clr sigma = function
| Some clr, (k, c)
  when (k = NoFlag  || k = WithAt) && is_pf_var sigma c ->
   hyp_of_var sigma c :: clr
| Some clr, _ -> clr
| None, _ -> []

(** Basic tacticals *)

(** Multipliers *)(* {{{ ***********************************************************)

(* tactical *)

let tclID tac = tac

let tclDOTRY n tac =
  let open Tacticals in
  if n <= 0 then tclIDTAC else
  let rec loop i =
    if i = n then tclTRY tac else
    tclTRY (tclTHEN tac (loop (i + 1))) in
  loop 1

let tclDO n tac =
  let prefix i = str"At iteration " ++ int i ++ str": " in
  let tac_err_at i =
    Proofview.Goal.enter begin fun gl ->
      Proofview.tclORELSE tac begin function
      | (CErrors.UserError s, info) ->
        let e' = CErrors.UserError (prefix i ++ s) in
        Proofview.tclZERO ~info e'
      | (e, info) -> Proofview.tclZERO ~info e
      end
    end
  in
  let rec loop i =
    Proofview.Goal.enter begin fun gl ->
    if i = n then tac_err_at i else
    Tacticals.tclTHEN (tac_err_at i) (loop (i + 1))
  end in
  loop 1

let tclAT_LEAST_ONCE t =
  let open Tacticals in
  tclTHEN t (tclREPEAT t)

let tclMULT = function
  | 0, May  -> Tacticals.tclREPEAT
  | 1, May  -> Tacticals.tclTRY
  | n, May  -> tclDOTRY n
  | 0, Must -> tclAT_LEAST_ONCE
  | n, Must when n > 1 -> tclDO n
  | _       -> tclID

let cleartac clr = Proofview.tclTHEN (pf_check_hyps_uniq [] clr) (Tactics.clear (hyps_ids clr))

(* }}} *)

let get_hyp env sigma id =
  try EConstr.of_named_decl (Environ.lookup_named id env)
  with Not_found -> raise (Logic.RefinerError (env, sigma, Logic.NoSuchHyp id))

(** Generalize tactic *)

(* XXX the k of the redex should percolate out *)
let pf_interp_gen_aux env sigma ~concl to_ind ((oclr, occ), t) =
  let pat = interp_cpattern env sigma t None in (* UGLY API *)
  let sigma = Evd.merge_universe_context sigma (Evd.evar_universe_context @@ fst pat) in
  let sigma, c, cl = fill_rel_occ_pattern env sigma concl pat occ in
  let clr = interp_clr sigma (oclr, (tag_of_cpattern t, c)) in
  if not(occur_existential sigma c) then
    if tag_of_cpattern t = WithAt then
      if not (EConstr.isVar sigma c) then
        errorstrm (str "@ can be used with variables only")
      else match get_hyp env sigma (EConstr.destVar sigma c) with
      | NamedDecl.LocalAssum _ -> errorstrm (str "@ can be used with let-ins only")
      | NamedDecl.LocalDef (name, b, ty) -> true, pat, EConstr.mkLetIn (map_annot Name.mk_name name,b,ty,cl),c,clr, sigma
    else let sigma, ccl =  pf_mkprod env sigma c cl in false, pat, ccl, c, clr, sigma
  else if to_ind && occ = None then
    let p, evs, ucst' = abs_evars env sigma (fst pat, c) in
    let sigma = Evd.merge_universe_context sigma ucst' in
    if List.is_empty evs then anomaly "occur_existential but no evars" else
    let sigma, pty, rp = pfe_type_relevance_of env sigma p in
    false, pat, EConstr.mkProd (make_annot (constr_name sigma c) rp, pty, concl), p, clr, sigma
  else CErrors.user_err ?loc:(loc_of_cpattern t) (str "generalized term didn't match")

let genclrtac cl cs clr =
  let open Proofview.Notations in
  let open Tacticals in
  (* apply_type may give a type error, but the useful message is
   * the one of clear.  You type "move: x" and you get
   * "x is used in hyp H" instead of
   * "The term H has type T x but is expected to have type T x0". *)
  (Proofview.tclORELSE
    (Tactics.apply_type ~typecheck:true cl cs)
    (fun (type_err, info) ->
      pf_constr_of_global Coqlib.(lib_ref "core.False.type") >>= fun f ->
      (Tactics.elim_type f) <*>
      (cleartac clr) <*>
      (Proofview.tclZERO ~info type_err)))
  <*>
  (cleartac clr)

let gentac gen =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
(*   ppdebug(lazy(str"sigma@gentac=" ++ pr_evar_map None (project gl))); *)
  let conv, _, cl, c, clr, sigma = pf_interp_gen_aux env sigma ~concl false gen in
  debug_ssr (fun () -> str"c@gentac=" ++ pr_econstr_env env sigma c);
  Proofview.Unsafe.tclEVARS sigma <*>
  if conv
  then Tacticals.tclTHEN (convert_concl ~check:true cl) (cleartac clr)
  else genclrtac cl [c] clr
  end

let genstac (gens, clr) =
  Tacticals.tclTHENLIST (cleartac clr :: List.rev_map gentac gens)

let interp_gen env sigma ~concl to_ind gen =
  let _, _, a, b, c, sigma = pf_interp_gen_aux env sigma ~concl to_ind gen in
  sigma, (a, b ,c)

let is_protect hd env sigma =
  let protectC = mkSsrRef "protect_term" in
  EConstr.isRefX sigma protectC hd

let abs_wgen env sigma keep_let f gen (args,c) =
  let evar_closed t p =
    if occur_existential sigma t then
      CErrors.user_err ?loc:(loc_of_cpattern p)
        (pr_econstr_pat env sigma t ++
        str" contains holes and matches no subterm of the goal.") in
  match gen with
  | _, Some ((x, mode), None) when mode = "@" || (mode = " " && keep_let) ->
     let x = hoi_id x in
     let decl = get_hyp env sigma x in
     sigma,
     (if NamedDecl.is_local_def decl then args else EConstr.mkVar x :: args),
     EConstr.mkProd_or_LetIn (decl |> NamedDecl.to_rel_decl |> RelDecl.set_name (Name (f x)))
                     (EConstr.Vars.subst_var x c)
  | _, Some ((x, _), None) ->
     let x = hoi_id x in
     let hyp = get_hyp env sigma x in
     let x' = make_annot (Name (f x)) (NamedDecl.get_relevance hyp) in
     let prod = EConstr.mkProd (x', NamedDecl.get_type hyp, EConstr.Vars.subst_var x c) in
     sigma, EConstr.mkVar x :: args, prod
  | _, Some ((x, "@"), Some p) ->
     let x = hoi_id x in
     let cp = interp_cpattern env sigma p None in
     let sigma = Evd.merge_universe_context sigma (Evd.evar_universe_context (fst cp)) in
     let sigma, t, c = fill_rel_occ_pattern env sigma c cp None in
     evar_closed t p;
     let ut = red_product_skip_id env sigma t in
     let sigma, ty, r = pfe_type_relevance_of env sigma t in
     sigma, args, EConstr.mkLetIn(make_annot (Name (f x)) r, ut, ty, c)
  | _, Some ((x, _), Some p) ->
     let x = hoi_id x in
     let cp = interp_cpattern env sigma p None in
     let sigma = Evd.merge_universe_context sigma (Evd.evar_universe_context (fst cp)) in
     let sigma, t, c = fill_rel_occ_pattern env sigma c cp None in
     evar_closed t p;
     let sigma, ty, r = pfe_type_relevance_of env sigma t in
     sigma, t :: args, EConstr.mkProd(make_annot (Name (f x)) r, ty, c)
  | _ -> sigma, args, c

let clr_of_wgen gen clrs = match gen with
  | clr, Some ((x, _), None) ->
     let x = hoi_id x in
     cleartac clr :: cleartac [SsrHyp(Loc.tag x)] :: clrs
  | clr, _ -> cleartac clr :: clrs


let reduct_in_concl ~check t = Tactics.reduct_in_concl ~cast:false ~check (t, DEFAULTcast)
let unfold cl =
  Proofview.tclEVARMAP >>= fun sigma ->
  let module R = Reductionops in let module F = CClosure.RedFlags in
  let flags = F.mkflags [F.fBETA; F.fMATCH; F.fFIX; F.fCOFIX; F.fDELTA] in
  let fold accu c = F.red_add accu (F.fCONST (fst (EConstr.destConst sigma c))) in
  let flags = List.fold_left fold flags cl in
  reduct_in_concl ~check:false (R.clos_norm_flags flags)

open Proofview
open Notations

let pf_apply f = Proofview.Goal.enter_one ~__LOC__ begin fun gl ->
  f (Proofview.Goal.env gl) (Proofview.Goal.sigma gl)
end

let tclINTERP_AST_CLOSURE_TERM_AS_CONSTR c =
  tclINDEPENDENTL @@ pf_apply begin fun env sigma ->
  let old_ssrterm = mkRHole, Some c.Ssrast.body in
  let ist =
    option_assert_get c.Ssrast.interp_env
      Pp.(str "tclINTERP_AST_CLOSURE_TERM_AS_CONSTR: term with no ist") in
  let sigma, t = Tacinterp.interp_constr_gen Pretyping.WithoutTypeConstraint ist env sigma old_ssrterm in
  Unsafe.tclEVARS sigma <*>
  tclUNIT t
end

let tacREDUCE_TO_QUANTIFIED_IND ty =
  pf_apply begin fun env sigma ->
  try tclUNIT (Tacred.reduce_to_quantified_ind env sigma ty)
  with e -> tclZERO e
  end

let tacTYPEOF c = Goal.enter_one ~__LOC__ (fun g ->
  let sigma, env = Goal.sigma g, Goal.env g in
  let sigma, ty = Typing.type_of env sigma c in
  Unsafe.tclEVARS sigma <*> tclUNIT ty)

(** This tactic creates a partial proof realizing the introduction rule, but
    does not check anything. *)
let unsafe_intro env decl b =
  let open Context.Named.Declaration in
  Refine.refine ~typecheck:false begin fun sigma ->
    let ctx = Environ.named_context_val env in
    let nctx = EConstr.push_named_context_val decl ctx in
    let inst = EConstr.identity_subst_val (Environ.named_context_val env) in
    let ninst = EConstr.mkRel 1 :: inst in
    let nb = EConstr.Vars.subst1 (EConstr.mkVar (get_id decl)) b in
    let sigma, ev = Evarutil.new_pure_evar ~principal:true nctx sigma nb in
    sigma, EConstr.mkNamedLambda_or_LetIn decl (EConstr.mkEvar (ev, ninst))
  end

let set_decl_id id = let open Context in function
  | Rel.Declaration.LocalAssum(name,ty) -> Named.Declaration.LocalAssum({name with binder_name=id},ty)
  | Rel.Declaration.LocalDef(name,ty,t) -> Named.Declaration.LocalDef({name with binder_name=id},ty,t)

let rec decompose_assum env sigma orig_goal =
  let open Context in
  match EConstr.kind sigma orig_goal with
  | Prod(name,ty,t) ->
      Rel.Declaration.LocalAssum(name,ty), t, true
  | LetIn(name,ty,t1,t2) -> Rel.Declaration.LocalDef(name, ty, t1), t2, true
  | _ ->
      let goal = Reductionops.whd_allnolet env sigma orig_goal in
      match EConstr.kind sigma goal with
      | Prod(name,ty,t) -> Rel.Declaration.LocalAssum(name,ty), t, false
      | LetIn(name,ty,t1,t2) -> Rel.Declaration.LocalDef(name,ty,t1), t2, false
      | App(hd,args) when EConstr.isLetIn sigma hd -> (* hack *)
          let _,v,_,b = EConstr.destLetIn sigma hd in
          let ctx, t, _ =
            decompose_assum env sigma
              (EConstr.mkApp (EConstr.Vars.subst1 v b, args)) in
          ctx, t, false
      | _ -> CErrors.user_err
          Pp.(str "No assumption in " ++ Printer.pr_econstr_env env sigma goal)

let tclFULL_BETAIOTA = Goal.enter begin fun gl ->
  let r, _ = Redexpr.reduction_of_red_expr (Goal.env gl)
    Genredexpr.(Lazy {
      rBeta=true; rMatch=true; rFix=true; rCofix=true;
      rZeta=false; rDelta=false; rConst=[]}) in
  Tactics.e_reduct_in_concl ~cast:false ~check:false (r,Constr.DEFAULTcast)
end

type intro_id =
  | Anon
  | Id of Id.t
  | Seed of string

(** [intro id k] introduces the first premise (product or let-in) of the goal
    under the name [id], reducing the head of the goal (using beta, iota, delta
    but not zeta) if necessary. If [id] is None, a name is generated, that will
    not be user accessible. If the goal does not start with a product or a
let-in even after reduction, it fails. In case of success, the original name
and final id are passed to the continuation [k] which gets evaluated. *)
let tclINTRO ~id ~conclusion:k = Goal.enter begin fun gl ->
  let open Context in
  let env, sigma, g = Goal.(env gl, sigma gl, concl gl) in
  let decl, t, no_red = decompose_assum env sigma g in
  let original_name = Rel.Declaration.get_name decl in
  let already_used = Tacmach.pf_ids_of_hyps gl in
  let id = match id, original_name with
    | Id id, _ -> id
    | Seed id, _ -> mk_anon_id id already_used
    | Anon, Name id ->
       if is_discharged_id id then id
       else mk_anon_id (Id.to_string id) already_used
    | Anon, Anonymous ->
       let ids = Tacmach.pf_ids_of_hyps gl in
       mk_anon_id ssr_anon_hyp ids
  in
  if List.mem id already_used then
    errorstrm Pp.(Id.print id ++ str" already used");
  unsafe_intro env (set_decl_id id decl) t <*>
  (if no_red then tclUNIT () else tclFULL_BETAIOTA) <*>
  k ~orig_name:original_name ~new_name:id
end

let return ~orig_name:_ ~new_name:_ = tclUNIT ()

let tclINTRO_ID id = tclINTRO ~id:(Id id) ~conclusion:return
let tclINTRO_ANON ?seed () =
  match seed with
  | None -> tclINTRO ~id:Anon ~conclusion:return
  | Some seed -> tclINTRO ~id:(Seed seed) ~conclusion:return

let tclRENAME_HD_PROD name = Goal.enter begin fun gl ->
  let concl = Goal.concl gl in
  let sigma = Goal.sigma gl in
  match EConstr.kind sigma concl with
  | Prod(x,src,tgt) ->
      convert_concl_no_check EConstr.(mkProd ({x with binder_name = name},src,tgt))
  | _ -> CErrors.anomaly (Pp.str "rename_hd_prod: no head product")
end

let tcl0G ~default tac =
  numgoals >>= fun ng -> if ng = 0 then tclUNIT default else tac

let rec tclFIRSTa = function
  | [] -> Tacticals.tclZEROMSG Pp.(str"No applicable tactic.")
  | tac :: rest -> tclORELSE tac (fun _ -> tclFIRSTa rest)

let rec tclFIRSTi tac n =
  if n < 0 then Tacticals.tclZEROMSG Pp.(str "tclFIRSTi")
  else tclORELSE (tclFIRSTi tac (n-1)) (fun _ -> tac n)

let tacCONSTR_NAME ?name c =
  match name with
  | Some n -> tclUNIT n
  | None ->
      Goal.enter_one ~__LOC__ (fun g ->
        let sigma = Goal.sigma g in
        tclUNIT (constr_name sigma c))

let tacMKPROD c ?name cl =
  tacTYPEOF c >>= fun t ->
  tacCONSTR_NAME ?name c >>= fun name ->
  Goal.enter_one ~__LOC__ begin fun g ->
    let sigma, env = Goal.sigma g, Goal.env g in
    let r = Retyping.relevance_of_term env sigma c in
    if name <> Names.Name.Anonymous || EConstr.Vars.noccurn sigma  1 cl
    then tclUNIT (EConstr.mkProd (make_annot name r, t, cl))
    else
      let name = Names.Id.of_string (Namegen.hdchar env sigma t) in
      tclUNIT (EConstr.mkProd (make_annot (Name.Name name) r, t, cl))
end

let tacINTERP_CPATTERN cp =
  pf_apply begin fun env sigma ->
    tclUNIT (Ssrmatching.interp_cpattern env sigma cp None)
  end

let tacUNIFY a b =
  pf_apply begin fun env sigma ->
  let sigma = Ssrmatching.unify_HO env sigma a b in
  Unsafe.tclEVARS sigma
  end

let tclOPTION o d =
  match o with
  | None -> d >>= tclUNIT
  | Some x -> tclUNIT x

let tacIS_INJECTION_CASE ?ty t = begin
  tclOPTION ty (tacTYPEOF t) >>= fun ty ->
  tacREDUCE_TO_QUANTIFIED_IND ty >>= fun ((mind,_),_) ->
  tclUNIT (Coqlib.check_ind_ref "core.eq.type" mind)
end

let tclWITHTOP tac = Goal.enter begin fun gl ->
  let top =
    mk_anon_id "top_assumption" (Tacmach.pf_ids_of_hyps gl) in
  tclINTRO_ID top <*>
  tac (EConstr.mkVar top) <*>
  Tactics.clear [top]
end

let tacMK_SSR_CONST name =
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  match mkSsrConst env sigma name with
  | sigma, c -> Unsafe.tclEVARS sigma <*> tclUNIT c
  | exception e when CErrors.noncritical e ->
    tclLIFT (Proofview.NonLogical.raise (e, Exninfo.null))

let tacDEST_CONST c =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.destConst sigma c with
  | c, _ -> tclUNIT c
  | exception e when CErrors.noncritical e ->
    tclLIFT (Proofview.NonLogical.raise (e, Exninfo.null))

(* TASSI: This version of unprotects inlines the unfold tactic definition,
 * since we don't want to wipe out let-ins, and it seems there is no flag
 * to change that behaviour in the standard unfold code *)
let unprotecttac =
  tacMK_SSR_CONST "protect_term" >>= tacDEST_CONST >>= fun prot ->
  let open CClosure.RedFlags in
  let flags = red_add_transparent CClosure.allnolet TransparentState.empty in
  let flags = red_add flags (fCONST prot) in
  Tacticals.onClause (fun idopt ->
    let hyploc = Option.map (fun id -> id, InHyp) idopt in
    Tactics.reduct_option ~check:false
      (Reductionops.clos_norm_flags flags, DEFAULTcast) hyploc)
    allHypsAndConcl


module type StateType = sig
  type state
  val init : state
end

module MakeState(S : StateType) = struct

let state_field : S.state Proofview_monad.StateStore.field =
  Proofview_monad.StateStore.field ()

(* FIXME: should not inject fresh_state, but initialize it at the beginning *)
let lift_upd_state upd s =
  let open Proofview_monad.StateStore in
  let old_state = Option.default S.init (get s state_field) in
  upd old_state >>= fun new_state ->
  tclUNIT (set s state_field new_state)

let tacUPDATE upd = Goal.enter begin fun gl ->
  let s0 = Goal.state gl in
  Goal.enter_one ~__LOC__ (fun _ -> lift_upd_state upd s0) >>= fun s ->
  Unsafe.tclGETGOALS >>= fun gls ->
  let gls = List.map (fun gs ->
    let g = Proofview_monad.drop_state gs in
    Proofview_monad.goal_with_state g s) gls in
  Unsafe.tclSETGOALS gls
end

let tclGET k = Goal.enter begin fun gl ->
  let open Proofview_monad.StateStore in
  k (Option.default S.init (get (Goal.state gl) state_field))
end

let tclGET1 k = Goal.enter_one begin fun gl ->
  let open Proofview_monad.StateStore in
  k (Option.default S.init (get (Goal.state gl) state_field))
end


let tclSET new_s =
  let open Proofview_monad.StateStore in
  Unsafe.tclGETGOALS >>= fun gls ->
  let gls = List.map (fun gs ->
    let g = Proofview_monad.drop_state gs in
    let s = Proofview_monad.get_state gs in
    Proofview_monad.goal_with_state g (set s state_field new_s)) gls in
  Unsafe.tclSETGOALS gls

let get g =
  Option.default S.init
    (Proofview_monad.StateStore.get (Goal.state g) state_field)

end

let is_construct_ref sigma c r =
  EConstr.isConstruct sigma c && GlobRef.equal (GlobRef.ConstructRef (fst(EConstr.destConstruct sigma c))) r
let is_ind_ref sigma c r = EConstr.isInd sigma c && GlobRef.equal (GlobRef.IndRef (fst(EConstr.destInd sigma c))) r
let is_const_ref sigma c r =
  EConstr.isConst sigma c && GlobRef.equal (GlobRef.ConstRef (fst(EConstr.destConst sigma c))) r

(* vim: set filetype=ocaml foldmethod=marker: *)
