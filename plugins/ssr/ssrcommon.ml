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

open Util
open Names
open Evd
open Term
open Constr
open Termops
open Printer
open Locusops

open Ltac_plugin
open Tacmach
open Refiner
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

let errorstrm x = CErrors.user_err ~hdr:"ssreflect" x

let allocc = Some(false,[])

(** Bound assumption argument *)

(* The Ltac API does have a type for assumptions but it is level-dependent *)
(* and therefore impractical to use for complex arguments, so we substitute *)
(* our own to have a uniform representation. Also, we refuse to intern     *)
(* idents that match global/section constants, since this would lead to    *)
(* fragile Ltac scripts.                                                   *)

let hyp_id (SsrHyp (_, id)) = id

let hyp_err ?loc msg id =
  CErrors.user_err ?loc ~hdr:"ssrhyp" Pp.(str msg ++ Id.print id)

let not_section_id id = not (Termops.is_section_variable id)

let hyps_ids = List.map hyp_id

let rec check_hyps_uniq ids = function
  | SsrHyp (loc, id) :: _ when List.mem id ids ->
    hyp_err ?loc "Duplicate assumption " id
  | SsrHyp (_, id) :: hyps -> check_hyps_uniq (id :: ids) hyps
  | [] -> ()

let check_hyp_exists hyps (SsrHyp(_, id)) =
  try ignore(Context.Named.lookup id hyps)
  with Not_found -> errorstrm Pp.(str"No assumption is named " ++ Id.print id)

let test_hypname_exists hyps id =
  try ignore(Context.Named.lookup id hyps); true
  with Not_found -> false

let hoik f = function Hyp x -> f x | Id x -> f x
let hoi_id = hoik hyp_id

let mk_hint tac = false, [Some tac]
let mk_orhint tacs = true, tacs
let nullhint = true, []
let nohint = false, []

type 'a tac_a = (goal * 'a) sigma -> (goal * 'a) list sigma

let push_ctx  a gl = re_sig (sig_it gl, a) (project gl)
let push_ctxs a gl =
  re_sig (List.map (fun x -> x,a) (sig_it gl)) (project gl)
let pull_ctx gl = let g, a = sig_it gl in re_sig g (project gl), a
let pull_ctxs gl = let g, a = List.split (sig_it gl) in re_sig g (project gl), a

let with_ctx f gl =
  let gl, ctx = pull_ctx gl in
  let rc, ctx = f ctx in
  rc, push_ctx ctx gl
let without_ctx f gl =
  let gl, _ctx = pull_ctx gl in
  f gl
let tac_ctx t gl =
  let gl, a = pull_ctx gl in
  let gl = t gl in
  push_ctxs a gl

let tclTHEN_ia t1 t2 gl =
  let gal = t1 gl in
  let goals, sigma = sig_it gal, project gal in
  let _, opened, sigma =
    List.fold_left (fun (i,opened,sigma) g ->
      let gl = t2 i (re_sig g sigma) in
      i+1, sig_it gl :: opened, project gl)
      (1,[],sigma) goals in
  re_sig (List.flatten (List.rev opened)) sigma

let tclTHEN_a t1 t2 gl = tclTHEN_ia t1 (fun _ -> t2) gl

let tclTHENS_a t1 tl gl = tclTHEN_ia t1
  (fun i -> List.nth tl (i-1)) gl

let rec tclTHENLIST_a = function
  | [] -> tac_ctx tclIDTAC
  | t1::tacl -> tclTHEN_a t1 (tclTHENLIST_a tacl)

(* like  tclTHEN_i but passes to the tac "i of n" and not just i *)
let tclTHEN_i_max tac taci gl =
  let maxi = ref 0 in
  tclTHEN_ia (tclTHEN_ia tac (fun i -> maxi := max i !maxi; tac_ctx tclIDTAC))
    (fun i gl -> taci i !maxi gl) gl

let tac_on_all gl tac =
  let goals = sig_it gl in
  let opened, sigma =
    List.fold_left (fun (opened,sigma) g ->
      let gl = tac (re_sig g sigma) in
      sig_it gl :: opened, project gl)
      ([],project gl) goals in
  re_sig (List.flatten (List.rev opened)) sigma

(* Used to thread data between intro patterns at run time *)
type tac_ctx = {
  tmp_ids : (Id.t * Name.t ref) list;
  wild_ids : Id.t list;
  delayed_clears : Id.t list;
}

let new_ctx () =
  { tmp_ids = []; wild_ids = []; delayed_clears = [] }

let with_fresh_ctx t gl =
  let gl = push_ctx (new_ctx()) gl in
  let gl = t gl in
  fst (pull_ctxs gl)

open Genarg
open Stdarg
open Pp

let errorstrm x = CErrors.user_err ~hdr:"ssreflect" x
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
open Globnames
open Decl_kinds

let mkRHole = DAst.make @@ GHole (Evar_kinds.InternalHole, Namegen.IntroAnonymous, None)

let rec mkRHoles n = if n > 0 then mkRHole :: mkRHoles (n - 1) else []
let rec isRHoles cl = match cl with
| [] -> true
| c :: l -> match DAst.get c with GHole _ -> isRHoles l | _ -> false
let mkRApp f args = if args = [] then f else DAst.make @@ GApp (f, args)
let mkRVar id = DAst.make @@ GRef (VarRef id,None)
let mkRltacVar id = DAst.make @@ GVar (id)
let mkRCast rc rt =  DAst.make @@ GCast (rc, CastConv rt)
let mkRType =  DAst.make @@ GSort (GType [])
let mkRProp =  DAst.make @@ GSort (GProp)
let mkRArrow rt1 rt2 = DAst.make @@ GProd (Anonymous, Explicit, rt1, rt2)
let mkRConstruct c = DAst.make @@ GRef (ConstructRef c,None)
let mkRInd mind = DAst.make @@ GRef (IndRef mind,None)
let mkRLambda n s t = DAst.make @@ GLambda (n, Explicit, s, t)

let rec mkRnat n =
  if n <= 0 then DAst.make @@ GRef (Coqlib.glob_O, None) else
  mkRApp (DAst.make @@ GRef (Coqlib.glob_S, None)) [mkRnat (n - 1)]

let glob_constr ist genv = function
  | _, Some ce ->
    let vars = Id.Map.fold (fun x _ accu -> Id.Set.add x accu) ist.Tacinterp.lfun Id.Set.empty in
    let ltacvars = {
      Constrintern.empty_ltac_sign with Constrintern.ltac_vars = vars } in
    Constrintern.intern_gen Pretyping.WithoutTypeConstraint ~ltacvars genv Evd.(from_env genv) ce
  | rc, None -> rc

let pf_intern_term ist gl (_, c) = glob_constr ist (pf_env gl) c
let intern_term ist env (_, c) = glob_constr ist env c

(* Estimate a bound on the number of arguments of a raw constr. *)
(* This is not perfect, because the unifier may fail to         *)
(* typecheck the partial application, so we use a minimum of 5. *)
(* Also, we don't handle delayed or iterated coercions to       *)
(* FUNCLASS, which is probably just as well since these can     *)
(* lead to infinite arities.                                    *)

let splay_open_constr gl (sigma, c) =
  let env = pf_env gl in let t = Retyping.get_type_of env sigma c in
  Reductionops.splay_prod env sigma t

let isAppInd env sigma c =
  let c = Reductionops.clos_whd_flags CClosure.all env sigma c in
  let c, _ = decompose_app_vect sigma c in
  EConstr.isInd sigma c

(** Generic argument-based globbing/typing utilities *)

let interp_refine ist gl rc =
  let constrvars = Tacinterp.extract_ltac_constr_values ist (pf_env gl) in
  let vars = { Glob_ops.empty_lvar with
    Ltac_pretype.ltac_constrs = constrvars; ltac_genargs = ist.Tacinterp.lfun
  } in
  let kind = Pretyping.OfType (pf_concl gl) in
  let flags = {
    Pretyping.use_typeclasses = true;
    solve_unification_constraints = true;
    use_hook = None;
    fail_evar = false;
    expand_evars = true }
  in
  let sigma, c = Pretyping.understand_ltac flags (pf_env gl) (project gl) vars kind rc in
(*   ppdebug(lazy(str"sigma@interp_refine=" ++ pr_evar_map None sigma)); *)
  ppdebug(lazy(str"c@interp_refine=" ++ Printer.pr_econstr_env (pf_env gl) sigma c));
  (sigma, (sigma, c))


let interp_open_constr ist gl gc =
  let (sigma, (c, _)) = Tacinterp.interp_open_constr_with_bindings ist (pf_env gl) (project gl) (gc, Tactypes.NoBindings) in
  (project gl, (sigma, c))

let interp_term ist gl (_, c) = snd (interp_open_constr ist gl c)

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
  let arg = Tacinterp.interp_genarg ist globarg in
  let (sigma, arg) = of_ftactic arg gl in
  sigma, Tacinterp.Value.cast (topwit wit) arg

let interp_hyp ist gl (SsrHyp (loc, id)) =
  let s, id' = interp_wit wit_var ist gl CAst.(make ?loc id) in
  if not_section_id id' then s, SsrHyp (loc, id') else
  hyp_err ?loc "Can't clear section hypothesis " id'

let interp_hyps ist gl ghyps =
  let hyps = List.map snd (List.map (interp_hyp ist gl) ghyps) in
  check_hyps_uniq [] hyps; Tacmach.project gl, hyps

(* Old terms *)
let mk_term k c = k, (mkRHole, Some c)
let mk_lterm c = mk_term xNoFlag c

(* New terms *)

let mk_ast_closure_term a t = {
  annotation = a;
  body = t;
  interp_env = None;
  glob_env = None;
}

let glob_ast_closure_term (ist : Genintern.glob_sign) t =
  { t with glob_env = Some ist }
let subst_ast_closure_term (_s : Mod_subst.substitution) t =
  (* _s makes sense only for glob constr *)
  t
let interp_ast_closure_term (ist : Geninterp.interp_sign) (gl : 'goal Evd.sigma) t =
  (* gl is only useful if we want to interp *now*, later we have
   * a potentially different gl.sigma *)
  Tacmach.project gl, { t with interp_env = Some ist }

let ssrterm_of_ast_closure_term { body; annotation } =
  let c = match annotation with
    | `Parens -> xInParens
    | `At -> xWithAt
    | _ -> xNoFlag in
  mk_term c body

let ssrdgens_of_parsed_dgens = function
  | [], clr -> { dgens = []; gens = []; clr }
  | [gens], clr -> { dgens = []; gens; clr }
  | [dgens;gens], clr -> { dgens; gens; clr }
  | _ -> assert false


let nbargs_open_constr gl oc =
  let pl, _ = splay_open_constr gl oc in List.length pl

let pf_nbargs gl c = nbargs_open_constr gl (project gl, c)

let internal_names = ref []
let add_internal_name pt = internal_names := pt :: !internal_names
let is_internal_name s = List.exists (fun p -> p s) !internal_names

let tmp_tag = "_the_"
let tmp_post = "_tmp_"
let mk_tmp_id i =
  Id.of_string (Printf.sprintf "%s%s%s" tmp_tag (CString.ordinal i) tmp_post)
let new_tmp_id ctx =
  let id = mk_tmp_id (1 + List.length ctx.tmp_ids) in
  let orig = ref Anonymous in
  (id, orig), { ctx with tmp_ids = (id, orig) :: ctx.tmp_ids }
;;

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
let mk_wildcard_id i =
  Id.of_string (Printf.sprintf "%s%s%s" wildcard_tag (CString.ordinal i) wildcard_post)
let has_wildcard_tag s = 
  let n = String.length s in let m = String.length wildcard_tag in
  let m' = String.length wildcard_post in
  n < m + m' + 2 && same_prefix s wildcard_tag m &&
  String.sub s (n - m') m' = wildcard_post &&
  skip_digits s m = n - m' - 2
let _ = add_internal_name has_wildcard_tag

let new_wild_id ctx =
  let i = 1 + List.length ctx.wild_ids in
  let id = mk_wildcard_id i in
  id, { ctx with wild_ids = id :: ctx.wild_ids }

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

let mk_anon_id t gl_ids =
  let m, si0, id0 =
    let s = ref (Printf.sprintf  "_%s_" t) in
    if is_internal_name !s then s := "_" ^ !s;
    let n = String.length !s - 1 in
    let rec loop i j =
      let d = !s.[i] in if not (is_digit d) then i + 1, j else
      loop (i - 1) (if d = '0' then j else i) in
    let m, j = loop (n - 1) n in m, (!s, j), Id.of_string !s in
  if not (List.mem id0 gl_ids) then id0 else
  let s, i = List.fold_left (max_suffix m) si0 gl_ids in
  let open Bytes in
  let s = of_string s in
  let n = length s - 1 in
  let rec loop i =
    if get s i = '9' then (set s i '0'; loop (i - 1)) else
    if i < m then (set s n '0'; set s m '1'; cat s (of_string "_")) else
    (set s i (Char.chr (Char.code (get s i) + 1)); s) in
  Id.of_bytes (loop (n - 1))

let convert_concl_no_check t = Tactics.convert_concl_no_check t DEFAULTcast
let convert_concl t = Tactics.convert_concl t DEFAULTcast

let rename_hd_prod orig_name_ref gl =
  match EConstr.kind (project gl) (pf_concl gl) with
  | Prod(_,src,tgt) ->
      Proofview.V82.of_tactic (convert_concl_no_check (EConstr.mkProd (!orig_name_ref,src,tgt))) gl
  | _ -> CErrors.anomaly (str "gentac creates no product")

(* Reduction that preserves the Prod/Let spine of the "in" tactical. *)

let inc_safe n = if n = 0 then n else n + 1
let rec safe_depth s c = match EConstr.kind s c with
| LetIn (Name x, _, _, c') when is_discharged_id x -> safe_depth s c' + 1
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

let pf_concl gl = EConstr.Unsafe.to_constr (pf_concl gl)
let pf_get_hyp gl x = EConstr.Unsafe.to_named_decl (pf_get_hyp gl x)

let pf_e_type_of gl t =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma, ty = Typing.type_of env sigma t in
  re_sig it sigma, ty

let nf_evar sigma t = 
  EConstr.Unsafe.to_constr (Evarutil.nf_evar sigma (EConstr.of_constr t))

let pf_abs_evars2 gl rigid (sigma, c0) =
  let c0 = EConstr.to_constr ~abort_on_undefined_evars:false sigma c0 in
  let sigma0, ucst = project gl, Evd.evar_universe_context sigma in
  let nenv = env_size (pf_env gl) in
  let abs_evar n k =
    let evi = Evd.find sigma k in
    let concl = EConstr.Unsafe.to_constr evi.evar_concl in
    let dc = EConstr.Unsafe.to_named_context (CList.firstn n (evar_filtered_context evi)) in
    let abs_dc c = function
    | NamedDecl.LocalDef (x,b,t) -> mkNamedLetIn x b t (mkArrow t c)
    | NamedDecl.LocalAssum (x,t) -> mkNamedProd x t c in
    let t = Context.Named.fold_inside abs_dc ~init:concl dc in
    nf_evar sigma t in
  let rec put evlist c = match Constr.kind c with
  | Evar (k, a) ->  
    if List.mem_assoc k evlist || Evd.mem sigma0 k || List.mem k rigid then evlist else
    let n = max 0 (Array.length a - nenv) in
    let t = abs_evar n k in (k, (n, t)) :: put evlist t
  | _ -> Constr.fold put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, EConstr.of_constr c0,[], ucst else
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n, _)) :: evl -> if k = k' then i, n else lookup k (i + 1) evl in
  let rec get i c = match Constr.kind c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then Constr.map (get i) c else if n = 0 then mkRel j else
    mkApp (mkRel j, Array.init n (fun k -> get i a.(n - 1 - k)))
  | _ -> Constr.map_with_binders ((+) 1) get i c in
  let rec loop c i = function
  | (_, (n, t)) :: evl ->
    loop (mkLambda (mk_evar_name n, get (i - 1) t, c)) (i - 1) evl
  | [] -> c in
  List.length evlist, EConstr.of_constr (loop (get 1 c0) 1 evlist), List.map fst evlist, ucst

let pf_abs_evars gl t = pf_abs_evars2 gl [] t


(* As before but if (?i : T(?j)) and (?j : P : Prop), then the lambda for i
 * looks like (fun evar_i : (forall pi : P. T(pi))) thanks to "loopP" and all 
 * occurrences of evar_i are replaced by (evar_i evar_j) thanks to "app".
 *
 * If P can be solved by ssrautoprop (that defaults to trivial), then
 * the corresponding lambda looks like (fun evar_i : T(c)) where c is 
 * the solution found by ssrautoprop.
 *)
let ssrautoprop_tac = ref (fun gl -> assert false)

(* Thanks to Arnaud Spiwack for this snippet *)
let call_on_evar tac e s =
  let { it = gs ; sigma = s } =
    tac { it = e ; sigma = s; } in
  gs, s

open Pp
let pp _ = () (* FIXME *)
module Intset = Evar.Set

let pf_abs_evars_pirrel gl (sigma, c0) =
  pp(lazy(str"==PF_ABS_EVARS_PIRREL=="));
  pp(lazy(str"c0= " ++ Printer.pr_constr_env (pf_env gl) sigma c0));
  let sigma0 = project gl in
  let c0 = nf_evar sigma0 (nf_evar sigma c0) in
  let nenv = env_size (pf_env gl) in
  let abs_evar n k =
    let evi = Evd.find sigma k in
    let concl = EConstr.Unsafe.to_constr evi.evar_concl in
    let dc = EConstr.Unsafe.to_named_context (CList.firstn n (evar_filtered_context evi)) in
    let abs_dc c = function
    | NamedDecl.LocalDef (x,b,t) -> mkNamedLetIn x b t (mkArrow t c)
    | NamedDecl.LocalAssum (x,t) -> mkNamedProd x t c in
    let t = Context.Named.fold_inside abs_dc ~init:concl dc in
    nf_evar sigma0 (nf_evar sigma t) in
  let rec put evlist c = match Constr.kind c with
  | Evar (k, a) ->  
    if List.mem_assoc k evlist || Evd.mem sigma0 k then evlist else
    let n = max 0 (Array.length a - nenv) in
    let k_ty = 
      Retyping.get_sort_family_of 
        (pf_env gl) sigma (Evd.evar_concl (Evd.find sigma k)) in
    let is_prop = k_ty = InProp in
    let t = abs_evar n k in (k, (n, t, is_prop)) :: put evlist t
  | _ -> Constr.fold put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0 else
  let pr_constr t = Printer.pr_econstr_env (pf_env gl) sigma (Reductionops.nf_beta (pf_env gl) (project gl) (EConstr.of_constr t)) in
  pp(lazy(str"evlist=" ++ pr_list (fun () -> str";")
    (fun (k,_) -> Evar.print k) evlist));
  let evplist = 
    let depev = List.fold_left (fun evs (_,(_,t,_)) -> 
        let t = EConstr.of_constr t in
        Intset.union evs (Evarutil.undefined_evars_of_term sigma t)) Intset.empty evlist in
    List.filter (fun (i,(_,_,b)) -> b && Intset.mem i depev) evlist in
  let evlist, evplist, sigma = 
    if evplist = [] then evlist, [], sigma else
    List.fold_left (fun (ev, evp, sigma) (i, (_,t,_) as p) ->
      try 
        let ng, sigma = call_on_evar !ssrautoprop_tac i sigma in
        if (ng <> []) then errorstrm (str "Should we tell the user?");
        List.filter (fun (j,_) -> j <> i) ev, evp, sigma
      with _ -> ev, p::evp, sigma) (evlist, [], sigma) (List.rev evplist) in
  let c0 = nf_evar sigma c0 in
  let evlist = 
    List.map (fun (x,(y,t,z)) -> x,(y,nf_evar sigma t,z)) evlist in
  let evplist = 
    List.map (fun (x,(y,t,z)) -> x,(y,nf_evar sigma t,z)) evplist in
  pp(lazy(str"c0= " ++ pr_constr c0));
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n,_,_)) :: evl -> if k = k' then i,n else lookup k (i + 1) evl in
  let rec get evlist i c = match Constr.kind c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then Constr.map (get evlist i) c else if n = 0 then mkRel j else
    mkApp (mkRel j, Array.init n (fun k -> get evlist i a.(n - 1 - k)))
  | _ -> Constr.map_with_binders ((+) 1) (get evlist) i c in
  let rec app extra_args i c = match decompose_app c with
  | hd, args when isRel hd && destRel hd = i ->
      let j = destRel hd in
      mkApp (mkRel j, Array.of_list (List.map (Vars.lift (i-1)) extra_args @ args))
  | _ -> Constr.map_with_binders ((+) 1) (app extra_args) i c in
  let rec loopP evlist c i = function
  | (_, (n, t, _)) :: evl ->
    let t = get evlist (i - 1) t in
    let n = Name (Id.of_string (ssr_anon_hyp ^ string_of_int n)) in 
    loopP evlist (mkProd (n, t, c)) (i - 1) evl
  | [] -> c in
  let rec loop c i = function
  | (_, (n, t, _)) :: evl ->
    let evs = Evarutil.undefined_evars_of_term sigma (EConstr.of_constr t) in
    let t_evplist = List.filter (fun (k,_) -> Intset.mem k evs) evplist in
    let t = loopP t_evplist (get t_evplist 1 t) 1 t_evplist in
    let t = get evlist (i - 1) t in
    let extra_args = 
      List.map (fun (k,_) -> mkRel (fst (lookup k i evlist))) 
        (List.rev t_evplist) in
    let c = if extra_args = [] then c else app extra_args 1 c in
    loop (mkLambda (mk_evar_name n, t, c)) (i - 1) evl
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

let pf_type_id gl t = Id.of_string (Namegen.hdchar (pf_env gl) (project gl) t)
let pfe_type_of gl t =
  let sigma, ty = pf_type_of gl t in
  re_sig (sig_it gl) sigma, ty
let pf_type_of gl t =
  let sigma, ty = pf_type_of gl (EConstr.of_constr t) in
  re_sig (sig_it gl)  sigma, EConstr.Unsafe.to_constr ty

let pf_abs_cterm gl n c0 =
  if n <= 0 then c0 else
  let c0 = EConstr.Unsafe.to_constr c0 in
  let noargs = [|0|] in
  let eva = Array.make n noargs in
  let rec strip i c = match Constr.kind c with
  | App (f, a) when isRel f ->
    let j = i - destRel f in
    if j >= n || eva.(j) = noargs then mkApp (f, Array.map (strip i) a) else
    let dp = eva.(j) in
    let nd = Array.length dp - 1 in
    let mkarg k = strip i a.(if k < nd then dp.(k + 1) - j else k + dp.(0)) in
    mkApp (f, Array.init (Array.length a - dp.(0)) mkarg)
  | _ -> Constr.map_with_binders ((+) 1) strip i c in
  let rec strip_ndeps j i c = match Constr.kind c with
  | Prod (x, t, c1) when i < j ->
    let dl, c2 = strip_ndeps j (i + 1) c1 in
    if Vars.noccurn 1 c2 then dl, Vars.lift (-1) c2 else
    i :: dl, mkProd (x, strip i t, c2)
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c1' = destProd c1 in
    let dl, c2 = strip_ndeps j (i + 1) c1' in
    if Vars.noccurn 1 c2 then dl, Vars.lift (-1) c2 else
    i :: dl, mkLetIn (x, strip i b, strip i t, c2)
  | _ -> [], strip i c in
  let rec strip_evars i c = match Constr.kind c with
    | Lambda (x, t1, c1) when i < n ->
      let na = nb_evar_deps x in
      let dl, t2 = strip_ndeps (i + na) i t1 in
      let na' = List.length dl in
      eva.(i) <- Array.of_list (na - na' :: dl);
      let x' =
        if na' = 0 then Name (pf_type_id gl (EConstr.of_constr t2)) else mk_evar_name na' in
      mkLambda (x', t2, strip_evars (i + 1) c1)
(*      if noccurn 1 c2 then lift (-1) c2 else
      mkLambda (Name (pf_type_id gl t2), t2, c2) *)
    | _ -> strip i c in
  EConstr.of_constr (strip_evars 0 c0)

(* }}} *)

let pf_merge_uc uc gl =
  re_sig (sig_it gl) (Evd.merge_universe_context (Refiner.project gl) uc)
let pf_merge_uc_of sigma gl =
  let ucst = Evd.evar_universe_context sigma in
  pf_merge_uc ucst gl


let rec constr_name sigma c = match EConstr.kind sigma c with
  | Var id -> Name id
  | Cast (c', _, _) -> constr_name sigma c'
  | Const (cn,_) -> Name (Label.to_id (Constant.label cn))
  | App (c', _) -> constr_name sigma c'
  | _ -> Anonymous

let pf_mkprod gl c ?(name=constr_name (project gl) c) cl =
  let gl, t = pfe_type_of gl c in
  if name <> Anonymous || EConstr.Vars.noccurn (project gl) 1 cl then gl, EConstr.mkProd (name, t, cl) else
  gl, EConstr.mkProd (Name (pf_type_id gl t), t, cl)

let pf_abs_prod name gl c cl = pf_mkprod gl c ~name (Termops.subst_term (project gl) c cl)

(** look up a name in the ssreflect internals module *)
let ssrdirpath = DirPath.make [Id.of_string "ssreflect"]
let ssrqid name = Libnames.make_qualid ssrdirpath (Id.of_string name) 
let ssrtopqid name = Libnames.qualid_of_ident (Id.of_string name) 
let locate_reference qid =
  Smartlocate.global_of_extended_global (Nametab.locate_extended qid)
let mkSsrRef name =
  try locate_reference (ssrqid name) with Not_found ->
  try locate_reference (ssrtopqid name) with Not_found ->
  CErrors.user_err (Pp.str "Small scale reflection library not loaded")
let mkSsrRRef name = (DAst.make @@ GRef (mkSsrRef name,None)), None
let mkSsrConst name env sigma =
  EConstr.fresh_global env sigma (mkSsrRef name)
let pf_mkSsrConst name gl =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let (sigma, t) = mkSsrConst name env sigma in
  t, re_sig it sigma
let pf_fresh_global name gl =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma,t  = Evd.fresh_global env sigma name in
  EConstr.Unsafe.to_constr t, re_sig it sigma

let mkProt t c gl =
  let prot, gl = pf_mkSsrConst "protect_term" gl in
  EConstr.mkApp (prot, [|t; c|]), gl

let mkEtaApp c n imin =
  let open EConstr in
  if n = 0 then c else
  let nargs, mkarg =
    if n < 0 then -n, (fun i -> mkRel (imin + i)) else
    let imax = imin + n - 1 in n, (fun i -> mkRel (imax - i)) in
  mkApp (c, Array.init nargs mkarg)

let mkRefl t c gl =
  let sigma = project gl in
  let (sigma, refl) = EConstr.fresh_global (pf_env gl) sigma Coqlib.((build_coq_eq_data()).refl) in
  EConstr.mkApp (refl, [|t; c|]), { gl with sigma }

let discharge_hyp (id', (id, mode)) gl =
  let cl' = Vars.subst_var id (pf_concl gl) in
  match pf_get_hyp gl id, mode with
  | NamedDecl.LocalAssum (_, t), _ | NamedDecl.LocalDef (_, _, t), "(" ->
     Proofview.V82.of_tactic (Tactics.apply_type ~typecheck:true (EConstr.of_constr (mkProd (Name id', t, cl')))
       [EConstr.of_constr (mkVar id)]) gl
  | NamedDecl.LocalDef (_, v, t), _ ->
     Proofview.V82.of_tactic
       (convert_concl (EConstr.of_constr (mkLetIn (Name id', v, t, cl')))) gl

(* wildcard names *)
let clear_wilds wilds gl =
  Proofview.V82.of_tactic (Tactics.clear (List.filter (fun id -> List.mem id wilds) (pf_ids_of_hyps gl))) gl

let clear_with_wilds wilds clr0 gl =
  let extend_clr clr nd =
    let id = NamedDecl.get_id nd in
    if List.mem id clr || not (List.mem id wilds) then clr else
    let vars = Termops.global_vars_set_of_decl (pf_env gl) (project gl) nd in
    let occurs id' = Id.Set.mem id' vars in
    if List.exists occurs clr then id :: clr else clr in
  Proofview.V82.of_tactic (Tactics.clear (Context.Named.fold_inside extend_clr ~init:clr0 (Tacmach.pf_hyps gl))) gl

let clear_wilds_and_tmp_and_delayed_ids gl =
  let _, ctx = pull_ctx gl in
  tac_ctx
   (tclTHEN
    (clear_with_wilds ctx.wild_ids ctx.delayed_clears)
    (clear_wilds (List.map fst ctx.tmp_ids @ ctx.wild_ids))) gl

let rec is_name_in_ipats name = function
  | IPatClear clr :: tl -> 
      List.exists (function SsrHyp(_,id) -> id = name) clr 
      || is_name_in_ipats name tl
  | IPatId id :: tl -> id = name || is_name_in_ipats name tl
  | IPatAbstractVars ids :: tl ->
      CList.mem_f Id.equal name ids || is_name_in_ipats name tl
  | (IPatCase l | IPatDispatch (_,l) | IPatInj l) :: tl ->
      List.exists (is_name_in_ipats name) l || is_name_in_ipats name tl
  | (IPatView _ | IPatAnon _ | IPatSimpl _ | IPatRewrite _ | IPatTac _ | IPatNoop) :: tl -> is_name_in_ipats name tl
  | [] -> false

let view_error s gv =
  errorstrm (str ("Cannot " ^ s ^ " view ") ++ pr_term gv)


open Locus
(****************************** tactics ***********************************)

let rewritetac dir c =
  (* Due to the new optional arg ?tac, application shouldn't be too partial *)
  Proofview.V82.of_tactic begin
    Equality.general_rewrite (dir = L2R) AllOccurrences true false c
  end

(**********************`:********* hooks ************************************)

type name_hint = (int * EConstr.types array) option ref

let pf_abs_ssrterm ?(resolve_typeclasses=false) ist gl t =
  let sigma, ct as t = interp_term ist gl t in
  let sigma, _ as t =
    let env = pf_env gl in
    if not resolve_typeclasses then t
    else
       let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
       sigma, Evarutil.nf_evar sigma ct in
  let n, c, abstracted_away, ucst = pf_abs_evars gl t in
  List.fold_left Evd.remove sigma abstracted_away, pf_abs_cterm gl n c, ucst, n

let top_id = mk_internal_id "top assumption"

let ssr_n_tac seed n gl =
  let name = if n = -1 then seed else ("ssr" ^ seed ^ string_of_int n) in
  let fail msg = CErrors.user_err (Pp.str msg) in
  let tacname = 
    try Tacenv.locate_tactic (Libnames.qualid_of_ident (Id.of_string name))
    with Not_found -> try Tacenv.locate_tactic (ssrqid name)
    with Not_found ->
      if n = -1 then fail "The ssreflect library was not loaded"
      else fail ("The tactic "^name^" was not found") in
  let tacexpr = Loc.tag @@ Tacexpr.Reference (ArgArg (Loc.tag @@ tacname)) in
  Proofview.V82.of_tactic (Tacinterp.eval_tactic (Tacexpr.TacArg tacexpr)) gl

let donetac n gl = ssr_n_tac "done" n gl

open Constrexpr
open Util

(** Constructors for constr_expr *)
let mkCProp loc = CAst.make ?loc @@ CSort GProp
let mkCType loc = CAst.make ?loc @@ CSort (GType [])
let mkCVar ?loc id = CAst.make ?loc @@ CRef (qualid_of_ident ?loc id, None)
let rec mkCHoles ?loc n =
  if n <= 0 then [] else (CAst.make ?loc @@ CHole (None, Namegen.IntroAnonymous, None)) :: mkCHoles ?loc (n - 1)
let mkCHole loc = CAst.make ?loc @@ CHole (None, Namegen.IntroAnonymous, None)
let mkCLambda ?loc name ty t =  CAst.make ?loc @@
   CLambdaN ([CLocalAssum([CAst.make ?loc name], Default Explicit, ty)], t)
let mkCArrow ?loc ty t = CAst.make ?loc @@
   CProdN ([CLocalAssum([CAst.make Anonymous], Default Explicit, ty)], t)
let mkCCast ?loc t ty = CAst.make ?loc @@ CCast (t, CastConv ty)

let rec isCHoles = function { CAst.v = CHole _ } :: cl -> isCHoles cl | cl -> cl = []
let rec isCxHoles = function ({ CAst.v = CHole _ }, None) :: ch -> isCxHoles ch | _ -> false

let pf_interp_ty ?(resolve_typeclasses=false) ist gl ty =
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
     mk_term ' ' (force_type ty) in
   let strip_cast (sigma, t) =
     let rec aux t = match EConstr.kind_of_type sigma t with
     | CastType (t, ty) when !n_binders = 0 && EConstr.isSort sigma ty -> t
     | ProdType(n,s,t) -> decr n_binders; EConstr.mkProd (n, s, aux t)
     | LetInType(n,v,ty,t) -> decr n_binders; EConstr.mkLetIn (n, v, ty, aux t)
     | _ -> anomaly "pf_interp_ty: ssr Type cast deleted by typecheck" in
     sigma, aux t in
   let sigma, cty as ty = strip_cast (interp_term ist gl ty) in
   let ty =
     let env = pf_env gl in
     if not resolve_typeclasses then ty
     else
       let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
       sigma, Evarutil.nf_evar sigma cty in
   let n, c, _, ucst = pf_abs_evars gl ty in
   let lam_c = pf_abs_cterm gl n c in
   let ctx, c = EConstr.decompose_lam_n_assum sigma n lam_c in
   n, EConstr.it_mkProd_or_LetIn c ctx, lam_c, ucst
;;

(* TASSI: given (c : ty), generates (c ??? : ty[???/...]) with m evars *)
exception NotEnoughProducts
let saturate ?(beta=false) ?(bi_types=false) env sigma c ?(ty=Retyping.get_type_of env sigma c) m 
=
  let rec loop ty args sigma n = 
  if n = 0 then 
    let args = List.rev args in
     (if beta then Reductionops.whd_beta sigma else fun x -> x)
      (EConstr.mkApp (c, Array.of_list (List.map snd args))), ty, args, sigma 
  else match EConstr.kind_of_type sigma ty with
  | ProdType (_, src, tgt) ->
      let sigma = create_evar_defs sigma in
      let (sigma, x) =
        Evarutil.new_evar env sigma
          (if bi_types then Reductionops.nf_betaiota env sigma src else src) in
      loop (EConstr.Vars.subst1 x tgt) ((m - n,x) :: args) sigma (n-1)
  | CastType (t, _) -> loop t args sigma n 
  | LetInType (_, v, _, t) -> loop (EConstr.Vars.subst1 v t) args sigma n
  | SortType _ -> assert false
  | AtomicType _ ->
      let ty =  (* FIXME *)
        (Reductionops.whd_all env sigma) ty in
      match EConstr.kind_of_type sigma ty with
      | ProdType _ -> loop ty args sigma n
      | _ -> raise NotEnoughProducts
  in
   loop ty [] sigma m

let pf_saturate ?beta ?bi_types gl c ?ty m = 
  let env, sigma, si = pf_env gl, project gl, sig_it gl in
  let t, ty, args, sigma = saturate ?beta ?bi_types env sigma c ?ty m in
  t, ty, args, re_sig si sigma 

let pf_partial_solution gl t evl =
  let sigma, g = project gl, sig_it gl in
  let sigma = Goal.V82.partial_solution sigma g t in
  re_sig (List.map (fun x -> (fst (EConstr.destEvar sigma x))) evl) sigma

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
let applyn ~with_evars ?beta ?(with_shelve=false) n t gl =
  if with_evars then
    let refine gl =
      let t, ty, args, gl = pf_saturate ?beta ~bi_types:true gl t n in
(*       pp(lazy(str"sigma@saturate=" ++ pr_evar_map None (project gl))); *)
      let gl = pf_unify_HO gl ty (Tacmach.pf_concl gl) in
      let gs = CList.map_filter (fun (_, e) ->
        if EConstr.isEvar (project gl) e then Some e else None)
        args in
      pf_partial_solution gl t gs
    in
    Proofview.(V82.of_tactic
      (tclTHEN (V82.tactic refine)
        (if with_shelve then shelve_unifiable else tclUNIT ()))) gl
  else
    let t, gl = if n = 0 then t, gl else
      let sigma, si = project gl, sig_it gl in
      let rec loop sigma bo args = function (* saturate with metas *)
        | 0 -> EConstr.mkApp (t, Array.of_list (List.rev args)), re_sig si sigma 
        | n -> match EConstr.kind sigma bo with
          | Lambda (_, ty, bo) -> 
              if not (EConstr.Vars.closed0 sigma ty) then
                raise dependent_apply_error;
              let m = Evarutil.new_meta () in
              loop (meta_declare m ty sigma) bo ((EConstr.mkMeta m)::args) (n-1)
          | _ -> assert false
      in loop sigma t [] n in
    pp(lazy(str"Refiner.refiner " ++ Printer.pr_econstr_env (pf_env gl) (project gl) t));
    Tacmach.refine_no_check t gl

let refine_with ?(first_goes_last=false) ?beta ?(with_evars=true) oc gl =
  let rec mkRels = function 1 -> [] | n -> mkRel n :: mkRels (n-1) in
  let uct = Evd.evar_universe_context (fst oc) in
  let n, oc = pf_abs_evars_pirrel gl (fst oc, EConstr.Unsafe.to_constr (snd oc)) in
  let gl = pf_unsafe_merge_uc uct gl in
  let oc = if not first_goes_last || n <= 1 then oc else
    let l, c = decompose_lam oc in
    if not (List.for_all_i (fun i (_,t) -> Vars.closedn ~-i t) (1-n) l) then oc else
    compose_lam (let xs,y = List.chop (n-1) l in y @ xs) 
      (mkApp (compose_lam l c, Array.of_list (mkRel 1 :: mkRels n)))
  in
  pp(lazy(str"after: " ++ Printer.pr_constr_env (pf_env gl) (project gl) oc));
  try applyn ~with_evars ~with_shelve:true ?beta n (EConstr.of_constr oc) gl
  with e when CErrors.noncritical e -> raise dependent_apply_error

(** Profiling *)(* {{{ *************************************************************)
type profiler = { 
  profile : 'a 'b. ('a -> 'b) -> 'a -> 'b;
  reset : unit -> unit;
  print : unit -> unit }
let profile_now = ref false
let something_profiled = ref false
let profilers = ref []
let add_profiler f = profilers := f :: !profilers;;
let _ =
  Goptions.declare_bool_option
    { Goptions.optname  = "ssreflect profiling";
      Goptions.optkey   = ["SsrProfiling"];
      Goptions.optread  = (fun _ -> !profile_now);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b -> 
        Ssrmatching.profile b;
        profile_now := b;
        if b then List.iter (fun f -> f.reset ()) !profilers;
        if not b then List.iter (fun f -> f.print ()) !profilers) }
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

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.set_keyword_state frozen_lexer ;;

(** Basic tactics *)

let rec fst_prod red tac = Proofview.Goal.nf_enter begin fun gl ->
  let concl = Proofview.Goal.concl gl in
  match EConstr.kind (Proofview.Goal.sigma gl) concl with
  | Prod (id,_,tgt) | LetIn(id,_,_,tgt) -> tac id
  | _ -> if red then Tacticals.New.tclZEROMSG (str"No product even after head-reduction.")
         else Tacticals.New.tclTHEN Tactics.hnf_in_concl (fst_prod true tac)
end

let introid ?(orig=ref Anonymous) name = tclTHEN (fun gl ->
   let g, env = Tacmach.pf_concl gl, pf_env gl in
   let sigma = project gl in
   match EConstr.kind sigma g with
   | App (hd, _) when EConstr.isLambda sigma hd -> 
      Proofview.V82.of_tactic (convert_concl_no_check (Reductionops.whd_beta sigma g)) gl
   | _ -> tclIDTAC gl)
  (Proofview.V82.of_tactic
    (fst_prod false (fun id -> orig := id; Tactics.intro_mustbe_force name)))
;;

let anontac decl gl =
  let id =  match RelDecl.get_name decl with
  | Name id ->
    if is_discharged_id id then id else mk_anon_id (Id.to_string id) (Tacmach.pf_ids_of_hyps gl)
  | _ -> mk_anon_id ssr_anon_hyp (Tacmach.pf_ids_of_hyps gl) in
  introid id gl

let rec intro_anon gl =
  try anontac (List.hd (fst (EConstr.decompose_prod_n_assum (project gl) 1 (Tacmach.pf_concl gl)))) gl
  with err0 -> try tclTHEN (Proofview.V82.of_tactic Tactics.red_in_concl) intro_anon gl with e when CErrors.noncritical e -> raise err0
  (* with _ -> CErrors.error "No product even after reduction" *)

let is_pf_var sigma c =
  EConstr.isVar sigma c && not_section_id (EConstr.destVar sigma c)

let hyp_of_var sigma v = SsrHyp (Loc.tag @@ EConstr.destVar sigma v)

let interp_clr sigma = function
| Some clr, (k, c) 
  when (k = xNoFlag  || k = xWithAt) && is_pf_var sigma c ->
   hyp_of_var sigma c :: clr 
| Some clr, _ -> clr
| None, _ -> []

(** Basic tacticals *)

(** Multipliers *)(* {{{ ***********************************************************)

(* tactical *)

let tclID tac = tac

let tclDOTRY n tac =
  if n <= 0 then tclIDTAC else
  let rec loop i gl =
    if i = n then tclTRY tac gl else
    tclTRY (tclTHEN tac (loop (i + 1))) gl in
  loop 1

let tclDO n tac =
  let prefix i = str"At iteration " ++ int i ++ str": " in
  let tac_err_at i gl =
    try tac gl
    with 
    | CErrors.UserError (l, s) as e ->
        let _, info = CErrors.push e in
        let e' = CErrors.UserError (l, prefix i ++ s) in
        Util.iraise (e', info)
    | Ploc.Exc(loc, CErrors.UserError (l, s))  -> 
        raise (Ploc.Exc(loc, CErrors.UserError (l, prefix i ++ s))) in
  let rec loop i gl =
    if i = n then tac_err_at i gl else
    (tclTHEN (tac_err_at i) (loop (i + 1))) gl in
  loop 1

let tclMULT = function
  | 0, May  -> tclREPEAT
  | 1, May  -> tclTRY
  | n, May  -> tclDOTRY n
  | 0, Must -> tclAT_LEAST_ONCE
  | n, Must when n > 1 -> tclDO n
  | _       -> tclID

let old_cleartac clr = check_hyps_uniq [] clr; Proofview.V82.of_tactic (Tactics.clear (hyps_ids clr))
let cleartac clr = check_hyps_uniq [] clr; Tactics.clear (hyps_ids clr)

(* }}} *)

(** Generalize tactic *)

(* XXX the k of the redex should percolate out *)
let pf_interp_gen_aux gl to_ind ((oclr, occ), t) =
  let pat = interp_cpattern gl t None in (* UGLY API *)
  let cl, env, sigma = Tacmach.pf_concl gl, pf_env gl, project gl in
  let (c, ucst), cl = 
    try fill_occ_pattern ~raise_NoMatch:true env sigma (EConstr.Unsafe.to_constr cl) pat occ 1
    with NoMatch -> redex_of_pattern env pat, (EConstr.Unsafe.to_constr cl) in
  let gl = pf_merge_uc ucst gl in
  let c = EConstr.of_constr c in
  let cl = EConstr.of_constr cl in
  let clr = interp_clr sigma (oclr, (tag_of_cpattern t, c)) in
  if not(occur_existential sigma c) then
    if tag_of_cpattern t = xWithAt then 
      if not (EConstr.isVar sigma c) then
	errorstrm (str "@ can be used with variables only")
      else match Tacmach.pf_get_hyp gl (EConstr.destVar sigma c) with
      | NamedDecl.LocalAssum _ -> errorstrm (str "@ can be used with let-ins only")
      | NamedDecl.LocalDef (name, b, ty) -> true, pat, EConstr.mkLetIn (Name name,b,ty,cl),c,clr,ucst,gl
    else let gl, ccl =  pf_mkprod gl c cl in false, pat, ccl, c, clr,ucst,gl
  else if to_ind && occ = None then
    let nv, p, _, ucst' = pf_abs_evars gl (fst pat, c) in
    let ucst = UState.union ucst ucst' in
    if nv = 0 then anomaly "occur_existential but no evars" else
    let gl, pty = pfe_type_of gl p in
    false, pat, EConstr.mkProd (constr_name (project gl) c, pty, Tacmach.pf_concl gl), p, clr,ucst,gl
  else CErrors.user_err ?loc:(loc_of_cpattern t) (str "generalized term didn't match")

let apply_type x xs = Proofview.V82.of_tactic (Tactics.apply_type ~typecheck:true x xs)

let genclrtac cl cs clr =
  let tclmyORELSE tac1 tac2 gl =
    try tac1 gl
    with e when CErrors.noncritical e -> tac2 e gl in
  (* apply_type may give a type error, but the useful message is
   * the one of clear.  You type "move: x" and you get
   * "x is used in hyp H" instead of
   * "The term H has type T x but is expected to have type T x0". *)
  tclTHEN
    (tclmyORELSE
      (apply_type cl cs)
      (fun type_err gl ->
         tclTHEN
           (tclTHEN (Proofview.V82.of_tactic (Tactics.elim_type (EConstr.of_constr
             (UnivGen.constr_of_global @@ Coqlib.build_coq_False ())))) (old_cleartac clr))
           (fun gl -> raise type_err)
           gl))
    (old_cleartac clr)

let gentac gen gl =
(*   ppdebug(lazy(str"sigma@gentac=" ++ pr_evar_map None (project gl))); *)
  let conv, _, cl, c, clr, ucst,gl = pf_interp_gen_aux gl false gen in
  ppdebug(lazy(str"c@gentac=" ++ pr_econstr_env (pf_env gl) (project gl) c));
  let gl = pf_merge_uc ucst gl in
  if conv
  then tclTHEN (Proofview.V82.of_tactic (convert_concl cl)) (old_cleartac clr) gl
  else genclrtac cl [c] clr gl

let genstac (gens, clr) =
  tclTHENLIST (old_cleartac clr :: List.rev_map gentac gens)

let gen_tmp_ids
  ?(ist=Geninterp.({ lfun = Id.Map.empty; extra = Tacinterp.TacStore.empty })) gl
=
  let gl, ctx = pull_ctx gl in
  push_ctxs ctx
    (tclTHENLIST
      (List.map (fun (id,orig_ref) ->
        tclTHEN 
        (gentac ((None,Some(false,[])),cpattern_of_id id))
        (rename_hd_prod orig_ref))
      ctx.tmp_ids) gl)
;;

let pf_interp_gen gl to_ind gen =
  let _, _, a, b, c, ucst,gl = pf_interp_gen_aux gl to_ind gen in
  a, b ,c, pf_merge_uc ucst gl

(* TASSI: This version of unprotects inlines the unfold tactic definition, 
 * since we don't want to wipe out let-ins, and it seems there is no flag
 * to change that behaviour in the standard unfold code *)
let unprotecttac gl =
  let c, gl = pf_mkSsrConst "protect_term" gl in
  let prot, _ = EConstr.destConst (project gl) c in
  Tacticals.onClause (fun idopt ->
    let hyploc = Option.map (fun id -> id, InHyp) idopt in
    Proofview.V82.of_tactic (Tactics.reduct_option 
      (Reductionops.clos_norm_flags 
        (CClosure.RedFlags.mkflags 
          [CClosure.RedFlags.fBETA;
           CClosure.RedFlags.fCONST prot;
           CClosure.RedFlags.fMATCH;
           CClosure.RedFlags.fFIX;
           CClosure.RedFlags.fCOFIX]), DEFAULTcast) hyploc))
    allHypsAndConcl gl

let is_protect hd env sigma =
  let _, protectC = mkSsrConst "protect_term" env sigma in
  EConstr.eq_constr_nounivs sigma hd protectC

let abs_wgen keep_let f gen (gl,args,c) =
  let sigma, env = project gl, pf_env gl in
  let evar_closed t p =
    if occur_existential sigma t then
      CErrors.user_err ?loc:(loc_of_cpattern p) ~hdr:"ssreflect"
        (pr_constr_pat (EConstr.Unsafe.to_constr t) ++
        str" contains holes and matches no subterm of the goal") in
  match gen with
  | _, Some ((x, mode), None) when mode = "@" || (mode = " " && keep_let) ->
     let x = hoi_id x in
     let decl = Tacmach.pf_get_hyp gl x in
     gl,
     (if NamedDecl.is_local_def decl then args else EConstr.mkVar x :: args),
     EConstr.mkProd_or_LetIn (decl |> NamedDecl.to_rel_decl |> RelDecl.set_name (Name (f x)))
                     (EConstr.Vars.subst_var x c)
  | _, Some ((x, _), None) ->
     let x = hoi_id x in
     gl, EConstr.mkVar x :: args, EConstr.mkProd (Name (f x),Tacmach.pf_get_hyp_typ gl x, EConstr.Vars.subst_var x c)
  | _, Some ((x, "@"), Some p) -> 
     let x = hoi_id x in
     let cp = interp_cpattern gl p None in
     let (t, ucst), c =
       try fill_occ_pattern ~raise_NoMatch:true env sigma (EConstr.Unsafe.to_constr c) cp None 1
       with NoMatch -> redex_of_pattern env cp, (EConstr.Unsafe.to_constr c) in
     let c = EConstr.of_constr c in
     let t = EConstr.of_constr t in
     evar_closed t p;
     let ut = red_product_skip_id env sigma t in
     let gl, ty = pfe_type_of gl t in
     pf_merge_uc ucst gl, args, EConstr.mkLetIn(Name (f x), ut, ty, c)
  | _, Some ((x, _), Some p) ->
     let x = hoi_id x in
     let cp = interp_cpattern gl p None in
     let (t, ucst), c =
       try fill_occ_pattern ~raise_NoMatch:true env sigma (EConstr.Unsafe.to_constr c) cp None 1
       with NoMatch -> redex_of_pattern env cp, (EConstr.Unsafe.to_constr c) in
     let c = EConstr.of_constr c in
     let t = EConstr.of_constr t in
     evar_closed t p;
     let gl, ty = pfe_type_of gl t in
     pf_merge_uc ucst gl, t :: args, EConstr.mkProd(Name (f x), ty, c)
  | _ -> gl, args, c

let clr_of_wgen gen clrs = match gen with
  | clr, Some ((x, _), None) ->
     let x = hoi_id x in
     old_cleartac clr :: old_cleartac [SsrHyp(Loc.tag x)] :: clrs
  | clr, _ -> old_cleartac clr :: clrs


let reduct_in_concl t = Tactics.reduct_in_concl (t, DEFAULTcast)
let unfold cl =
  let module R = Reductionops in let module F = CClosure.RedFlags in
  reduct_in_concl (R.clos_norm_flags (F.mkflags
    (List.map (fun c -> F.fCONST (fst (destConst (EConstr.Unsafe.to_constr c)))) cl @
       [F.fBETA; F.fMATCH; F.fFIX; F.fCOFIX])))

open Proofview
open Notations

let tacSIGMA = Goal.enter_one begin fun g ->
  let k = Goal.goal g in
  let sigma = Goal.sigma g in
  tclUNIT (Tacmach.re_sig k sigma)
end

let tclINTERP_AST_CLOSURE_TERM_AS_CONSTR c =
  tclINDEPENDENTL begin tacSIGMA >>= fun gl ->
  let old_ssrterm = mkRHole, Some c.Ssrast.body in
  let ist =
    option_assert_get c.Ssrast.interp_env
      Pp.(str "tclINTERP_AST_CLOSURE_TERM_AS_CONSTR: term with no ist") in
  let sigma, t =
    interp_wit Stdarg.wit_constr ist gl old_ssrterm in
  Unsafe.tclEVARS sigma <*>
  tclUNIT t
end

let tacREDUCE_TO_QUANTIFIED_IND ty =
  tacSIGMA >>= fun gl ->
  tclUNIT (Tacmach.pf_reduce_to_quantified_ind gl ty)

let tacTYPEOF c = Goal.enter_one ~__LOC__ (fun g ->
  let sigma, env = Goal.sigma g, Goal.env g in
  let sigma, ty = Typing.type_of env sigma c in
  Unsafe.tclEVARS sigma <*> tclUNIT ty)

(** This tactic creates a partial proof realizing the introduction rule, but
    does not check anything. *)
let unsafe_intro env store decl b =
  let open Context.Named.Declaration in
  Refine.refine ~typecheck:false begin fun sigma ->
    let ctx = Environ.named_context_val env in
    let nctx = EConstr.push_named_context_val decl ctx in
    let inst = List.map (get_id %> EConstr.mkVar) (Environ.named_context env) in
    let ninst = EConstr.mkRel 1 :: inst in
    let nb = EConstr.Vars.subst1 (EConstr.mkVar (get_id decl)) b in
    let sigma, ev =
      Evarutil.new_evar_instance nctx sigma nb ~principal:true ~store ninst in
    sigma, EConstr.mkNamedLambda_or_LetIn decl ev
  end

let set_decl_id id = let open Context in function
  | Rel.Declaration.LocalAssum(name,ty) -> Named.Declaration.LocalAssum(id,ty)
  | Rel.Declaration.LocalDef(name,ty,t) -> Named.Declaration.LocalDef(id,ty,t)

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
  Tactics.e_reduct_in_concl ~check:false (r,Constr.DEFAULTcast)
end

(** [intro id k] introduces the first premise (product or let-in) of the goal
    under the name [id], reducing the head of the goal (using beta, iota, delta
    but not zeta) if necessary. If [id] is None, a name is generated, that will
    not be user accessible. If the goal does not start with a product or a
let-in even after reduction, it fails. In case of success, the original name
and final id are passed to the continuation [k] which gets evaluated. *)
let tclINTRO ~id ~conclusion:k = Goal.enter begin fun gl ->
  let open Context in
  let env, sigma, extra, g = Goal.(env gl, sigma gl, extra gl, concl gl) in
  let decl, t, no_red = decompose_assum env sigma g in
  let original_name = Rel.Declaration.get_name decl in
  let already_used = Tacmach.New.pf_ids_of_hyps gl in
  let id = match id, original_name with
    | Some id, _ -> id
    | _, Name id ->
       if is_discharged_id id then id
       else mk_anon_id (Id.to_string id) already_used
    | _, _ ->
       let ids = Tacmach.New.pf_ids_of_hyps gl in
       mk_anon_id ssr_anon_hyp ids
  in
  if List.mem id already_used then
    errorstrm Pp.(Id.print id ++ str" already used");
  unsafe_intro env extra (set_decl_id id decl) t <*>
  (if no_red then tclUNIT () else tclFULL_BETAIOTA) <*>
  k ~orig_name:original_name ~new_name:id
end

let return ~orig_name:_ ~new_name:_ = tclUNIT ()

let tclINTRO_ID id = tclINTRO ~id:(Some id) ~conclusion:return
let tclINTRO_ANON = tclINTRO ~id:None ~conclusion:return

let tclRENAME_HD_PROD name = Goal.enter begin fun gl ->
  let convert_concl_no_check t =
    Tactics.convert_concl_no_check t DEFAULTcast in
  let concl = Goal.concl gl in
  let sigma = Goal.sigma gl in
  match EConstr.kind sigma concl with
  | Prod(_,src,tgt) ->
      convert_concl_no_check EConstr.(mkProd (name,src,tgt))
  | _ -> CErrors.anomaly (Pp.str "rename_hd_prod: no head product")
end

let tcl0G tac =
  numgoals >>= fun ng -> if ng = 0 then tclUNIT () else tac

let rec tclFIRSTa = function
  | [] -> Tacticals.New.tclZEROMSG Pp.(str"No applicable tactic.")
  | tac :: rest -> tclORELSE tac (fun _ -> tclFIRSTa rest)

let rec tclFIRSTi tac n =
  if n < 0 then Tacticals.New.tclZEROMSG Pp.(str "tclFIRSTi")
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
    if name <> Names.Name.Anonymous || EConstr.Vars.noccurn sigma  1 cl
    then tclUNIT (EConstr.mkProd (name, t, cl))
    else
      let name = Names.Id.of_string (Namegen.hdchar env sigma t) in
      tclUNIT (EConstr.mkProd (Names.Name.Name name, t, cl))
end

let tacINTERP_CPATTERN cp =
  tacSIGMA >>= begin fun gl ->
  tclUNIT (Ssrmatching.interp_cpattern gl cp None)
end

let tacUNIFY a b =
  tacSIGMA >>= begin fun gl ->
  let gl = Ssrmatching.pf_unify_HO gl a b in
  Unsafe.tclEVARS (Tacmach.project gl)
end

let tclOPTION o d =
  match o with
  | None -> d >>= tclUNIT
  | Some x -> tclUNIT x

let tacIS_INJECTION_CASE ?ty t = begin
  tclOPTION ty (tacTYPEOF t) >>= fun ty ->
  tacREDUCE_TO_QUANTIFIED_IND ty >>= fun ((mind,_),_) ->
  tclUNIT (GlobRef.equal (GlobRef.IndRef mind) (Coqlib.build_coq_eq ()))
end

let tclWITHTOP tac = Goal.enter begin fun gl ->
  let top =
    mk_anon_id "top_assumption" (Tacmach.New.pf_ids_of_hyps gl) in
  tclINTRO_ID top <*>
  tac (EConstr.mkVar top) <*>
  Tactics.clear [top]
end

let tacMK_SSR_CONST name = Goal.enter_one ~__LOC__ begin fun g ->
  let sigma, env = Goal.(sigma g, env g) in
  let sigma, c = mkSsrConst name env sigma in
  Unsafe.tclEVARS sigma <*>
  tclUNIT c
end

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


(* vim: set filetype=ocaml foldmethod=marker: *)
