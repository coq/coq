(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Bruno Barras with Benjamin Werner's account to implement
   a call-by-value conversion algorithm and a lazy reduction machine
   with sharing, Nov 1996 *)
(* Addition of zeta-reduction (let-in contraction) by Hugo Herbelin, Oct 2000 *)
(* Call-by-value machine moved to cbv.ml, Mar 01 *)
(* Additional tools for module subtyping by Jacek Chrzaszcz, Aug 2002 *)
(* Extension with closure optimization by Bruno Barras, Aug 2003 *)
(* Support for evar reduction by Bruno Barras, Feb 2009 *)
(* Miscellaneous other improvements by Bruno Barras, 1997-2009 *)

(* This file implements a lazy reduction for the Calculus of Inductive
   Constructions *)

[@@@ocaml.warning "+4"]
[@@@ocaml.warning "@27"]

open CErrors
open Util
open Names
open Constr
open Declarations
open Context
open Environ
open Vars
open Esubst
open RedFlags

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration
[@@@ocaml.warning "-60"]
module EqWithHoles = struct
  [@@@ocaml.warning "-32"]
  let eq_under_context eq ~base ~under (nas1, p1) (nas2, p2) =
    Int.equal (Array.length nas1) (Array.length nas2) &&
    eq ~base:(base + Array.length nas1) ~under:(under + Array.length nas1) p1 p2
  let eq_invert eq iv1 iv2 =
    match iv1, iv2 with
    | NoInvert, NoInvert -> true
    | NoInvert, CaseInvert _ | CaseInvert _, NoInvert -> false
    | CaseInvert {indices}, CaseInvert iv2 ->
      Array.equal eq indices iv2.indices
  (* Copied and generalized *)
  let compare_head_gen_leq_with kind1 kind2 leq_universes leq_sorts eq_evars eq leq ~nargs ~base ~under t1 t2 =
    match kind_nocast_gen kind1 t1, kind_nocast_gen kind2 t2 with
    | Cast _, _ | _, Cast _ -> assert false (* kind_nocast *)
    | Rel n1, Rel n2 -> Int.equal n1 n2
    | Meta m1, Meta m2 -> Int.equal m1 m2
    | Var id1, Var id2 -> Id.equal id1 id2
    | Int i1, Int i2 -> Uint63.equal i1 i2
    | Float f1, Float f2 -> Float64.equal f1 f2
    | String s1, String s2 -> Pstring.equal s1 s2
    | Sort s1, Sort s2 -> leq_sorts s1 s2
    | Prod (_,t1,c1), Prod (_,t2,c2) -> eq ~nargs:0 ~base ~under t1 t2 && leq ~nargs:0 ~base:(base+1) ~under:(under+1) c1 c2
    | Lambda (_,t1,c1), Lambda (_,t2,c2) -> eq ~nargs:0 ~base ~under t1 t2 && eq ~nargs:0 ~base:(base+1) ~under:(under+1) c1 c2
    | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> eq ~nargs:0 ~base ~under b1 b2 && eq ~nargs:0 ~base ~under t1 t2 && leq ~nargs ~base:(base+1) ~under:(under+1) c1 c2
    | App (c1, l1), App (c2, l2) ->
      let len = Array.length l1 in
      Int.equal len (Array.length l2) &&
      leq ~nargs:(nargs+len) ~base ~under c1 c2 && Array.equal_norefl (eq ~nargs:0 ~base ~under) l1 l2
    | Proj (p1,_,c1), Proj (p2,_,c2) ->
      Projection.CanOrd.equal p1 p2 && eq ~nargs:0 ~base ~under c1 c2
    | Evar (e1,l1), Evar (e2,l2) -> eq_evars ~nargs ~base ~under (e1, l1) (e2, l2)
    | Const (c1,u1), Const (c2,u2) ->
      (* The args length currently isn't used but may as well pass it. *)
      Constant.CanOrd.equal c1 c2 && leq_universes (Some (GlobRef.ConstRef c1, nargs)) u1 u2
    | Ind (c1,u1), Ind (c2,u2) -> Ind.CanOrd.equal c1 c2 && leq_universes (Some (GlobRef.IndRef c1, nargs)) u1 u2
    | Construct (c1,u1), Construct (c2,u2) ->
      Construct.CanOrd.equal c1 c2 && leq_universes (Some (GlobRef.ConstructRef c1, nargs)) u1 u2
    | Case (ci1,u1,pms1,(p1,_r1),iv1,c1,bl1), Case (ci2,u2,pms2,(p2,_r2),iv2,c2,bl2) ->
      (* Ignore _r1/_r2: implied by comparing p1/p2 *)
      (* FIXME: what are we doing with u1 = u2 ? *)
      Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind && leq_universes (Some (GlobRef.IndRef ci1.ci_ind, 0)) u1 u2 &&
      Array.equal (eq ~nargs:0 ~base ~under) pms1 pms2 && eq_under_context (eq ~nargs:0) ~base ~under p1 p2 &&
      eq_invert (eq ~nargs:0 ~base ~under) iv1 iv2 &&
      eq ~nargs:0 ~base ~under c1 c2 && Array.equal (eq_under_context (eq ~nargs:0) ~base ~under) bl1 bl2
    | Fix ((ln1, i1),(_,tl1,bl1)), Fix ((ln2, i2),(_,tl2,bl2)) ->
      Int.equal i1 i2 && Array.equal Int.equal ln1 ln2
      && Array.equal_norefl (eq ~nargs:0 ~base ~under) tl1 tl2 && Array.equal_norefl (eq ~nargs:0 ~base ~under) bl1 bl2
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
      Int.equal ln1 ln2 && Array.equal_norefl (eq ~nargs:0 ~base ~under) tl1 tl2 && Array.equal_norefl (eq ~nargs:0 ~base ~under) bl1 bl2
    | Array(u1,t1,def1,ty1), Array(u2,t2,def2,ty2) ->
      leq_universes None u1 u2 &&
      Array.equal_norefl (eq ~nargs:0 ~base ~under) t1 t2 &&
      eq ~nargs:0 ~base ~under def1 def2 && eq ~nargs:0 ~base ~under ty1 ty2
    | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
      | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
      | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false

  let noccur_outside n m term =
    let rec occur_rec n c = match [@ocaml.warning "-4"] Constr.kind c with
      | Constr.Rel p -> if n>p || p>n+m then raise_notrace Not_found
      | _        -> Constr.iter_with_binders succ occur_rec n c
    in
    try occur_rec n term; true with Not_found -> false

  let eq_existential eq ~evs ~nargs ~base ~under (evk1, args1) (evk2, args2) =
    ignore nargs; ignore under;
    if Evar.equal evk1 evk2 then
      let open CClosure in
      let args1 = evs.evar_expand (evk1, args1) in
      let args2 = evs.evar_expand (evk2, args2) in
      match [@ocaml.warning "-4"] args1, args2 with
      | EvarDefined t1, EvarDefined t2 -> eq ~nargs ~base ~under t1 t2
      | EvarUndefined (ev1, args1), EvarUndefined (ev2, args2) ->
        Evar.equal ev1 ev2 &&
        List.equal (eq ~nargs ~base ~under) args1 args2
      | _, _ -> false
    else false
    let eq_inst _ i1 i2 = UVars.Instance.equal i1 i2
    let eq_sorts s1 s2 = Sorts.equal s1 s2

    let eq ~map ~evs =
      let rec eq ~nargs ~base ~under l r =
        let f = compare_head_gen_leq_with Constr.kind Constr.kind eq_inst eq_sorts (eq_existential eq ~evs) eq eq ~nargs ~base ~under in
        (l == r) ||
        match [@ocaml.warning "-4"] Constr.kind l, Constr.kind r with
        | _, Constr.Meta i when i < 0 ->
          begin
            (noccur_outside under (base-under) l) &&
            let j = i * -1 - 1 in
            match map.(j) with
            | None ->
              let r = Vars.lift (under * -1) l in
              Array.set map j (Some r);
              true
            | Some r ->
              f l (Vars.lift under r)
          end
        | _, _ -> f l r
      in
      eq

  (* [info] should only have beta enabled *)
  let matches_with_holes info tab (evs : CClosure.evar_handler) num_holes (term : Constr.t) (pattern : Constr.t) : Constr.t option array option =
    let map : Constr.t option array = Array.make num_holes None in
    let args = Array.init num_holes (fun i -> (Constr.mkMeta (i * -1 -1))) in
    let pattern = CClosure.norm_val info tab (CClosure.inject (Constr.mkApp (pattern,args))) in
    let base =
      let rec go under acc t =
        match [@ocaml.warning "-4"] Constr.kind t with
        | Constr.Rel i -> max acc (i - under)
        | _ -> Constr.fold_constr_with_binders (fun i -> i + 1) go acc under t
      in
      go 0 0 term
    in
    if eq ~map ~evs ~nargs:0 ~base ~under:0 term pattern then
      Some map
    else
      None
end

(**********************************************************************)
(* Lazy reduction: the one used in kernel operations                  *)

(* type of shared terms. fconstr and frterm are mutually recursive.
 * Clone of the constr structure, but completely mutable, and
 * annotated with reduction state (reducible or not).
 *  - FLIFT is a delayed shift; allows sharing between 2 lifted copies
 *    of a given term.
 *  - FCLOS is a delayed substitution applied to a constr
 *)

(* Ntrl means the term is in βιδζ head normal form and cannot create a redex
     when substituted
   Cstr means the term is in βιδζ head normal form and that it can
     create a redex when substituted (i.e. constructor, fix, lambda)
   Red is used for terms that might be reduced
*)
type red_state = Ntrl | Cstr | Red

let neutr = function Ntrl -> Ntrl | Red | Cstr -> Red
let is_red = function Red -> true | Ntrl | Cstr -> false

type table_key = Constant.t UVars.puniverses tableKey

type evar_repack = Evar.t * constr list -> constr

(* Global (Co)Fixpoints *)
type gfix = (Constr.t,unit) Result.t Lazy.t array
type gcofix = (Constr.t,unit) Result.t Lazy.t array

type ('a,'r) gfix_info_aux = {
  gfix_nargs : int;
  gfix_tys : (Name.t binder_annot * constr) list;
  gfix_univs : UVars.Instance.t;
  gfix_body : 'a;
  gfix_refold : 'r;
}

type gfix_info =
  | GFixInfo of (fixpoint, gfix) gfix_info_aux
  | GCoFixInfo of (cofixpoint, gcofix) gfix_info_aux

type fconstr = {
  mutable mark : red_state;
  mutable term: fterm;
}

and fterm =
  | FRel of int
  | FAtom of constr (* Metas and Sorts *)
  | FFlex of table_key
  | FInd of pinductive
  | FConstruct of pconstructor
  | FApp of fconstr * fconstr array
  | FProj of Projection.t * Sorts.relevance * fconstr
  | FFix of fixpoint * usubs * bool * gfix option
  | FCoFix of cofixpoint * usubs * gcofix option
  | FCaseT of case_info * UVars.Instance.t * constr array * case_return * fconstr * case_branch array * usubs (* predicate and branches are closures *)
  | FCaseInvert of case_info * UVars.Instance.t * constr array * case_return * finvert * fconstr * case_branch array * usubs
  | FLambda of int * (Name.t binder_annot * constr) list * constr * usubs
  | FProd of Name.t binder_annot * fconstr * constr * usubs
  | FLetIn of Name.t binder_annot * fconstr * fconstr * constr * usubs
  | FEvar of Evar.t * constr list * usubs * evar_repack
  | FInt of Uint63.t
  | FFloat of Float64.t
  | FString of Pstring.t
  | FArray of UVars.Instance.t * fconstr Parray.t * fconstr
  | FLIFT of int * fconstr
  | FCLOS of constr * usubs
  | FIrrelevant

and usubs = fconstr subs UVars.puniverses

and finvert = fconstr array

let set_ntrl v = v.mark <- Ntrl

(** Reduction cache *)
type infos_cache = {
  i_env : env;
  i_sigma : CClosure.evar_handler;
  i_share : bool;
  i_univs : UGraph.t;
}

type clos_infos = {
  i_flags : reds;
  i_relevances : Sorts.relevance Range.t;
  i_cache : infos_cache;
  i_cc_info_beta : CClosure.clos_infos;
  i_cc_tab : CClosure.clos_tab;
}

let info_env info = info.i_cache.i_env

let push_relevance infos x =
  { infos with i_relevances = Range.cons x.binder_relevance infos.i_relevances }

let push_relevances infos nas =
  { infos with
    i_relevances =
      Array.fold_left (fun l x -> Range.cons x.binder_relevance l)
        infos.i_relevances nas }

let usubs_shft (n,(e,u)) = subs_shft (n, e), u

(* Lifting. Preserves sharing (useful only for cell with norm=Red).
   lft_fconstr always create a new cell, while lift_fconstr avoids it
   when the lift is 0. *)
let rec lft_fconstr n ft =
  match ft.term with
    | (FInd _|FConstruct _|FFlex(ConstKey _|VarKey _)|FInt _|FFloat _|FString _|FIrrelevant) -> ft
    | FRel i -> {mark=ft.mark;term=FRel(i+n)}
    | FLambda(k,tys,f,e) -> {mark=Cstr; term=FLambda(k,tys,f,usubs_shft(n,e))}
    | FFix(fx,e,must_unfold,gfix) ->
      {mark=Cstr; term=FFix(fx,usubs_shft(n,e),must_unfold,gfix)}
    | FCoFix(cfx,e,gcofix) ->
      {mark=Cstr; term=FCoFix(cfx,usubs_shft(n,e),gcofix)}
    | FLIFT(k,m) -> lft_fconstr (n+k) m
    | FFlex (RelKey _) | FAtom _ | FApp _ | FProj _ | FCaseT _ | FCaseInvert _ | FProd _
      | FLetIn _ | FEvar _ | FCLOS _ | FArray _ -> {mark=ft.mark; term=FLIFT(n,ft)}
let lift_fconstr k f =
  if Int.equal k 0 then f else lft_fconstr k f
let lift_fconstr_vect k v =
  if Int.equal k 0 then v else Array.Fun1.map lft_fconstr k v

let clos_rel e i =
  match expand_rel i e with
    | Inl(n,mt) -> lift_fconstr n mt
    | Inr(k,None) -> {mark=Ntrl; term= FRel k}
    | Inr(k,Some p) ->
        lift_fconstr (k-p) {mark=Red;term=FFlex(RelKey p)}

(* We use empty as a special identity value, if we don't check
   subst_instance_instance will raise array out of bounds. *)
let usubst_instance (_,u) u' =
  if UVars.Instance.is_empty u then u'
  else UVars.subst_instance_instance u u'

let usubst_punivs (_,u) (v,u' as orig) =
  if UVars.Instance.is_empty u then orig
  else v, UVars.subst_instance_instance u u'

let usubst_sort (_,u) s =
  if UVars.Instance.is_empty u then s
  else UVars.subst_instance_sort u s

let usubst_relevance (_,u) r =
  if UVars.Instance.is_empty u then r
  else UVars.subst_instance_relevance u r

let usubst_binder e x =
  let r = x.binder_relevance in
  let r' = usubst_relevance e r in
  if r == r' then x else { x with binder_relevance = r' }

let mk_lambda env t =
  let (rvars,t') = Term.decompose_lambda t in
  FLambda(List.length rvars, List.rev rvars, t', env)

let usubs_lift (e,u) = subs_lift e, u

let usubs_liftn n (e,u) = subs_liftn n e, u

let rec subs_consn v i n s =
  if Int.equal i n then s
  else subs_consn v (i + 1) n (subs_cons v.(i) s)

let usubs_consn v i n s = on_fst (subs_consn v i n) s

let usubs_consv v s =
  usubs_consn v 0 (Array.length v) s


(* Optimization: do not enclose variables in a closure.
   Makes variable access much faster *)
let mk_clos (e:usubs) t =
  match kind t with
    | Rel i -> clos_rel (fst e) i
    | Var x -> {mark = Red; term = FFlex (VarKey x) }
    | Const c -> {mark = Red; term = FFlex (ConstKey (usubst_punivs e c)) }
    | Sort s ->
      let s = usubst_sort e s in
      {mark = Ntrl; term = FAtom (mkSort s) }
    | Meta _ -> {mark = Ntrl; term = FAtom t }
    | Ind kn -> {mark = Ntrl; term = FInd (usubst_punivs e kn) }
    | Construct kn -> {mark = Cstr; term = FConstruct (usubst_punivs e kn) }
    | Int i -> {mark = Cstr; term = FInt i}
    | Float f -> {mark = Cstr; term = FFloat f}
    | String s -> {mark = Cstr; term = FString s}
    | (CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _|Proj _|Array _) ->
        {mark = Red; term = FCLOS(t,e)}

let injectu c u = mk_clos (subs_id 0, u) c

let inject c = injectu c UVars.Instance.empty

let mk_irrelevant = { mark = Cstr; term = FIrrelevant }

let is_irrelevant _info _r = false



(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *)
type 'a next_native_args = (CPrimitives.arg_kind * 'a) list

module Undo = struct
  type t =
  | OnMatchFix
  | OnNoProgress

  let pp u =
    let open Pp in
    match u with
    | OnMatchFix -> str "OnMatchFix"
    | OnNoProgress -> str "OnNoProgress"

  let remove_OnNoProgress us =
    try
      List.remove_first (fun u -> u = OnNoProgress) us
    with Not_found -> us

  let remove_OnMatchFix us =
    try
      List.remove_first (fun u -> u = OnMatchFix) us
    with Not_found -> us
end

module Original = struct
  type t = {
    term: fconstr;
    body: fconstr;
  }
end

module UnfoldDef = struct
  type t = {
    orig : Original.t;
    ogfix : gfix_info option;
    recargs_shift : int;
    recargs : int list;
    undo : Undo.t list;
    must_unfold: bool;
  }

  let pp { undo; _ } =
    let open Pp in
    hov 2 (str "{" ++ str "_" ++ str ",[" ++ prlist_with_sep (fun () -> str ",") Undo.pp undo ++ str "]}")
end

module UnfoldProj = struct
  type t = {
    orig : Original.t;
    undo: Undo.t list;
  }

  let pp { undo; _ } =
    let open Pp in
    hov 2 (str "{" ++ str "_" ++ str "," ++ prlist_with_sep (fun () -> str",") Undo.pp undo ++ str "}")
end

module Stack = struct
  type stack_member =
    | Zapp of fconstr array
    | ZcaseT of case_info * UVars.Instance.t * constr array * case_return * case_branch array * usubs
    | Zproj of UnfoldProj.t * Projection.Repr.t * Sorts.relevance
    | Zfix of fconstr * stack
    | Zprimitive of CPrimitives.t * pconstant * fconstr list * fconstr next_native_args
        (* operator, constr def, arguments already seen (in rev order), next arguments *)
    | Zshift of int
    | Zunfold of (Undo.t list * Original.t * stack) option * UnfoldDef.t * stack (* stack argument is reversed; undo is for the focused argument; the stack there is reversed as well *)
    | ZundoOrRefold of Undo.t list * bool * Original.t * stack (* the stack argument is reversed *)

  and stack = stack_member list

  let rec push_progress (s : stack) =
    match s with
    | [] -> s
    | (Zapp _) as z :: s -> z :: push_progress s
    | (Zshift _ as z)::s -> z :: push_progress s
    | (ZcaseT (_, _, _, _, _, _))::_ -> s
    | (Zproj (_, _, _))::_ -> s
    | (Zfix _)::_ -> s
    | (Zprimitive (_, _, _, _))::_ -> s
    | (Zunfold (Some (undos, orig, rev_params'), unf, rev_params)) :: s ->
      let undo = Some (Undo.remove_OnNoProgress undos, orig, rev_params') in
      Zunfold (undo, unf, rev_params) :: s
    | (Zunfold _ :: _) -> s
    | ZundoOrRefold (undos, _, orig, rev_params) :: s' ->
      ZundoOrRefold (undos, true, orig, rev_params) :: s'


  let push_undo (undos, progress, orig, rev_params) (s : stack) =
    let has_OnNoProgress = List.mem Undo.OnNoProgress undos in
    if has_OnNoProgress then
      if progress then s else
      let rec go rev_params (s : stack) =
        match s with
        | (ZcaseT (_, _, _, _, _, _))::_
        | (Zproj (_, _, _))::_
        | (Zfix _)::_
        | (Zprimitive (_, _, _, _))::_
        | (ZundoOrRefold(_)::_)
        | [] -> ZundoOrRefold (undos, progress, orig, rev_params) :: s
        | Zapp _ as z :: s -> z :: go (z :: rev_params) s
        | Zshift _ as z ::s -> z :: go rev_params s (* TODO: can this be correct? *)
        | Zunfold (undo', unf, rev_params') :: s' ->
          if undo' = None then
            Zunfold(Some(undos,orig,rev_params), unf, rev_params') :: s'
          else
            s (* TODO: is it correct to keep oldest undo info?? *)
      in
      go rev_params s
    else
      ZundoOrRefold (undos, progress, orig, rev_params) :: s

  let append_stack v s =
    if Int.equal (Array.length v) 0 then s else
    match s with
    | Zapp l :: s -> Zapp (Array.append v l) :: s
    | (ZcaseT _ | Zproj _ | Zfix _ | Zshift _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _) :: _ | [] ->
      Zapp v :: s

  (* Collapse the shifts in the stack *)
  let zshift n s =
    match (n,s) with
        (0,_) -> s
      | (_,Zshift(k)::s) -> Zshift(n+k)::s
      | (_,(ZcaseT _ | Zproj _ | Zfix _ | Zapp _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _) :: _) | _,[] -> Zshift(n)::s

  let rec stack_args_size = function
    | Zapp v :: s -> Array.length v + stack_args_size s
    | Zshift(_)::s -> stack_args_size s
    | (ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _) :: _ | [] -> 0

  (* The assertions in the functions below are granted because they are
    called only when m is a constructor, a cofix
    (strip_update_shift_app), a fix (get_nth_arg) or an abstraction
    (strip_update_shift, through get_arg). *)

  (* optimised for the case where there are no shifts... *)
  let strip_update_shift_app_red head stk =
    let rec strip_rec rstk h depth = function
      | Zshift(k) as e :: s ->
          strip_rec (e::rstk) (lift_fconstr k h) (depth+k) s
      | (Zapp args :: s) ->
          strip_rec (Zapp args :: rstk) {mark=h.mark;term=FApp(h,args)} depth s
      | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _) :: _ | []) as stk ->
        (depth,List.rev rstk, stk)
    in
    strip_rec [] head 0 stk

  let strip_update_shift_app head stack =
    assert (not (is_red head.mark));
    strip_update_shift_app_red head stack

  let get_nth_arg head n stk =
    assert (not (is_red head.mark));
    let rec strip_rec rstk h n = function
      | Zshift(k) as e :: s ->
          strip_rec (e::rstk) (lift_fconstr k h) n s
      | Zapp args::s' ->
          let q = Array.length args in
          if n >= q
          then
            strip_rec (Zapp args::rstk) {mark=h.mark;term=FApp(h,args)} (n-q) s'
          else
            let bef = Array.sub args 0 n in
            let aft = Array.sub args (n+1) (q-n-1) in
            let stk' =
              List.rev (if Int.equal n 0 then rstk else (Zapp bef :: rstk)) in
            (Some (stk', args.(n)), append_stack aft s')
      | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _) :: _ | []) as s -> (None, List.rev rstk @ s) in
    strip_rec [] head n stk


  (* Beta reduction: look for an applied argument in the stack.
    Since the encountered update marks are removed, h must be a whnf *)
  let get_args =
    let rec get_args rev_args n tys f e = function
        | Zshift k as z :: s ->
            get_args (z :: rev_args) n tys f (usubs_shft (k,e)) s
        | Zapp l as z :: s ->
            let na = Array.length l in
            if n == na then (Inl (z :: rev_args, usubs_consn l 0 na e), s)
            else if n < na then (* more arguments *)
              let eargs = Array.sub l n (na-n) in
              let rev_args = Zapp (Array.sub l 0 n) :: rev_args in
              (Inl (rev_args, usubs_consn l 0 n e), Zapp eargs :: s)
            else (* more lambdas *)
              let etys = List.skipn na tys in
              get_args (z :: rev_args) (n-na) etys f (usubs_consn l 0 na e) s
        | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _) :: _ | []) as stk ->
          (Inr {mark=Cstr; term=FLambda(n,tys,f,e)}, stk)
    in
    get_args []


  let zip ?(dbg=false) m stk =
    let rec zip m stk =
      match stk with
        | [] -> m
        | Zapp args :: s -> zip {mark=neutr m.mark; term=FApp(m, args)} s
        | ZcaseT(ci, u, pms, p, br, e)::s ->
            let t = FCaseT(ci, u, pms, p, m, br, e) in
            let mark = (neutr m.mark) in
            zip {mark; term=t} s
        | Zproj (_, p,r) :: s ->
            let mark = (neutr m.mark) in
            zip {mark; term=FProj(Projection.make p true,r,m)} s
        | Zfix(fx,par)::s ->
            zip fx (par @ append_stack [|m|] s)
        | Zshift(n)::s ->
            zip (lift_fconstr n m) s
        | Zprimitive(_op,c,rargs,kargs)::s ->
          let args = List.rev_append rargs (m::List.map snd kargs) in
          let f = {mark = Red; term = FFlex (ConstKey c)} in
          zip {mark=(neutr m.mark); term = FApp (f, Array.of_list args)} s
        | ZundoOrRefold _ :: stk -> assert dbg; zip m stk
        | Zunfold (_, unf, rev_params) :: stk ->
          assert dbg;
          let open UnfoldDef in
          zip (unf.orig.Original.term) (List.rev_append rev_params (Zapp [|m|] :: stk))
    in
    zip m stk


  (* Get the arguments of a native operator *)
  let rec skip_native_args rargs nargs =
    match nargs with
    | (kd, a) :: nargs' ->
        if kd = CPrimitives.Kwhnf then rargs, nargs
        else skip_native_args (a::rargs) nargs'
    | [] -> rargs, []

  let get_native_args op c stk =
    let kargs = CPrimitives.kind op in
    let rec get_args rnargs kargs args =
      match kargs, args with
      | kd::kargs, a::args -> get_args ((kd,a)::rnargs) kargs args
      | _, _ -> rnargs, kargs, args in
    let rec strip_rec rnargs h depth kargs = function
      | Zshift k :: s ->
        strip_rec (List.map (fun (kd,f) -> kd,lift_fconstr k f) rnargs)
          (lift_fconstr k h) (depth+k) kargs s
      | Zapp args :: s' ->
        begin match get_args rnargs kargs (Array.to_list args) with
          | rnargs, [], [] ->
            (skip_native_args [] (List.rev rnargs), s')
          | rnargs, [], eargs ->
            (skip_native_args [] (List.rev rnargs),
            Zapp (Array.of_list eargs) :: s')
          | rnargs, kargs, _ ->
            strip_rec rnargs {mark = h.mark;term=FApp(h, args)} depth kargs s'
        end
      | (Zprimitive _ | ZcaseT _ | Zproj _ | Zfix _ | Zunfold _ | ZundoOrRefold _) :: _ | [] -> assert false
    in strip_rec [] {mark = Red; term = FFlex(ConstKey c)} 0 kargs stk

  let get_native_args1 op c stk =
    match get_native_args op c stk with
    | ((rargs, (kd,a):: nargs), stk) ->
        assert (kd = CPrimitives.Kwhnf);
        (rargs, a, nargs, stk)
    | _ -> assert false

  let check_native_args op stk =
    let nargs = CPrimitives.arity op in
    let rargs = stack_args_size stk in
    nargs <= rargs


  (* Iota reduction: extract the arguments to be passed to the Case
    branches *)
  let rec reloc_rargs_rec depth = function
    | Zapp args :: s ->
      Zapp (lift_fconstr_vect depth args) :: reloc_rargs_rec depth s
    | Zshift(k)::s -> if Int.equal k depth then s else reloc_rargs_rec (depth-k) s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _) :: _ | []) as stk -> stk

  let reloc_rargs depth stk =
    if Int.equal depth 0 then stk else reloc_rargs_rec depth stk

  let rec try_drop_parameters depth n = function
      | Zapp args::s ->
          let q = Array.length args in
          if n > q then try_drop_parameters depth (n-q) s
          else if Int.equal n q then reloc_rargs depth s
          else
            let aft = Array.sub args n (q-n) in
            reloc_rargs depth (append_stack aft s)
      | Zshift(k)::s -> try_drop_parameters (depth-k) n s
      | [] ->
          if Int.equal n 0 then []
          else raise Not_found
      | (ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _) :: _ -> assert false
          (* strip_update_shift_app only produces Zapp and Zshift items *)

  let drop_parameters depth n argstk =
    try try_drop_parameters depth n argstk
    with Not_found ->
    (* we know that n < stack_args_size(argstk) (if well-typed term) *)
    anomaly (Pp.str "ill-typed term: found a match on a partially applied constructor.")

  let rec foldl_applicative_assert f s acc =
    match [@ocaml.warning "-4"] s with
    | [] -> acc
    | Zapp vs :: s -> foldl_applicative_assert f s (f vs acc)
    | _ -> assert false

  let rec project_nth_arg n = function
    | Zapp args :: s ->
        let q = Array.length args in
          if n >= q then project_nth_arg (n - q) s
          else (* n < q *) args.(n)
    | (ZcaseT _ | Zproj _ | Zfix _ | Zshift _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _) :: _ | [] -> assert false
        (* After drop_parameters we have a purely applicative stack *)

  let rec skip_irrelevant_stack info stk = match stk with
  | [] -> []
  | (Zshift _ | Zapp _) :: s -> skip_irrelevant_stack info s
  | (Zfix _ | Zproj _) :: s ->
    (* Typing rules ensure that fix / proj over SProp is irrelevant *)
    skip_irrelevant_stack info s
  | ZcaseT (_, _, _, (_,r), _, e) :: s ->
    let r = usubst_relevance e r in
    if is_irrelevant info r then skip_irrelevant_stack info s
    else stk
  | Zprimitive _ :: _ -> assert false (* no irrelevant primitives so far *)
  | (Zunfold _ | ZundoOrRefold _) :: s -> skip_irrelevant_stack info s (* irrelevant terms are not matches or fixes *)

  let strip_shift_app_undo ~is_matchfix (m:fconstr) (stk : stack)
      ~(abort:fconstr * stack -> 'a)
      (f : cont:(unit -> 'a) -> depth:int -> cargs:(unit -> stack) -> stack -> 'a) : 'a =
    let rec go depth rev_undo stk =
      let (new_depth, new_cargs, s) = strip_update_shift_app m stk in
      let depth = depth + new_depth in
      let cargs () =
        List.rev_append (List.concat_map (fun (args,_) -> args) rev_undo) new_cargs
      in
      match [@ocaml.warning "-4"] s with
      | (ZundoOrRefold (undos, prog, orig, rev_params) :: stk) ->
        let undo = (undos,prog,orig,rev_params) in
        go depth ((new_cargs,undo) :: rev_undo) stk
      | (_ as s) ->
        let cont () =
          let undos = List.rev rev_undo in
          let rec go_undo undos prog_acc args_acc m s =
            match undos with
            | [] ->
              let cargs () = args_acc @ new_cargs in
              f ~cont:(fun () -> abort (m,cargs()@s)) ~depth ~cargs s
            | (args,(undo,prog,orig,rev_params)) :: undos ->
              let prog_acc = prog_acc || prog in
              if (not prog_acc && List.mem Undo.OnNoProgress undo)
              || (is_matchfix && List.mem Undo.OnMatchFix undo)
              then
                let s = (List.map_append (fun (args,(u,p,o,rp)) -> args@[ZundoOrRefold (u,p,o,rp)]) undos) @ s in
                let s = if prog_acc then push_progress s else s in
                abort (orig.Original.term, List.rev_append rev_params s)
              else
                (* We keep [ZundoOrRefold] around to allow refolding later on *)
                let undo = Undo.remove_OnMatchFix undo in
                let undo = if prog_acc then Undo.remove_OnNoProgress undo else undo in
                assert (undo = []);
                go_undo undos prog_acc (args_acc @ args @ [ZundoOrRefold (undo,prog_acc,orig,rev_params)]) m s
          in
          go_undo undos false [] m s
        in
        f ~cont ~depth ~cargs s
    in
    go 0 [] stk
end

open Stack

(************************************************************************)

type table_val = (fconstr * gfix_info option, Empty.t, UVars.Instance.t * bool * rewrite_rule list) constant_def

module Table : sig
  type t
  val create : unit -> t
  val lookup : clos_infos -> t -> table_key -> table_val
end = struct
  module Table = Hashtbl.Make(struct
    type t = table_key
    let equal = eq_table_key (eq_pair eq_constant_key UVars.Instance.equal)
    let hash = hash_table_key (fun (c, _) -> Constant.UserOrd.hash c)
  end)

  type t = table_val Table.t

  let create () = Table.create 17

  exception Irrelevant

  let shortcut_irrelevant info r =
    if is_irrelevant info r then raise Irrelevant

  let assoc_defined d =
    match d with
    | NamedDecl.LocalDef (_, c, _) -> inject c
    | NamedDecl.LocalAssum (_, _) -> raise Not_found

  let constant_value_in u = function
    | Def b -> b
    | OpaqueDef _ -> raise (NotEvaluableConst Opaque)
    | Undef _ -> raise (NotEvaluableConst NoBody)
    | Primitive p -> raise (NotEvaluableConst (IsPrimitive (u,p)))
    | Symbol _ -> assert false
    (*  Should already be dealt with *)

  let replace_name_by_id env cst name =
    if not (Names.Name.is_name name) then Result.Error () else
    let id =
      match name with
      | Names.Name.Name n -> n
      | Names.Name.Anonymous -> assert false
    in
    (* we take the constant from the one entry that is definitely known *)
    let cst = Constant.change_label cst (Names.Label.of_id id) in
    if Environ.mem_constant cst env then Result.Ok cst else
    Result.error ()

  type fix_or_cofix =
  | FOCFix of fixpoint
  | FOCCoFix of cofixpoint

  let foc_names = function
  | FOCFix ((_, _), (names,_,_)) -> names
  | FOCCoFix (_, (names, _,_ )) -> names

  let rec maybe_expand_mutual_fixpoints
      (info : clos_infos)
      (tab : t)
      (cst, univ)
      (inst : UVars.Instance.t)
      (foc : fix_or_cofix)
      nargs args j =
    let name = (foc_names foc).(j).Context.binder_name in
    Result.bind (replace_name_by_id (info_env info) cst name) @@ fun cst ->
    let info = { info with i_flags = (RedFlags.red_add_transparent info.i_flags TransparentState.full) } in
    match [@ocaml.warning "-4"] lookup info tab (ConstKey (cst, univ)) with
    | Def (m, _) ->
      begin
        match [@ocaml.warning "-4"] m.term with
        | FCLOS (c, env) ->
          if not (Esubst.is_subs_id (fst env)) then Result.Error () else
          let ctx, body = Term.decompose_lambda c in
          if List.length ctx <> nargs then Result.Error () else
            begin
            match foc, Constr.kind body with
            | FOCFix ((rdcl,_),(names,types,bodies)),
              Fix ((rdcl', j'), (names',types',bodies')) ->
                if
                  j' = j &&
                  rdcl' = rdcl &&
                  names' = names &&
                  (Array.equal Constr.equal types' types) &&
                  (Array.equal Constr.equal bodies' bodies)
                then
                  Result.Ok (mkApp (mkConstU (cst, inst), args))
                else
                  Result.Error ()
            | FOCCoFix (_, (names,types,bodies)),
              CoFix (j', (names',types',bodies')) ->
                if
                  j' = j &&
                  names' = names &&
                  (Array.equal Constr.equal types' types) &&
                  (Array.equal Constr.equal bodies' bodies)
                then
                  Result.Ok (mkApp (mkConstU (cst, inst), args))
                else
                  Result.Error ()
            | _, _ -> Result.Error ()
          end
        | _ -> Result.Error ()
      end
    | _ -> Result.Error ()


  and expand_global_fixpoint info tab cst c =
    let ctx, body = Term.decompose_lambda c in
    match [@ocaml.warning "-4"] kind body with
    | Fix (((rd,i),_) as fix) ->
      let nargs = List.length ctx in
      let args = Array.init nargs (fun i -> mkRel (nargs - i)) in
      let inst = UVars.Instance.abstract_instance @@ UVars.Instance.length @@ snd cst in
      let refold = Array.init (Array.length rd) (fun j ->
          if i = j then
            lazy (Result.Ok (mkApp (mkConstU (fst cst, inst), args)))
          else
            lazy (maybe_expand_mutual_fixpoints info tab cst inst (FOCFix fix) nargs args j)
        )
      in
      Some (GFixInfo {
        gfix_nargs = nargs;
        gfix_tys = List.rev ctx;
        gfix_univs = snd cst;
        gfix_body = fix;
        gfix_refold = refold;
      })
    | CoFix ((i, (names, _, _)) as cofix) ->
      let nargs = List.length ctx in
      let args = Array.init nargs (fun i -> mkRel (nargs - i)) in
      let inst = UVars.Instance.abstract_instance @@ UVars.Instance.length @@ snd cst in
      let refold = Array.init (Array.length names) (fun j ->
          if i = j then
            lazy (Result.Ok (mkApp (mkConstU (fst cst, inst), args)))
          else
            lazy (maybe_expand_mutual_fixpoints info tab cst inst (FOCCoFix cofix) nargs args j)
        )
      in
      Some (GCoFixInfo {
        gfix_nargs = nargs;
        gfix_tys = List.rev ctx;
        gfix_univs = snd cst;
        gfix_body = cofix;
        gfix_refold = refold;
      })
    | _ -> None

  and value_of info tab ref =
    try
      let env = info.i_cache.i_env in
      match ref with
      | RelKey n ->
        let i = n - 1 in
        let d =
          try Range.get env.env_rel_context.env_rel_map i
          with Invalid_argument _ -> raise Not_found
        in
        shortcut_irrelevant info (RelDecl.get_relevance d);
        let body =
          match d with
          | RelDecl.LocalAssum _ -> raise Not_found
          | RelDecl.LocalDef (_, t, _) -> lift n t
        in
        Def (inject body, None)
      | VarKey id ->
        let def = Environ.lookup_named id env in
        shortcut_irrelevant info
          (binder_relevance (NamedDecl.get_annot def));
        let ts = RedFlags.red_transparent info.i_flags in
        if TransparentState.is_transparent_variable ts id then
          Def (assoc_defined def, None)
        else
          raise Not_found
      | ConstKey (cst,u) ->
        let cb = lookup_constant cst env in
        shortcut_irrelevant info (UVars.subst_instance_relevance u cb.const_relevance);
        let ts = RedFlags.red_transparent info.i_flags in
        if TransparentState.is_transparent_constant ts cst then match cb.const_body with
        | Undef _ | Def _ | OpaqueDef _ | Primitive _ ->
          let body = constant_value_in u cb.const_body in
          let gfix = expand_global_fixpoint info tab (cst, u) body in
          Def (injectu body u, gfix)
        | Symbol b ->
          let r = Cmap_env.get cst env.symb_pats in
          raise (NotEvaluableConst (HasRules (u, b, r)))
        else
          raise Not_found
    with
    | Irrelevant -> Def (mk_irrelevant, None)
    | NotEvaluableConst (IsPrimitive (_u,op)) (* Const *) -> Primitive op
    | NotEvaluableConst (HasRules (u, b, r)) -> Symbol (u, b, r)
    | Not_found (* List.assoc *)
    | NotEvaluableConst _ (* Const *) -> Undef None

  and lookup info tab ref =
    try Table.find tab ref with Not_found ->
    let v = value_of info tab ref in
    Table.add tab ref v; v
end

type clos_tab = Table.t

let create_tab = Table.create

(************************************************************************)

(** Hand-unrolling of the map function to bypass the call to the generic array
    allocation *)
let mk_clos_vect env v = match v with
| [||] -> [||]
| [|v0|] -> [|mk_clos env v0|]
| [|v0; v1|] -> [|mk_clos env v0; mk_clos env v1|]
| [|v0; v1; v2|] -> [|mk_clos env v0; mk_clos env v1; mk_clos env v2|]
| [|v0; v1; v2; v3|] ->
  [|mk_clos env v0; mk_clos env v1; mk_clos env v2; mk_clos env v3|]
| v -> Array.Fun1.map mk_clos env v

let rec subst_constr (subst,usubst as e) c =
  let c = Vars.map_constr_relevance (usubst_relevance e) c in
  match [@ocaml.warning "-4"] Constr.kind c with
| Rel i ->
  begin match expand_rel i subst with
  | Inl (k, lazy v) -> Vars.lift k v
  | Inr (m, _) -> mkRel m
  end
| Const _ | Ind _ | Construct _ | Sort _ -> subst_instance_constr usubst c
| Case (ci, u, pms, p, iv, discr, br) ->
  let u' = usubst_instance e u in
  let c = if u == u' then c else mkCase (ci, u', pms, p, iv, discr, br) in
  Constr.map_with_binders usubs_lift subst_constr e c
| Array (u,elems,def,ty) ->
  let u' = usubst_instance e u in
  let c = if u == u' then c else mkArray (u',elems,def,ty) in
  Constr.map_with_binders usubs_lift subst_constr e c
| _ ->
  Constr.map_with_binders usubs_lift subst_constr e c

let subst_context e ctx =
  let open Context.Rel.Declaration in
  let rec subst_context ctx = match ctx with
  | [] -> e, []
  | LocalAssum (na, ty) :: ctx ->
    let e, ctx = subst_context ctx in
    let ty = subst_constr e ty in
    usubs_lift e, LocalAssum (na, ty) :: ctx
  | LocalDef (na, ty, bdy) :: ctx ->
    let e, ctx = subst_context ctx in
    let ty = subst_constr e ty in
    let bdy = subst_constr e bdy in
    usubs_lift e, LocalDef (na, ty, bdy) :: ctx
  in
  snd @@ subst_context ctx

(* The inverse of mk_clos: move back to constr *)
(* XXX should there be universes in lfts???? *)
let rec to_constr (lfts, usubst as ulfts) v =
  let subst_us c = subst_instance_constr usubst c in
  match v.term with
    | FRel i -> mkRel (reloc_rel i lfts)
    | FFlex (RelKey p) -> mkRel (reloc_rel p lfts)
    | FFlex (VarKey x) -> mkVar x
    | FAtom c -> subst_us (exliftn lfts c)
    | FFlex (ConstKey op) -> subst_us (mkConstU op)
    | FInd op -> subst_us (mkIndU op)
    | FConstruct op -> subst_us (mkConstructU op)
    | FCaseT (ci, u, pms, p, c, ve, env) ->
      to_constr_case ulfts ci u pms p NoInvert c ve env
    | FCaseInvert (ci, u, pms, p, indices, c, ve, env) ->
      let iv = CaseInvert {indices=Array.Fun1.map to_constr ulfts indices} in
      to_constr_case ulfts ci u pms p iv c ve env
    | FFix ((op,(lna,tys,bds)) as fx, e, _, _) ->
      if is_subs_id (fst e) && is_lift_id lfts then
        subst_instance_constr (usubst_instance ulfts (snd e)) (mkFix fx)
      else
        let n = Array.length bds in
        let subs_ty = comp_subs ulfts e in
        let subs_bd = comp_subs (on_fst (el_liftn n) ulfts) (on_fst (subs_liftn n) e) in
        let lna = Array.Fun1.map usubst_binder subs_ty lna in
        let tys = Array.Fun1.map subst_constr subs_ty tys in
        let bds = Array.Fun1.map subst_constr subs_bd bds in
        mkFix (op, (lna, tys, bds))
    | FCoFix ((op,(lna,tys,bds)) as cfx, e, _) ->
      if is_subs_id (fst e) && is_lift_id lfts then
        subst_instance_constr (usubst_instance ulfts (snd e)) (mkCoFix cfx)
      else
        let n = Array.length bds in
        let subs_ty = comp_subs ulfts e in
        let subs_bd = comp_subs (on_fst (el_liftn n) ulfts) (on_fst (subs_liftn n) e) in
        let lna = Array.Fun1.map usubst_binder subs_ty lna in
        let tys = Array.Fun1.map subst_constr subs_ty tys in
        let bds = Array.Fun1.map subst_constr subs_bd bds in
        mkCoFix (op, (lna, tys, bds))
    | FApp (f,ve) ->
        mkApp (to_constr ulfts f,
               Array.Fun1.map to_constr ulfts ve)
    | FProj (p,r,c) ->
        mkProj (p,usubst_relevance ulfts r,to_constr ulfts c)

    | FLambda (len, tys, f, e) ->
      if is_subs_id (fst e) && is_lift_id lfts then
        subst_instance_constr (usubst_instance ulfts (snd e)) (Term.compose_lam (List.rev tys) f)
      else
        let subs = comp_subs ulfts e in
        let tys = List.mapi (fun i (na, c) ->
            usubst_binder subs na, subst_constr (usubs_liftn i subs) c)
            tys
        in
        let f = subst_constr (usubs_liftn len subs) f in
        Term.compose_lam (List.rev tys) f
    | FProd (n, t, c, e) ->
      if is_subs_id (fst e) && is_lift_id lfts then
        mkProd (n, to_constr ulfts t, subst_instance_constr (usubst_instance ulfts (snd e)) c)
      else
        let subs' = comp_subs ulfts e in
        mkProd (usubst_binder subs' n,
                to_constr ulfts t,
                subst_constr (usubs_lift subs') c)
    | FLetIn (n,b,t,f,e) ->
      let subs = comp_subs (on_fst el_lift ulfts) (usubs_lift e) in
      mkLetIn (usubst_binder subs n,
               to_constr ulfts b,
               to_constr ulfts t,
               subst_constr subs f)
    | FEvar (ev, args, env, repack) ->
      let subs = comp_subs ulfts env in
      repack (ev, List.map (fun a -> subst_constr subs a) args)
    | FLIFT (k,a) -> to_constr (el_shft k lfts, usubst) a

    | FInt i ->
       Constr.mkInt i
    | FFloat f ->
        Constr.mkFloat f
    | FString s ->
        Constr.mkString s

    | FArray (u,t,ty) ->
      let u = usubst_instance ((),usubst) u in
      let def = to_constr ulfts (Parray.default t) in
      let t = Array.init (Parray.length_int t) (fun i ->
          to_constr ulfts (Parray.get t (Uint63.of_int i)))
      in
      let ty = to_constr ulfts ty in
      mkArray(u, t, def,ty)

    | FCLOS (t,env) ->
      if is_subs_id (fst env) && is_lift_id lfts then
        subst_instance_constr (usubst_instance ulfts (snd env)) t
      else
        let subs = comp_subs ulfts env in
        subst_constr subs t

    | FIrrelevant -> assert (!Flags.in_debugger); mkVar(Id.of_string"_IRRELEVANT_")

and to_constr_case (lfts,_ as ulfts) ci u pms (p,r) iv c ve env =
  let subs = comp_subs ulfts env in
  let r = usubst_relevance subs r in
  if is_subs_id (fst env) && is_lift_id lfts then
    mkCase (ci, usubst_instance subs u, pms, (p,r), iv, to_constr ulfts c, ve)
  else
    let f_ctx (nas, c) =
      let nas = Array.map (usubst_binder subs) nas in
      let c = subst_constr (usubs_liftn (Array.length nas) subs) c in
      (nas, c)
    in
    mkCase (ci,
            usubst_instance subs u,
            Array.map (fun c -> subst_constr subs c) pms,
            (f_ctx p,r),
            iv,
            to_constr ulfts c,
            Array.map f_ctx ve)

and comp_subs (el,u) (s,u') =
  Esubst.lift_subst (fun el c -> lazy (to_constr (el,u) c)) el s, u'

(* This function defines the correspondence between constr and
   fconstr. When we find a closure whose substitution is the identity,
   then we directly return the constr to avoid possibly huge
   reallocation. *)
let term_of_fconstr c = to_constr (el_id, UVars.Instance.empty) c

let subst_context env ctx =
  if is_subs_id (fst env) then
    subst_instance_context (snd env) ctx
  else
    let subs = comp_subs (el_id, UVars.Instance.empty) env in
    subst_context subs ctx

let it_mkLambda_or_LetIn ctx t =
  let open Context.Rel.Declaration in
  match List.rev ctx with
  | [] -> t
  | LocalAssum (n, ty) :: ctx ->
      let assums, ctx = List.map_until (function LocalAssum (n, ty) -> Some (n, ty) | LocalDef _ -> None) ctx in
      let assums = (n, ty) :: assums in
      { term = FLambda(List.length assums, assums, Term.it_mkLambda_or_LetIn (term_of_fconstr t) (List.rev ctx), (subs_id 0, UVars.Instance.empty)); mark = t.mark }
  | LocalDef _ :: _ ->
      mk_clos (subs_id 0, UVars.Instance.empty) (Term.it_mkLambda_or_LetIn (term_of_fconstr t) ctx)



module Dbg = struct
  open Pp

  let rec pp_fconstr env fc =
    hov 2 (str "{" ++ pp_mark fc.mark ++ str "; " ++ pp_fterm env fc.term ++ str "}")
  and pp_mark mark =
    match mark with
    | Cstr -> str "Cstr"
    | Ntrl -> str "Ntrl"
    | Red -> str "Red"         (* extra space for alignment *)
  and pp_fterm env (ft : fterm) =
    hov 2
      (match ft with
       | FRel r -> str "F#" ++ int r
       | FAtom c -> Constr.debug_print c
       | FFlex k -> str "FFlex" ++ pp_key env k
       | FInd (ind, _univ) -> str "FInd(" ++ int (snd ind) ++ str ")"
       | FConstruct (cstr, _univ) -> str "FConstruct(" ++ int (snd (fst cstr)) ++ str "," ++ int (snd cstr)  ++ str ")"
       | FApp (h, args) -> str "FApp(" ++ pp_fconstr env h ++ str "," ++ pp_fconstr_arr env args ++ str ")"
       | FProj (_, _, _) -> str "<FProj>"
       | FFix(_) -> str "<FFix>"
       | FCoFix(_) -> str "<FCoFix>"
       | FCaseT (_, _, _, _, _, _, _) -> str "<FCaseT>"
       | FCaseInvert (_, _, _, _, _, _, _, _) -> str "<FCaseInvert>"
       | FLambda (_, _, _, _) -> str "<FLambda>"
       | FProd (_, _, _, _) -> str "<FProd>"
       | FLetIn (_, _, _, _, _) -> str "<FLetIn>"
       | FEvar (_, _, _, _) -> str "<FEvar>"
       | FInt _ -> str "<FInt>"
       | FFloat _ -> str "<FFloat>"
       | FString _ -> str "<FString>"
       | FArray (_, _, _) -> str "<FArray>"
       | FLIFT (_, _) -> str "<FLIFT>"
       | FCLOS _ -> str "FCLOS(" ++ Constr.debug_print (term_of_fconstr { mark = Ntrl; term = ft }) ++ str ")";
       | FIrrelevant -> str "<FIRR>"
    )
  and pp_fconstr_arr env fcs =
    hov 2 (
    str "[|" ++
    prlist_with_sep
      (fun () -> str ";")
      (pp_fconstr env)
      (Array.to_list fcs) ++
    str "|]")
  and pp_key _ (k : _ Names.tableKey) =
    match[@ocaml.warning "-4"] k with
    | Names.ConstKey (c, _) -> str (Names.Constant.debug_to_string c)
    | _ -> str "<OtherKey>"

  let rec pp_stack env stk =
    hov 2 (str "[" ++ prlist_with_sep (fun () -> str ",") (pp_stack_member env) stk ++ str "]")
  and pp_stack_member env s =
    let open Stack in
    match s with
    | Zapp args -> str "Zapp(" ++ pp_fconstr_arr env args ++ str ")"
    | ZcaseT (_, _, _, _, _, _) -> str "ZcaseT(_)"
    | Zproj (unf,_, _) -> str "Zproj(" ++ UnfoldProj.pp unf ++ str ",_,_)"
    | Zfix _ -> str "Zfix(_)"
    | Zprimitive (_, _, _, _) -> str "Zprim(_)"
    | Zshift _ -> str "Zshift(_)"
    | Zunfold (undo, unf, _) -> str "Zunfold(" ++ pr_opt_default (fun () -> str "None") (fun (u, _,_) -> prlist_with_sep (fun () -> str ",") Undo.pp u) (undo) ++ str "," ++ UnfoldDef.pp unf ++ str ",_)"
    | ZundoOrRefold (undo, prog, orig, _) -> str "ZundoOrRefold(" ++ prlist_with_sep (fun () -> str ",") Undo.pp undo ++ str "," ++ bool prog ++ str "," ++ pp_fconstr env (orig.Original.term) ++ str ",_" ++ str ")"

  let dbg = CDebug.create ~name:"kred" ()
end



(*********************************************************************)


let inductive_subst mib u pms =
  let rec mk_pms i ctx = match ctx with
  | [] -> subs_id 0
  | RelDecl.LocalAssum _ :: ctx ->
    let subs = mk_pms (i - 1) ctx in
    subs_cons pms.(i) subs
  | RelDecl.LocalDef (_, c, _) :: ctx ->
    let subs = mk_pms i ctx in
    subs_cons (mk_clos (subs,u) c) subs
  in
  mk_pms (Array.length pms - 1) mib.mind_params_ctxt, u

(* Iota-reduction: feed the arguments of the constructor to the branch *)
let get_branch infos depth ci pms ((ind, c), u) br e args =
  let i = c - 1 in
  let args = drop_parameters depth ci.ci_npar args in
  let (_nas, br) = br.(i) in
  if Int.equal ci.ci_cstr_ndecls.(i) ci.ci_cstr_nargs.(i) then
    (* No let-bindings in the constructor, we don't have to fetch the
      environment to know the value of the branch. *)
    let e = foldl_applicative_assert usubs_consv args e in
    (br, e)
  else
    (* The constructor contains let-bindings, but they are not physically
        present in the match, so we fetch them in the environment. *)
    let env = info_env infos in
    let mib = Environ.lookup_mind (fst ind) env in
    let mip = mib.mind_packets.(snd ind) in
    let (ctx, _) = mip.mind_nf_lc.(i) in
    let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
    let map = function
    | Zapp args -> args
    | Zshift _ | ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _ | Zunfold _ | ZundoOrRefold _ ->
      assert false
    in
    let ind_subst = inductive_subst mib u (Array.map (mk_clos e) pms) in
    let args = Array.concat (List.map map args) in
    let rec push i e = function
    | [] -> []
    | RelDecl.LocalAssum _ :: ctx ->
      let ans = push (pred i) e ctx in
      args.(i) :: ans
    | RelDecl.LocalDef (_, b, _) :: ctx ->
      let ans = push i e ctx in
      let b = subst_instance_constr u b in
      let s = Array.rev_of_list ans in
      let e = usubs_consv s ind_subst in
      let v = mk_clos e b in
      v :: ans
    in
    let ext = push (Array.length args - 1) [] ctx in
    (br, usubs_consv (Array.rev_of_list ext) e)

(* Iota reduction: expansion of a fixpoint.
 * Given a fixpoint and a substitution, returns the corresponding
 * fixpoint body, and the substitution in which it should be
 * evaluated: its first variables are the fixpoint bodies
 *
 * FCLOS(fix Fi {F0 := T0 .. Fn-1 := Tn-1}, S)
 *    -> (S. FCLOS(F0,S) . ... . FCLOS(Fn-1,S), Ti)
 *)
(* does not deal with FLIFT *)
let contract_fix_vect fix =
  let (thisbody, make_body, env, nfix) =
    match [@ocaml.warning "-4"] fix with
      | FFix (((reci,i),(_,_,bds as rdcl)),env, must_unfold, (Some refold as rf)) ->
          (bds.(i),
           (fun j ->
              let lazy r = refold.(j) in
              match r with
              | Result.Ok t ->
                { mark = Cstr; term = FCLOS (t, env) }
              | Result.Error () ->
                  { mark = Cstr;
                       term = FFix (((reci,j),rdcl),env, must_unfold, rf) }),
           env, Array.length bds)
      | FFix (((reci,i),(_,_,bds as rdcl)),env, must_unfold, None) ->
          (bds.(i),
           (fun j -> { mark = Cstr;
                       term = FFix (((reci,j),rdcl),env, must_unfold, None) }),
           env, Array.length bds)

      | FCoFix ((i,(_,_,bds as rdcl)),env, (Some refold as rf)) ->
          (bds.(i),
           (fun j ->
              let lazy r = refold.(j) in
              match r with
              | Result.Ok t ->
                { mark = Cstr; term = FCLOS (t, env) }
              | Result.Error () ->
                { mark = Cstr;
                  term = FCoFix ((j,rdcl),env, rf) }),
           env, Array.length bds)
      | FCoFix ((i,(_,_,bds as rdcl)),env, None) ->
          (bds.(i),
           (fun j -> { mark = Cstr;
                       term = FCoFix ((j,rdcl),env,None) }),
           env, Array.length bds)

      | _ -> assert false
  in
  let rec mk_subs env i =
    if Int.equal i nfix then env
    else mk_subs (subs_cons (make_body i) env) (i + 1)
  in
  (on_fst (fun env -> mk_subs env 0) env, thisbody)

let unfold_projection info term body p r =
  let module R = Reductionops.ReductionBehaviour in
  if red_projection info.i_flags p
  then
    let open UnfoldProj in
    match R.get (Names.Projection.constant p) with
    | Some R.NeverUnfold -> None
    | Some ((R.UnfoldWhenNoMatch flags | R.UnfoldWhen flags) as u) ->
      let undo =
        (* TODO: handle / correctly *)
        match[@ocaml.warning "-4"] flags.R.nargs, u with
        | None, UnfoldWhenNoMatch _ -> [Undo.OnNoProgress; Undo.OnMatchFix]
        | None, _ -> [Undo.OnNoProgress]
        | Some _, UnfoldWhenNoMatch _ -> [Undo.OnMatchFix]
        | Some _, UnfoldWhen _ -> []
        | Some _, _ -> assert false
      in
      Some (Zproj ({orig=Original.{term; body}; undo}, Projection.repr p, r))
    | None ->
      let undo = [Undo.OnNoProgress] in
      Some (Zproj ({orig=Original.{term; body}; undo}, Projection.repr p, r))
  else None

(************************************************************************)
(* Reduction of Native operators                                        *)

open Primred

module FNativeEntries =
  struct
    type elem = fconstr
    type args = fconstr array
    type evd = unit
    type uinstance = UVars.Instance.t

    let mk_construct c =
      (* All constructors used in primitive functions are relevant *)
      { mark = Cstr; term = FConstruct (UVars.in_punivs c) }

    let get = Array.get

    let get_int () e =
      match [@ocaml.warning "-4"] e.term with
      | FInt i -> i
      | _ -> assert false

    let get_float () e =
      match [@ocaml.warning "-4"] e.term with
      | FFloat f -> f
      | _ -> assert false

    let get_string () e =
      match [@ocaml.warning "-4"] e.term with
      | FString s -> s
      | _ -> assert false

    let get_parray () e =
      match [@ocaml.warning "-4"] e.term with
      | FArray (_u,t,_ty) -> t
      | _ -> assert false

    let dummy = {mark = Ntrl; term = FRel 0}

    let current_retro = ref Retroknowledge.empty
    let defined_int = ref false
    let fint = ref dummy

    let init_int retro =
      match retro.Retroknowledge.retro_int63 with
      | Some c ->
        defined_int := true;
        fint := { mark = Ntrl; term = FFlex (ConstKey (UVars.in_punivs c)) }
      | None -> defined_int := false

    let defined_float = ref false
    let ffloat = ref dummy

    let init_float retro =
      match retro.Retroknowledge.retro_float64 with
      | Some c ->
        defined_float := true;
        ffloat := { mark = Ntrl; term = FFlex (ConstKey (UVars.in_punivs c)) }
      | None -> defined_float := false

    let defined_string = ref false
    let fstring = ref dummy

    let init_string retro =
      match retro.Retroknowledge.retro_string with
      | Some c ->
        defined_string := true;
        fstring := { mark = Ntrl; term = FFlex (ConstKey (UVars.in_punivs c)) }
      | None -> defined_string := false

    let defined_bool = ref false
    let ftrue = ref dummy
    let ffalse = ref dummy

    let init_bool retro =
      match retro.Retroknowledge.retro_bool with
      | Some (ct,cf) ->
        defined_bool := true;
        ftrue := mk_construct ct;
        ffalse := mk_construct cf;
      | None -> defined_bool :=false

    let defined_carry = ref false
    let fC0 = ref dummy
    let fC1 = ref dummy

    let init_carry retro =
      match retro.Retroknowledge.retro_carry with
      | Some(c0,c1) ->
        defined_carry := true;
        fC0 := mk_construct c0;
        fC1 := mk_construct c1;
      | None -> defined_carry := false

    let defined_pair = ref false
    let fPair = ref dummy

    let init_pair retro =
      match retro.Retroknowledge.retro_pair with
      | Some c ->
        defined_pair := true;
        fPair := mk_construct c;
      | None -> defined_pair := false

    let defined_cmp = ref false
    let fEq = ref dummy
    let fLt = ref dummy
    let fGt = ref dummy
    let fcmp = ref dummy

    let init_cmp retro =
      match retro.Retroknowledge.retro_cmp with
      | Some (cEq, cLt, cGt) ->
        defined_cmp := true;
        fEq := mk_construct cEq;
        fLt := mk_construct cLt;
        fGt := mk_construct cGt;
        let (icmp, _) = cEq in
        fcmp := { mark = Ntrl; term = FInd (UVars.in_punivs icmp) }
      | None -> defined_cmp := false

    let defined_f_cmp = ref false
    let fFEq = ref dummy
    let fFLt = ref dummy
    let fFGt = ref dummy
    let fFNotComparable = ref dummy

    let init_f_cmp retro =
      match retro.Retroknowledge.retro_f_cmp with
      | Some (cFEq, cFLt, cFGt, cFNotComparable) ->
        defined_f_cmp := true;
        fFEq := mk_construct cFEq;
        fFLt := mk_construct cFLt;
        fFGt := mk_construct cFGt;
        fFNotComparable := mk_construct cFNotComparable;
      | None -> defined_f_cmp := false

    let defined_f_class = ref false
    let fPNormal = ref dummy
    let fNNormal = ref dummy
    let fPSubn = ref dummy
    let fNSubn = ref dummy
    let fPZero = ref dummy
    let fNZero = ref dummy
    let fPInf = ref dummy
    let fNInf = ref dummy
    let fNaN = ref dummy

    let init_f_class retro =
      match retro.Retroknowledge.retro_f_class with
      | Some (cPNormal, cNNormal, cPSubn, cNSubn, cPZero, cNZero,
              cPInf, cNInf, cNaN) ->
        defined_f_class := true;
        fPNormal := mk_construct cPNormal;
        fNNormal := mk_construct cNNormal;
        fPSubn := mk_construct cPSubn;
        fNSubn := mk_construct cNSubn;
        fPZero := mk_construct cPZero;
        fNZero := mk_construct cNZero;
        fPInf := mk_construct cPInf;
        fNInf := mk_construct cNInf;
        fNaN := mk_construct cNaN;
      | None -> defined_f_class := false

    let defined_array = ref false

    let init_array retro =
      defined_array := Option.has_some retro.Retroknowledge.retro_array

    let init env =
      current_retro := env.retroknowledge;
      init_int !current_retro;
      init_float !current_retro;
      init_string !current_retro;
      init_bool !current_retro;
      init_carry !current_retro;
      init_pair !current_retro;
      init_cmp !current_retro;
      init_f_cmp !current_retro;
      init_f_class !current_retro;
      init_array !current_retro

    let check_env env =
      if not (!current_retro == env.retroknowledge) then init env

    let check_int env =
      check_env env;
      assert (!defined_int)

    let check_float env =
      check_env env;
      assert (!defined_float)

    let check_string env =
      check_env env;
      assert (!defined_string)

    let check_bool env =
      check_env env;
      assert (!defined_bool)

    let check_carry env =
      check_env env;
      assert (!defined_carry && !defined_int)

    let check_pair env =
      check_env env;
      assert (!defined_pair && !defined_int)

    let check_cmp env =
      check_env env;
      assert (!defined_cmp)

    let check_f_cmp env =
      check_env env;
      assert (!defined_f_cmp)

    let check_f_class env =
      check_env env;
      assert (!defined_f_class)

    let check_array env =
      check_env env;
      assert (!defined_array)

    let mkInt env i =
      check_int env;
      { mark = Cstr; term = FInt i }

    let mkFloat env f =
      check_float env;
      { mark = Cstr; term = FFloat f }

    let mkString env s =
      check_string env;
      { mark = Cstr; term = FString s }

    let mkBool env b =
      check_bool env;
      if b then !ftrue else !ffalse

    let mkCarry env b e =
      check_carry env;
      {mark = Cstr;
       term = FApp ((if b then !fC1 else !fC0),[|!fint;e|])}

    let mkIntPair env e1 e2 =
      check_pair env;
      { mark = Cstr; term = FApp(!fPair, [|!fint;!fint;e1;e2|]) }

    let mkFloatIntPair env f i =
      check_pair env;
      check_float env;
      { mark = Cstr; term = FApp(!fPair, [|!ffloat;!fint;f;i|]) }

    let mkLt env =
      check_cmp env;
      !fLt

    let mkEq env =
      check_cmp env;
      !fEq

    let mkGt env =
      check_cmp env;
      !fGt

    let mkFLt env =
      check_f_cmp env;
      !fFLt

    let mkFEq env =
      check_f_cmp env;
      !fFEq

    let mkFGt env =
      check_f_cmp env;
      !fFGt

    let mkFNotComparable env =
      check_f_cmp env;
      !fFNotComparable

    let mkPNormal env =
      check_f_class env;
      !fPNormal

    let mkNNormal env =
      check_f_class env;
      !fNNormal

    let mkPSubn env =
      check_f_class env;
      !fPSubn

    let mkNSubn env =
      check_f_class env;
      !fNSubn

    let mkPZero env =
      check_f_class env;
      !fPZero

    let mkNZero env =
      check_f_class env;
      !fNZero

    let mkPInf env =
      check_f_class env;
      !fPInf

    let mkNInf env =
      check_f_class env;
      !fNInf

    let mkNaN env =
      check_f_class env;
      !fNaN

    let mkArray env u t ty =
      check_array env;
      { mark = Cstr; term = FArray (u,t,ty)}

  end

module FredNative = RedNative(FNativeEntries)

let is_irrelevant_constructor infos ((ind,_),u) =
  match Indmap_env.find_opt ind (info_env infos).Environ.irr_inds with
  | None -> false
  | Some r ->
    is_irrelevant infos @@ UVars.subst_instance_relevance u r


module Refold = struct
  let maybe_refold :
    clos_infos ->
    Constr.t ->
    Constr.t * int -> Constr.t array option
    = fun info term (pattern, num_holes) ->
    match [@ocaml.warning "-4"] EqWithHoles.matches_with_holes info.i_cc_info_beta info.i_cc_tab info.i_cache.i_sigma num_holes term pattern with
    | Some oargs when Array.for_all Option.has_some oargs ->
      Some (Array.map (fun t -> Option.get t) oargs)
    | _ -> None
end

(*********************************************************************)
(* A machine that inspects the head of a term until it finds an
   atom or a subterm that may produce a redex (abstraction,
   constructor, cofix, letin, constant), or a neutral term (product,
   inductive) *)
let rec knh info m stk =
  match m.term with
    | FLIFT(k,a) -> knh info a (zshift k stk)
    | FCLOS(t,e) -> knht info e t stk
    | FApp(a,b) -> knh info a (append_stack b stk)
    | FCaseT(ci,u,pms,(_,r as p),t,br,e) ->
      let r' = usubst_relevance e r in
      if is_irrelevant info r' then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        knh info t (ZcaseT(ci,u,pms,p,br,e)::stk)
    | FFix (((ri, n), (lna, _, _)), e, _, _) ->
      if is_irrelevant info (usubst_relevance e (lna.(n)).binder_relevance) then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        (match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh info arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FProj (_,r,_) when is_irrelevant info r->
      (mk_irrelevant, skip_irrelevant_stack info stk)
    | FProj (p,r,c) ->
      let body = { m with term = FProj(Projection.unfold p, r, c) } in
      begin
        match unfold_projection info m body p r with
        | None -> (m, stk)
        | Some s -> knh info c (s :: stk)
      end

(* cases where knh stops *)
    | (FFlex _|FLetIn _|FConstruct _|FEvar _|FCaseInvert _|FIrrelevant|
       FCoFix _|FLambda _|FRel _|FAtom _|FInd _|FProd _|FInt _|FFloat _|
       FString _|FArray _) ->
        (m, stk)

(* The same for pure terms *)
and knht info e t stk =
  match kind t with
    | App(a,b) ->
        knht info e a (append_stack (mk_clos_vect e b) stk)
    | Case(ci,u,pms,(_,r as p),NoInvert,t,br) ->
      if is_irrelevant info (usubst_relevance e r) then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        knht info e t (ZcaseT(ci, u, pms, p, br, e)::stk)
    | Case(ci,u,pms,(_,r as p),CaseInvert{indices},t,br) ->
      if is_irrelevant info (usubst_relevance e r) then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        let term = FCaseInvert (ci, u, pms, p, (Array.map (mk_clos e) indices), mk_clos e t, br, e) in
        { mark = Red; term }, stk
    | Fix (((_, n), (lna, _, _)) as fx) ->
      if is_irrelevant info (usubst_relevance e (lna.(n)).binder_relevance) then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        knh info { mark = Cstr; term = FFix (fx, e, false, None) } stk
    | Cast(a,_,_) -> knht info e a stk
    | Rel n -> knh info (clos_rel (fst e) n) stk
    | Proj (p, r, c) ->
      let r = usubst_relevance e r in
      if is_irrelevant info r then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else begin
        let term = { mark = Red; term = FProj (p, r, mk_clos e c) } in
        let body = { mark = Red; term = FProj (Projection.unfold p, r, mk_clos e c) } in
        match unfold_projection info term body p r with
        | None -> (term, stk)
        | Some s -> knht info e c (s :: stk)
      end
    | (Ind _|Const _|Construct _|Var _|Meta _ | Sort _ | Int _|Float _|String _) -> (mk_clos e t, stk)
    | CoFix cfx ->
      { mark = Cstr; term = FCoFix (cfx,e, None) }, stk
    | Lambda _ -> { mark = Cstr ; term = mk_lambda e t }, stk
    | Prod (n, t, c) ->
      { mark = Ntrl; term = FProd (usubst_binder e n, mk_clos e t, c, e) }, stk
    | LetIn (n,b,t,c) ->
      { mark = Red; term = FLetIn (usubst_binder e n, mk_clos e b, mk_clos e t, c, e) }, stk
    | Evar ev ->
      begin match info.i_cache.i_sigma.evar_expand ev with
      | EvarDefined c -> knht info e c stk
      | EvarUndefined (evk, args) ->
        assert (UVars.Instance.is_empty (snd e));
        if info.i_cache.i_sigma.evar_irrelevant ev then
          (mk_irrelevant, skip_irrelevant_stack info stk)
        else
          let repack = info.i_cache.i_sigma.evar_repack in
          { mark = Ntrl; term = FEvar (evk, args, e, repack) }, stk
      end
    | Array(u,t,def,ty) ->
      let len = Array.length t in
      let ty = mk_clos e ty in
      let t = Parray.init (Uint63.of_int len) (fun i -> mk_clos e t.(i)) (mk_clos e def) in
      let term = FArray (u,t,ty) in
      knh info { mark = Cstr; term } stk

(************************************************************************)

let conv : (clos_infos -> clos_tab -> fconstr -> fconstr -> bool) ref
  = ref (fun _ _ _ _ -> (assert false : bool))

type ('a, 'b) reduction = {
  red_ret : clos_infos -> Table.t -> pat_state:'b -> ?failed:bool -> (fconstr * stack) -> 'a;
  red_kni : clos_infos -> Table.t -> pat_state:'b -> fconstr -> stack -> 'a;
  red_knit : clos_infos -> Table.t -> pat_state:'b -> (fconstr Esubst.subs * UVars.Instance.t) -> Constr.t -> stack -> 'a;
}

type (_, _) escape =
  | No:  ('i, 'i) escape

module RedPattern :
sig

type ('constr, 'stack, 'context) resume_state

type ('constr, 'stack, 'context, _) depth =
  | Nil: ('constr * 'stack, 'ret) escape -> ('constr, 'stack, 'context, 'ret) depth
  | Cons: ('constr, 'stack, 'context) resume_state * ('constr, 'stack, 'context, 'ret) depth -> ('constr, 'stack, 'context, 'ret) depth

type 'a patstate = (fconstr, stack, rel_context, 'a) depth

val match_symbol : ('a, 'a patstate) reduction -> clos_infos -> Table.t ->
  pat_state:(fconstr, stack, rel_context, 'a) depth -> table_key -> UVars.Instance.t * bool * rewrite_rule list -> stack -> 'a

val match_head : ('a, 'a patstate) reduction -> clos_infos -> Table.t ->
  pat_state:(fconstr, stack, rel_context, 'a) depth -> (fconstr, stack, rel_context) resume_state -> fconstr -> stack -> 'a

end =
struct

type 'constr partial_subst = {
  subst: ('constr, Sorts.Quality.t, Univ.Level.t) Partial_subst.t;
  rhs: constr;
}

type 'constr subst_status = Dead | Live of 'constr partial_subst

type 'a status =
  | Check of 'a
  | Ignore

module Status = struct
  let split_array n = function
  | Check a when Array.length a <> n -> invalid_arg "Status.split_array"
  | Check a -> Array.init n (fun i -> Check (Array.unsafe_get a i))
  | Ignore as p -> Array.make n p

  let fold_left f a = function Check b -> f a b | Ignore -> a
end

type ('a, 'b) next =
  | Continue of 'a
  | Return of 'b

type ('constr, 'stack, 'context) state =
  | LocStart of { elims: pattern_elimination list status array; context: 'context; head: 'constr; stack: 'stack; next: ('constr, 'stack, 'context) state_next }
  | LocArg of { patterns: pattern_argument status array; context: 'context; arg: 'constr; next: ('constr, 'stack, 'context) state }

and ('constr, 'stack, 'context) state_next = (('constr, 'stack, 'context) state, bool * 'constr * 'stack) next

type ('constr, 'stack, 'context) resume_state =
  { states: 'constr subst_status array; context: 'context; patterns: head_elimination status array; next: ('constr, 'stack, 'context) state }

type ('constr, 'stack, 'context, _) depth =
  | Nil: ('constr * 'stack, 'ret) escape -> ('constr, 'stack, 'context, 'ret) depth
  | Cons: ('constr, 'stack, 'context) resume_state * ('constr, 'stack, 'context, 'ret) depth -> ('constr, 'stack, 'context, 'ret) depth

type 'a patstate = (fconstr, stack, rel_context, 'a) depth

let extract_or_kill filter a status =
  let step elim status =
    match elim, status with
    | Ignore, s -> s
    | _, Dead -> Dead
    | Check e, Live s -> match filter (e, s) with
      | None -> Dead
      | Some s -> Live s
  in
  Array.map2 step a status

let extract_or_kill2 filter a status =
  let step elim status =
    match elim, status with
   | Ignore, s -> Ignore, s
   | _, Dead -> Ignore, Dead
   | Check e, Live s -> match filter (e, s) with
      | None -> Ignore, Dead
      | Some (p, s) -> Check p, Live s
  in
  Array.split @@ Array.map2 step a status

let extract_or_kill3 filter a status =
  let step elim status =
    match elim, status with
    | Ignore, s -> Ignore, Ignore, s
    | _, Dead -> Ignore, Ignore, Dead
    | Check e, Live s -> match filter (e, s) with
      | None -> Ignore, Ignore, Dead
      | Some (p1, p2, s) -> Check p1, Check p2, Live s
  in
  Array.split3 @@ Array.map2 step a status

let extract_or_kill4 filter a status =
  let step elim status =
    match elim, status with
    | Ignore, s -> Ignore, Ignore, Ignore, s
    | _, Dead -> Ignore, Ignore, Ignore, Dead
    | Check e, Live s -> match filter (e, s) with
      | None -> Ignore, Ignore, Ignore, Dead
      | Some (p1, p2, p3, s) -> Check p1, Check p2, Check p3, Live s
  in
  Array.split4 @@ Array.map2 step a status

let rec match_main : type a. (a, a patstate) reduction -> _ -> _ -> pat_state:(fconstr, stack, _, a) depth -> _ -> _ -> a =
  fun red info tab ~pat_state states loc ->
  if Array.for_all (function Dead -> true | Live _ -> false) states then match_kill red info tab ~pat_state loc else
  match [@ocaml.warning "-4"] loc with
  | LocStart { elims; context; head; stack; next = Return _ as next } ->
    begin match Array.find2_map (fun state elim -> match state, elim with Live s, Check [] -> Some s | _ -> None) states elims with
    | Some { subst; rhs } ->
        let subst, qsubst, usubst = Partial_subst.to_arrays subst in
        let subst = Array.fold_right subs_cons subst (subs_id 0) in
        let usubst = UVars.Instance.of_array (qsubst, usubst) in
        let m' = mk_clos (subst, usubst) rhs in
        begin match pat_state with
        | _ -> red.red_kni info tab ~pat_state m' stack
        end
    | None -> match_elim red info tab ~pat_state next context states elims head stack
    end
  | LocArg { patterns; context; arg; next } ->
      match_arg red info tab ~pat_state next context states patterns arg
  | LocStart { elims; context; head; stack; next } ->
      match_elim red info tab ~pat_state next context states elims head stack

and match_kill : 'a. ('a, 'a patstate) reduction -> _ -> _ -> pat_state:(fconstr, stack, _, 'a) depth -> _ -> 'a =
  fun red info tab ~pat_state -> function
  | LocArg { next; _ } -> match_kill red info tab ~pat_state next
  | LocStart { head; stack; next; _ } ->
      ignore (zip head stack);
      match next with
      | Continue next -> match_kill red info tab ~pat_state next
      | Return k -> try_unfoldfix red info tab ~pat_state k

and match_endstack : 'a. ('a, 'a patstate) reduction -> _ -> _ -> pat_state:(_, _, _, 'a) depth -> _ -> _ -> 'a =
  fun red info tab ~pat_state states next ->
  match next with
  | Continue next -> match_main red info tab ~pat_state states next
  | Return k ->
      assert (Array.for_all (function Dead -> true | Live _ -> false) states);
      try_unfoldfix red info tab ~pat_state k

and try_unfoldfix : 'a. ('a, 'a patstate) reduction -> _ -> _ -> pat_state:(_, _, _, 'a) depth -> _ -> 'a =
  fun red info tab ~pat_state (b, m, stk) ->
  if not b then red.red_ret info tab ~pat_state ~failed:true (m, stk) else
  let _, cargs, stack = strip_update_shift_app_red m stk in
  match [@ocaml.warning "-4"] stack with
  | Zfix (fx,par) :: s ->
    let rarg = zip m cargs in
    let stk' = par @ append_stack [|rarg|] s in
    let (fxe,fxbd) = contract_fix_vect fx.term in
    red.red_knit info tab ~pat_state fxe fxbd stk'
  | _ -> red.red_ret info tab ~pat_state ~failed:true (m, stk)

and match_elim : 'a. ('a, 'a patstate) reduction -> _ -> _ -> pat_state:(fconstr, stack, _, 'a) depth -> _ -> _ -> _ -> _ -> _ -> _ -> 'a =
  fun red info tab ~pat_state next context states elims head stk ->
  match stk with
  | Zapp args :: s ->
      let pargselims, states = extract_or_kill2 (function [@ocaml.warning "-4"] PEApp pargs :: es, subst -> Some ((pargs, es), subst) | _ -> None) elims states in
      let na = Array.length args in
      let np = Array.fold_left (Status.fold_left (fun a (pargs, _) -> min a (Array.length pargs))) na pargselims in
      let pargs, elims, states =
        extract_or_kill3 (fun ((pargs, elims), subst) ->
          let npp = Array.length pargs in
          if npp == np then Some (pargs, elims, subst) else
          let fst, lst = Array.chop np pargs in
          Some (fst, PEApp lst :: elims, subst))
          pargselims states
      in
      let args, rest = Array.chop np args in
      let head = {mark=neutr head.mark; term=FApp(head, args)} in
      let stack = if Array.length rest > 0 then Zapp rest :: s else s in
      let loc = LocStart { elims; context; head; stack; next } in
      let loc = Array.fold_right2 (fun patterns arg next -> LocArg { patterns; context; arg; next }) (Array.transpose (Array.map (Status.split_array np) pargs)) args loc in
      match_main red info tab ~pat_state states loc
  | Zshift k :: s -> match_elim red info tab ~pat_state next context states elims (lift_fconstr k head) s
  | ZcaseT (ci, u, pms, (p, r), brs, e) :: s ->
      let t = FCaseT(ci, u, pms, (p, r), head, brs, e) in
      let mark = neutr head.mark in
      let head = {mark; term=t} in
      let specif = Environ.lookup_mind (fst ci.ci_ind) info.i_cache.i_env in
      let specif = (specif, specif.mind_packets.(snd ci.ci_ind)) in
      let ntys_ret = Environ.expand_arity specif (ci.ci_ind, u) pms (fst p) in
      let ntys_brs = Environ.expand_branch_contexts specif u pms brs in
      let prets, pbrss, elims, states = extract_or_kill4 (function [@ocaml.warning "-4"]
      | PECase (pind, pu, pret, pbrs) :: es, psubst ->
        if not @@ Ind.CanOrd.equal pind ci.ci_ind then None else
          let subst = UVars.Instance.pattern_match pu u psubst.subst in
          Option.map (fun subst -> (pret, pbrs, es, { psubst with subst })) subst
      | _ -> None)
          elims states
      in
      let loc = LocStart { elims; context; head; stack=s; next } in
      let ntys_ret = subst_context e ntys_ret in
      let ret = mk_clos (usubs_liftn (Context.Rel.length ntys_ret) e) (snd p) in
      let brs = Array.map2 (fun ctx br -> subst_context e ctx, mk_clos (usubs_liftn (Context.Rel.length ctx) e) (snd br)) ntys_brs brs in
      let loc = Array.fold_right2 (fun patterns (ctx, arg) next -> LocArg { patterns; context = ctx @ context; arg; next }) (Array.transpose (Array.map (Status.split_array (Array.length brs)) pbrss)) brs loc in
      let loc = LocArg { patterns = prets; context = ntys_ret @ context; arg = ret; next = loc } in
      match_main red info tab ~pat_state states loc
  | Zproj (_undo, proj', r) :: s ->
      let mark = (neutr head.mark) in
      let head = {mark; term=FProj(Projection.make proj' true, r, head)} in
      let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
      | PEProj proj :: es, subst ->
        if not @@ Projection.Repr.CanOrd.equal (Projection.repr proj) proj' then None else
        Some (es, subst)
      | _ -> None) elims states
      in
      let loc = LocStart { elims; context; head; stack=s; next } in
      match_main red info tab ~pat_state states loc
  | Zfix _ :: _ | Zprimitive _ :: _ ->
      let states = extract_or_kill (fun _ -> None) elims states in
      ignore (zip head stk);
      match_endstack red info tab ~pat_state states next
  | (Zunfold _ | ZundoOrRefold _) :: __ -> assert false (* TODO *)
  | [] ->
      let states = extract_or_kill (function [], subst -> Some subst | _ -> None) elims states in
      match_endstack red info tab ~pat_state states next

and match_arg : 'a. ('a, 'a patstate) reduction -> _ -> _ -> pat_state:(fconstr, stack, _, 'a) depth -> _ -> _ -> _ -> _ -> _ -> 'a =
  fun red info tab ~pat_state next context states patterns t ->
  let match_deeper = ref false in
  let t' = it_mkLambda_or_LetIn context t in
  let patterns, states = Array.split @@ Array.map2
    (function Dead -> fun _ -> Ignore, Dead | (Live ({ subst; _ } as psubst) as state) -> function
      | Ignore -> Ignore, state
      | Check EHole i -> Ignore, Live { psubst with subst = Partial_subst.add_term i t' subst }
      | Check EHoleIgnored -> Ignore, state
      | Check ERigid p -> match_deeper := true; Check p, state
    ) states patterns in
  if !match_deeper then
    let pat_state = Cons ({ states; context; patterns; next }, pat_state) in
    red.red_kni info tab ~pat_state t []
  else
    match_main red info tab ~pat_state states next

and match_head : 'a. ('a, 'a patstate) reduction -> _ -> _ -> pat_state:(fconstr, stack, _, 'a) depth -> _ -> _ -> _ -> _ -> _ -> _ -> 'a =
  fun red info tab ~pat_state next context states patterns t stk ->
  match [@ocaml.warning "-4"] t.term with
  | FInd (ind', u) ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHInd (ind, pu), elims), psubst ->
      if not @@ Ind.CanOrd.equal ind ind' then None else
      let subst = UVars.Instance.pattern_match pu u psubst.subst in
      Option.map (fun subst -> elims, { psubst with subst }) subst
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FConstruct (constr', u) ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHConstr (constr, pu), elims), psubst ->
      if not @@ Construct.CanOrd.equal constr constr' then None else
      let subst = UVars.Instance.pattern_match pu u psubst.subst in
      Option.map (fun subst -> elims, { psubst with subst }) subst
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FAtom t' -> begin match [@ocaml.warning "-4"] kind t' with
    | Sort s ->
      let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
      | (PHSort ps, elims), psubst ->
        let subst = Sorts.pattern_match ps s psubst.subst in
        Option.map (fun subst -> elims, { psubst with subst }) subst
      | _ -> None) patterns states
      in
      let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
      match_main red info tab ~pat_state states loc
    | Meta _ ->
      let elims, states = extract_or_kill2 (fun _ -> None) patterns states in
      let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
      match_main red info tab ~pat_state states loc
    | _ -> assert false
    end
  | FFlex (ConstKey (c', u)) ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHSymbol (c, pu), elims), psubst ->
      if not @@ Constant.CanOrd.equal c c' then None else
      let subst = UVars.Instance.pattern_match pu u psubst.subst in
      Option.map (fun subst -> elims, { psubst with subst }) subst
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FRel n ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHRel n', elims), psubst ->
      if not @@ Int.equal n n' then None else
      Some (elims, psubst)
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FInt i' ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHInt i, elims), psubst ->
      if not @@ Uint63.equal i i' then None else
      Some (elims, psubst)
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FFloat f' ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHFloat f, elims), psubst ->
      if not @@ Float64.equal f f' then None else
      Some (elims, psubst)
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FString s' ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHString s, elims), psubst ->
      if not @@ Pstring.equal s s' then None else
      Some (elims, psubst)
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FProd (n, ty, body, e) ->
    let ntys, _ = Term.decompose_prod body in
    let na = 1 + List.length ntys in
    let tysbodyelims, states = extract_or_kill2 (function [@ocaml.warning "-4"] (PHProd (ptys, pbod), es), psubst when Array.length ptys <= na -> Some ((ptys, pbod, es), psubst) | _ -> None) patterns states in
    let na = Array.fold_left (Status.fold_left (fun a (p1, _, _) -> min a (Array.length p1))) na tysbodyelims in
    assert (na > 0);
    let ptys, pbody, elims, states = extract_or_kill4 (fun ((ptys, pbod, elims), psubst) ->
        let npp = Array.length ptys in
        if npp == na then Some (ptys, pbod, elims, psubst) else
        let fst, lst = Array.chop na ptys in
        Some (fst, ERigid (PHProd (lst, pbod), []), elims, psubst)
      ) tysbodyelims states
    in

    let ntys, body = Term.decompose_prod_n (na-1) body in
    let ctx1 = List.map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) ntys |> subst_context e in
    let ctx = ctx1 @ [Context.Rel.Declaration.LocalAssum (n, term_of_fconstr ty)] in
    let ntys'' = List.mapi (fun n (_, t) -> mk_clos (usubs_liftn n e) t) (List.rev ntys) in
    let tys = Array.of_list (ty :: ntys'') in
    let contexts_upto = Array.init na (fun i -> List.lastn i ctx @ context) in
    let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
    let loc = LocArg { patterns = pbody; context = ctx @ context; arg = mk_clos (usubs_liftn na e) body; next = loc } in
    let loc = Array.fold_right3 (fun patterns arg context next -> LocArg { patterns; context; arg; next }) (Array.transpose (Array.map (Status.split_array na) ptys)) tys contexts_upto loc in
    match_main red info tab ~pat_state states loc
  | FLambda (na, ntys, body, e) ->
    let tysbodyelims, states = extract_or_kill2 (function [@ocaml.warning "-4"] (PHLambda (ptys, pbod), es), psubst when Array.length ptys <= na -> Some ((ptys, pbod, es), psubst) | _ -> None) patterns states in
    let na = Array.fold_left (Status.fold_left (fun a (p1, _, _) -> min a (Array.length p1))) na tysbodyelims in
    assert (na > 0);
    let ptys, pbody, elims, states = extract_or_kill4 (fun ((ptys, pbod, elims), psubst) ->
      let np = Array.length ptys in
      if np == na then Some (ptys, pbod, elims, psubst) else
      let fst, lst = Array.chop na ptys in
      Some (fst, ERigid (PHLambda (lst, pbod), []), elims, psubst)
      ) tysbodyelims states
    in
    let ntys, tys' = List.chop na ntys in
    let body = Term.compose_lam (List.rev tys') body in
    let ctx = List.rev_map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) ntys |> subst_context e in
    let tys = Array.of_list ntys in
    let tys = Array.mapi (fun n (_, t) -> mk_clos (usubs_liftn n e) t) tys in
    let contexts_upto = Array.init na (fun i -> List.lastn i ctx @ context) in
    let loc = LocStart { elims; context; head=t; stack=stk; next=Continue next } in
    let loc = LocArg { patterns = pbody; context = ctx @ context; arg = mk_clos (usubs_liftn na e) body; next = loc } in
    let loc = Array.fold_right3 (fun patterns arg context next -> LocArg { patterns; context; arg; next }) (Array.transpose (Array.map (Status.split_array na) ptys)) tys contexts_upto loc in
    match_main red info tab ~pat_state states loc
  | _ ->
    let states = extract_or_kill (fun _ -> None) patterns states in
    ignore (zip t stk);
    match_main red info tab ~pat_state states next

let match_symbol red info tab ~pat_state fl (u, b, r) stk =
  let unfold_fix = b && red_set info.i_flags fFIX in
  let states, elims = Array.split @@ Array.map
    (fun r ->
      let pu, es = r.lhs_pat in
      let subst = Partial_subst.make r.nvars in
      let subst = UVars.Instance.pattern_match pu u subst in
      match subst with
      | Some subst -> Live { subst; rhs = r.Declarations.rhs }, Check es
      | None -> Dead, Ignore
    ) (Array.of_list r)
  in
  let m = { mark = Red; term = FFlex fl } in
  let loc = LocStart { elims; context=[]; head = m; stack = stk; next = Return (unfold_fix, m, stk) } in
  match_main red info tab ~pat_state states loc

let match_head red info tab ~pat_state { states; context; patterns; next } m stk =
  match_head red info tab ~pat_state next context states patterns m stk

end

type 'a depth = 'a RedPattern.patstate

(* Computes a weak head normal form from the result of knh. *)
let rec knr : 'a. _ -> _ -> pat_state: 'a depth -> _ -> _ -> 'a =
  fun info tab ~pat_state m stk ->
  Dbg.(dbg Pp.(fun () -> str "knr; m head: " ++ Pp.fnl () ++ pp_fconstr info.i_cache.i_env m));
  Dbg.(dbg Pp.(fun () -> str "knr; m stk : " ++ Pp.fnl () ++ pp_stack info.i_cache.i_env stk));
  Dbg.(dbg Pp.(fun () -> str "knr; m full: " ++ Pp.fnl () ++ pp_fconstr info.i_cache.i_env (zip ~dbg:true m stk)));
  Dbg.(dbg Pp.(fun () -> str "knr; m constr: " ++ Pp.fnl () ++ Constr.debug_print (term_of_fconstr (zip ~dbg:true m stk))));
  Dbg.(dbg Pp.(fun () -> str "=============================================="));
  match m.term with
  | FLambda(n,tys,f,e) when red_set info.i_flags fBETA ->
      (match get_args n tys f e stk with
          Inl (_, e'), s -> knit info tab ~pat_state e' f s
        | Inr lam, s -> knr_ret info tab ~pat_state (lam,s))
  | FFlex fl when red_set info.i_flags fDELTA ->
      (match Table.lookup info tab fl with
        | Def (v, ogfix) ->
          begin
            match [@ocaml.warning "-4"] fl with
            | Names.ConstKey (cst, _) ->
              start_unfold info tab ~pat_state m cst v ogfix stk
            | _ ->
              let term = { m with mark = Cstr } in
              maybe_undo info tab ~pat_state ((Original.{term;body=v}, [Undo.OnNoProgress]), []) v stk
          end
        | Primitive op ->
          if check_native_args op stk then
            let c = match fl with ConstKey c -> c | RelKey _ | VarKey _ -> assert false in
            let rargs, a, nargs, stk = get_native_args1 op c stk in
            kni info tab ~pat_state a (Zprimitive(op,c,rargs,nargs)::stk)
          else
            (* Similarly to fix, partially applied primitives are not Ntrl! *)
            knr_ret info tab ~pat_state (m, stk)
        | Symbol (u, b, r) ->
          let red = {
            red_kni = kni;
            red_knit = knit;
            red_ret = knr_ret;
          } in
          RedPattern.match_symbol red info tab ~pat_state fl (u, b, r) stk
        | Undef _ | OpaqueDef _ -> (set_ntrl m; knr_ret info tab ~pat_state (m,stk)))
  | FConstruct c ->
     let use_match = red_set info.i_flags fMATCH in
     let use_fix = red_set info.i_flags fFIX in
     if use_match || use_fix then
       begin
        strip_shift_app_undo ~is_matchfix:false m stk
          ~abort:(knr_ret info tab ~pat_state ?failed:None)
        @@ fun ~cont ~depth ~cargs -> function[@ocaml.warning "-4"]
          | (ZcaseT(ci,_,pms,_,br,e)::s) when use_match ->
              assert (ci.ci_npar>=0);
              (* instance on the case and instance on the constructor are compatible by typing *)
              let (br, e) = get_branch info depth ci pms c br e (cargs()) in
              knit info tab ~pat_state e br (push_progress s)
          | (Zfix(fx,par)::s) when use_fix ->
              let rarg = zip m (cargs()) in
              let stk' = par @ append_stack [|rarg|] (push_progress s) in
              let (fxe,fxbd) = contract_fix_vect fx.term in
              knit info tab ~pat_state fxe fxbd stk'
          | (Zproj (unf, p,_)::s) when use_match ->
              let open UnfoldProj in
              let rargs = drop_parameters depth (Projection.Repr.npars p) (cargs()) in
              let rarg = project_nth_arg (Projection.Repr.arg p) rargs in
              let s = push_progress s in
              let s = push_undo (unf.undo, true, unf.orig, []) s in
              kni info tab ~pat_state rarg s
          | (Zunfold (_, unf, rev_params) :: stk) ->
            Dbg.(dbg Pp.(fun () -> str "knr; Zunfold"));
            let m = zip m (cargs()) in
            let rev_params = Zapp [|m|] :: rev_params in
            consume_arg info tab ~pat_state unf rev_params stk
          | _ -> cont ()
      end
     else if is_irrelevant_constructor info c then
      knr_ret info tab ~pat_state (mk_irrelevant, skip_irrelevant_stack info stk)
     else
      knr_ret info tab ~pat_state (m, stk)
  | FCoFix ((i, (lna, _, _)), e, _) ->
    if is_irrelevant info (usubst_relevance e (lna.(i)).binder_relevance) then
      knr_ret info tab ~pat_state (mk_irrelevant, skip_irrelevant_stack info stk)
    else if red_set info.i_flags fCOFIX then
      begin
        strip_shift_app_undo ~is_matchfix:true m stk
          ~abort:(knr_ret info tab ~pat_state ?failed:None)
        @@ fun ~cont ~depth:_ ~cargs -> function[@ocaml.warning "-4"]
        | ((ZcaseT _::_) as stk') ->
            let (fxe,fxbd) = contract_fix_vect m.term in
            let stk' = push_progress stk' in
            knit info tab ~pat_state fxe fxbd (cargs()@stk')
        | ((Zproj (unf,_,_)::_) as stk') ->
            let open UnfoldProj in
            let (fxe,fxbd) = contract_fix_vect m.term in
            let stk' = push_progress stk' in
            let stk' = push_undo (unf.undo, true, unf.orig, []) stk' in
            knit info tab ~pat_state fxe fxbd (cargs()@stk')
        | _ -> cont ()
      end
    else knr_ret info tab ~pat_state (m, stk)
  | FLetIn (_,v,_,bd,e) when red_set info.i_flags fZETA ->
      knit info tab ~pat_state (on_fst (subs_cons v) e) bd (push_progress stk)
  | FInt _ | FFloat _ | FString _ | FArray _ ->
    begin
      strip_shift_app_undo ~is_matchfix:false m stk
        ~abort:(knr_ret info tab ~pat_state ?failed:None)
      @@ fun ~cont ~depth:_ ~cargs -> function[@ocaml.warning "-4"]
      | (Zprimitive(op,(_,u as c),rargs,nargs)::s) ->
        let s = cargs()@s in
        let (rargs, nargs) = skip_native_args (m::rargs) nargs in
        begin match nargs with
        | [] ->
          let args = Array.of_list (List.rev rargs) in
          begin match FredNative.red_prim (info_env info) () op u args with
          | Some m -> kni info tab ~pat_state m (push_progress s)
          | None -> assert false
          end
        | (kd,a)::nargs ->
          assert (kd = CPrimitives.Kwhnf);
          kni info tab ~pat_state a (Zprimitive(op,c,rargs,nargs)::s)
        end
      | _ -> cont ()
    end
  | FCaseInvert (ci, u, pms, _p,iv,_c,v,env) when red_set info.i_flags fMATCH ->
    let pms = mk_clos_vect env pms in
    let u = usubst_instance env u in
    begin match case_inversion info tab ci u pms iv v with
      | Some c -> knit info tab ~pat_state env c stk
      | None -> knr_ret info tab ~pat_state (m, stk)
    end
  | FIrrelevant ->
    let stk = skip_irrelevant_stack info stk in
    knr_ret info tab ~pat_state (m, stk)
  | FProd _ | FAtom _ | FInd _ (* relevant statically *)
  | FCaseInvert _ | FProj _ | FFix _ | FEvar _ (* relevant because of knh(t) *)
  | FLambda _ | FFlex _ | FRel _ (* irrelevance handled by conversion *)
  | FLetIn _ (* only happens in reduction mode *) ->
    knr_ret info tab ~pat_state (m, stk)
  | FCLOS _ | FApp _ | FCaseT _ | FLIFT _ ->
    (* ruled out by knh(t) *)
    assert false

and knr_ret : type a. _ -> _ -> pat_state: a depth -> ?failed: _ -> _ -> a =
  fun info tab ~pat_state ?failed (m, stk) ->
  Dbg.(dbg Pp.(fun () -> str "kret"));
  match pat_state with
  | RedPattern.Cons (patt, pat_state) ->
      let red = {
        red_kni = kni;
        red_knit = knit;
        red_ret = knr_ret;
      } in
      RedPattern.match_head red info tab ~pat_state patt m stk
  | RedPattern.Nil b ->
    ignore failed;
    match b with No -> (m, stk)

and start_unfold : 'a. _ -> _ -> pat_state: 'a depth -> _ -> _ -> _ -> ?must_unfold:_ -> _ -> _ -> 'a
  = fun info tab ~pat_state m cst body ?(must_unfold=false) ogfix stk ->
  let module R = Reductionops.ReductionBehaviour in
  (* No matter how we proceed, [m] should not be considered reducible anymore by
     the rest of the machine *)
  let m = { m with mark = Ntrl } in
  let open UnfoldDef in
  match R.get cst with
  | None -> unfold info tab ~pat_state (Original.{term=m; body}, [Undo.OnNoProgress]) body ~must_unfold ogfix [] stk
  | Some NeverUnfold -> knr_ret info tab ~pat_state (m, stk)
  | Some ((UnfoldWhen flags | UnfoldWhenNoMatch flags) as u) ->
    let (undo, enough_args, must_unfold) =
      match[@ocaml.warning "-4"] flags.R.nargs, u with
      | None, UnfoldWhenNoMatch _ -> ([Undo.OnNoProgress; Undo.OnMatchFix], true, false)
      | None, _ -> ([Undo.OnNoProgress], true, false)
      | Some nargs, UnfoldWhenNoMatch _ -> ([Undo.OnMatchFix], nargs <= (stack_args_size stk), false)
      | Some nargs, UnfoldWhen _ -> ([], nargs <= (stack_args_size stk), true)
      | Some _, _ -> assert false
    in
    if not enough_args then
      knr_ret info tab ~pat_state (m, stk)
    else
      let unf =
        { recargs = flags.R.recargs;
          recargs_shift = 0;
          orig = Original.{term=m;body};
          ogfix;
          undo;
          must_unfold;
        }
      in
      consume_arg info tab ~pat_state unf [] stk

and unfold : 'a. _ -> _ -> pat_state: 'a depth  -> (Original.t * Undo.t list) -> ?must_unfold:_ -> _ -> _ -> _ -> _ -> 'a
  = fun info tab ~pat_state undos ?(must_unfold = false) body ogfix rev_params stk ->
  let stk = List.rev_append rev_params stk in
  match ogfix with
  | None -> maybe_undo info tab ~pat_state (undos, []) body stk
  | Some (GFixInfo gfix) ->
    if Int.equal gfix.gfix_nargs 0 then
      let refold = Some gfix.gfix_refold in
      maybe_undo info tab ~pat_state (undos, []) { mark = Cstr; term = FFix (gfix.gfix_body, (subs_id 0, gfix.gfix_univs), must_unfold, refold) } stk
    else if red_set info.i_flags fBETA then
      match get_args gfix.gfix_nargs gfix.gfix_tys (mkFix gfix.gfix_body) (subs_id 0, gfix.gfix_univs) stk with
      | Inl (rev_extra_args, e), stk ->
        let refold = Some gfix.gfix_refold in
        maybe_undo info tab ~pat_state (undos, rev_extra_args) { mark = Cstr; term = FFix (gfix.gfix_body, e, must_unfold, refold) } stk
      | Inr lam, stk -> knr_ret info tab ~pat_state (lam, stk)
    else maybe_undo info tab ~pat_state (undos, []) body stk
  | Some (GCoFixInfo gcofix) ->
    if Int.equal gcofix.gfix_nargs 0 then
      let refold = Some gcofix.gfix_refold in
      maybe_undo info tab ~pat_state (undos, []) { mark = Cstr; term = FCoFix (gcofix.gfix_body, (subs_id 0, gcofix.gfix_univs), refold) } stk
    else if red_set info.i_flags fBETA then
      match get_args gcofix.gfix_nargs gcofix.gfix_tys (mkCoFix gcofix.gfix_body) (subs_id 0, gcofix.gfix_univs) stk with
      | Inl (rev_extra_args, e), stk ->
        let refold = Some gcofix.gfix_refold in
        maybe_undo info tab ~pat_state (undos, rev_extra_args) { mark = Cstr; term = FCoFix (gcofix.gfix_body, e, refold) } stk
      | Inr lam, stk -> knr_ret info tab ~pat_state (lam, stk)
    else maybe_undo info tab ~pat_state (undos, []) body stk

and maybe_undo : 'a. _ -> _ -> pat_state: 'a depth -> (Original.t * Undo.t list) * stack -> _ -> _ -> 'a
  = fun info tab ~pat_state undos m stk ->
    match undos with
    | ((_, []), _rev_extra_args) ->
      kni info tab ~pat_state m stk
    | ((orig, undos), rev_extra_args) ->
      let (_, cargs, stk) = strip_update_shift_app (orig.Original.term) stk in
      let stk = cargs @ push_undo (undos, false, orig, List.rev_append cargs rev_extra_args) stk in
      kni info tab ~pat_state m stk

and consume_arg : 'a. _ -> _ -> pat_state: 'a depth -> _ -> _ -> _ -> 'a
  = fun info tab ~pat_state unf rev_params stk ->
  let open UnfoldDef in
  match unf.recargs with
  | [] ->
    let undo = (unf.orig, unf.undo) in
    Dbg.(dbg Pp.(fun () -> str "consume_arg: done; undo=" ++ (fun (Original.{term=x;_},_) -> pp_fconstr info.i_cache.i_env x) undo));
    unfold info tab ~pat_state undo unf.orig.Original.body unf.ogfix ~must_unfold:unf.must_unfold rev_params stk
  | recarg :: recargs ->
    Dbg.(dbg Pp.(fun () -> str "consume_arg: more args"));
    match get_nth_arg (unf.orig.Original.term) (recarg - unf.recargs_shift) stk with
    | (None, stk) ->
      Dbg.(dbg Pp.(fun () -> str "consume_arg: could not find arg: " ++ int (recarg - unf.recargs_shift)));
      let m = unf.orig.Original.term in
      let stk = List.rev_append rev_params stk in
      knr_ret info tab ~pat_state (m, stk)
    | (Some(params, arg), stk) ->
      Dbg.(dbg Pp.(fun () -> str "consume_arg: found arg: " ++ int (recarg - unf.recargs_shift)));
      let rev_params = List.rev_append params rev_params in
      let unf = { unf with recargs; recargs_shift = unf.recargs_shift + 1 + stack_args_size params } in
      let stk = Zunfold (None, unf, rev_params) :: stk in
      kni info tab ~pat_state arg stk

(* Computes the weak head normal form of a term *)
and kni : 'a. _ -> _ -> pat_state: 'a depth -> _ -> _ -> 'a =
  fun info tab ~pat_state m stk ->
  let (hm,s) = knh info m stk in
  knr info tab ~pat_state hm s
and knit : 'a. _ -> _ -> pat_state: 'a depth -> _ -> _ -> _ -> 'a =
  fun info tab ~pat_state e t stk ->
  let (ht,s) = knht info e t stk in
  knr info tab ~pat_state ht s

and case_inversion info _tab ci u params indices v = match v with
| [||] -> None (* empty type *)
| [| [||], v |] ->
  (* No binders / lets at all in the unique branch *)
  let open Declarations in
  if Array.is_empty indices then Some v
  else
    let env = info_env info in
    let ind = ci.ci_ind in
    let psubst = subs_consn params 0 ci.ci_npar (subs_id 0) in
    let mib = Environ.lookup_mind (fst ind) env in
    let mip = mib.mind_packets.(snd ind) in
    (* indtyping enforces 1 ctor with no letins in the context *)
    let _, expect = mip.mind_nf_lc.(0) in
    let _ind, expect_args = destApp expect in
    let tab = Table.create () in
    let check_index i index =
      let expected = expect_args.(ci.ci_npar + i) in
      let expected = mk_clos (psubst,u) expected in
      !conv info tab expected index
    in
    if Array.for_all_i check_index 0 indices
    then Some v else None
| _ -> assert false

let kni info tab v stk = kni info tab ~pat_state:(RedPattern.Nil No) v stk
let knit info tab v stk = knit info tab ~pat_state:(RedPattern.Nil No) v stk

(************************************************************************)

(* Computes the strong normal form of a term.
   1- Calls kni
   2- tries to rebuild the term. If a closure still has to be computed,
      calls itself recursively. *)

let is_val v = match v.term with
| FAtom _ | FRel _   | FInd _ | FConstruct _ | FInt _ | FFloat _ | FString _ -> true
| FFlex _ -> v.mark == Ntrl
| FApp _ | FProj _ | FFix _ | FCoFix _ | FCaseT _ | FCaseInvert _ | FLambda _
| FProd _ | FLetIn _ | FEvar _ | FArray _ | FLIFT _ | FCLOS _ -> false
| FIrrelevant -> assert false

(* Refolding stacks: just a list of stacks that hopefully contain
   interesting refolding information *)

let refold_rstks info ~rstks (m : Constr.t) : Constr.t =
  let rec go_inner m id rstk =
    match [@ocaml.warning "-4"] rstk with
    | [] -> Result.Ok m
    | ZundoOrRefold(undo, prog, orig, rev_params) :: rstk ->
      if not prog && List.mem Undo.OnNoProgress undo then
        (* this term will not survive. Abort *)
        Result.Error m
      else
        let num_holes = stack_args_size rev_params in
        let pattern = term_of_fconstr orig.Original.body in
        if id then Result.Ok m else
        let m = match Refold.maybe_refold info m (pattern, num_holes) with
          | Some args ->
            (mkApp (term_of_fconstr orig.Original.term, args))
          | _ -> m
        in
        go_inner m id rstk
    | Zapp args :: rstk ->
      (* We copied these stacks before zip_term had a chance to apply arguments.
         It is thus useful to pretend that they've already been applied to [m],
         i.e. ignoring [Zapp] nodes entirely *)
      go_inner m (id && Array.length args = 0) rstk
    | _ -> Result.Ok m
  in
  let rec go m first_stk rstks =
    match rstks with
    | [] -> m
    | rstk :: rstks ->
      match go_inner m first_stk rstk with
      | Result.Error m -> if first_stk then m else go m false rstks
      | Result.Ok m -> go m false rstks
  in
  go m true rstks

let rec zip_term kl klt info tab ?(progress=false) ~rstks m stk =
  let m = refold_rstks info ~rstks:(stk::rstks) m in
  (* Inject outer refolding information into subterms *)
  let kl info tab ~rstks = kl info tab ~rstks:(stk::rstks) in
  let klt info tab ~rstks = klt info tab ~rstks:(stk::rstks) in
  match stk with
| [] -> m
| Zapp args :: s ->
    zip_term kl klt info tab ~progress ~rstks (mkApp(m, Array.map (kl info tab ~rstks) args)) s
| ZcaseT(ci, u, pms, (p,r), br, e) :: s ->
  let zip_ctx (nas, c) =
      let nas = Array.map (usubst_binder e) nas in
      let e = usubs_liftn (Array.length nas) e in
      (nas, klt info tab ~rstks e c)
    in
    let r = usubst_relevance e r in
    let u = usubst_instance e u in
    let t = mkCase(ci, u, Array.map (fun c -> klt info tab ~rstks e c) pms, (zip_ctx p, r),
      NoInvert, m, Array.map zip_ctx br) in
    zip_term kl klt info tab ~progress:false ~rstks t s
| Zproj (_,p,r)::s ->
    let t = mkProj (Projection.make p true, r, m) in
    zip_term kl klt info tab ~progress:false ~rstks t s
| Zfix(fx,par)::s ->
  let (keep_unfolded,i,env,gfix) =
    match[@ocaml.warning "-4"] fx.term with
      FFix (((_,i),_),env,must_unfold,gfix) -> (must_unfold || gfix = None,i,env,gfix)
    | _ -> assert false
  in
  if (not keep_unfolded) && Result.is_ok (Lazy.force ((Option.get gfix).(i))) then
    let m = inject m in
    let gfix = Result.get_ok (Lazy.force ((Option.get gfix).(i))) in
    let fx = { mark = Cstr; term = FCLOS (gfix, env) } in
    let s = par @ Zapp [|m|] :: s in
    zip_term kl klt info tab ~progress ~rstks (norm_head kl klt info tab ~rstks fx) s
  else
    let h = mkApp(zip_term kl klt info tab ~progress ~rstks (kl info tab ~rstks fx) par,[|m|]) in
    zip_term kl klt info tab ~progress ~rstks h s
| Zshift(n)::s ->
    zip_term kl klt info tab ~progress ~rstks (lift n m) s
| Zprimitive(_,c,rargs, kargs)::s ->
    let kargs = List.map (fun (_,a) -> kl info tab ~rstks a) kargs in
    let args =
      List.fold_left (fun args a -> kl info tab ~rstks a ::args) (m::kargs) rargs in
    let h = mkApp (mkConstU c, Array.of_list args) in
    zip_term kl klt info tab ~progress:false ~rstks h s
| Zunfold (undo, unf, rev_params) :: s ->
  Dbg.(dbg Pp.(fun () -> str "zip_term; Zunfold"));
  let open UnfoldDef in
  let m =
    match undo with
    | Some (_, orig, rev_params) ->
      (* TODO: we've already tried to reduce this. We are just going to waste our time here. *)
      zip_term kl klt info tab ~progress ~rstks (norm_head kl klt info tab ~rstks (orig.Original.term)) (List.rev rev_params)
    | None -> m
  in
  let orig = zip_term kl klt info tab ~progress ~rstks (norm_head kl klt info tab ~rstks (unf.orig.Original.term)) (List.rev rev_params) in
  let orig = mkApp (orig, [|m|]) in
  zip_term kl klt info tab ~progress:false ~rstks orig s
| ZundoOrRefold (undos, prog, orig, rev_params) :: stk ->
  let orig = orig.Original.term in
  let progress = progress || prog in
  if not progress && List.mem Undo.OnNoProgress undos then
    zip_term kl klt info tab ~progress:false ~rstks (norm_head kl klt info tab ~rstks orig) (List.rev_append rev_params stk)
  else if List.mem Undo.OnMatchFix undos then
    match [@ocaml.warning "-4"] kind m with
    (* TODO: FCaseInvert? *)
    | Proj (p,_,_) when Names.Projection.unfolded p ->
      Dbg.(dbg Pp.(fun () -> str "finish|ZundoOrRefold; yes (Proj)!"));
      zip_term kl klt info tab ~progress:false ~rstks (norm_head kl klt info tab ~rstks orig) (List.rev_append rev_params stk)
    | Case _ ->
      Dbg.(dbg Pp.(fun () -> str "finish|ZundoOrRefold; yes (Fix/CoFix/Case)!"));
      zip_term kl klt info tab ~progress:false ~rstks (norm_head kl klt info tab ~rstks orig) (List.rev_append rev_params stk)
    | _ ->
      Dbg.(dbg Pp.(fun () -> str "finish|ZundoOrRefold? no!"));
      zip_term kl klt info tab ~progress ~rstks m stk
  else
    zip_term kl klt info tab ~progress ~rstks m stk

(* no redex: go up for atoms and already normalized terms, go down
   otherwise. *)
and norm_head kl klt info tab ~rstks (m : fconstr) =
  if is_val m then term_of_fconstr m else
    match m.term with
      | FLambda(_n,tys,f,e) ->
        let fold (e, info, ctxt) (na, ty) =
          let na = usubst_binder e na in
          let ty = klt info tab ~rstks e ty in
          let info = push_relevance info na in
          (usubs_lift e, info, (na, ty) :: ctxt)
        in
        let (e', info, rvtys) = List.fold_left fold (e,info,[]) tys in
        let bd = klt info tab ~rstks e' f in
        List.fold_left (fun b (na,ty) -> mkLambda(na,ty,b)) bd rvtys
      | FLetIn(na,a,b,f,e) ->
          let na = usubst_binder e na in
          let c = klt (push_relevance info na) tab ~rstks (usubs_lift e) f in
          mkLetIn(na, kl info tab ~rstks a, kl info tab ~rstks b, c)
      | FProd(na,dom,rng,e) ->
        let na = usubst_binder e na in
        let rng = klt (push_relevance info na) tab ~rstks (usubs_lift e) rng in
          mkProd(na, kl info tab ~rstks dom, rng)
      | FCoFix((n,(na,tys,bds)),e, _) ->
          let na = Array.Smart.map (usubst_binder e) na in
          let infobd = push_relevances info na in
          let ftys = Array.map (fun ty -> klt info tab ~rstks e ty) tys in
          let fbds = Array.map (fun bd -> klt infobd tab ~rstks (usubs_liftn (Array.length na) e) bd) bds in
          mkCoFix (n, (na, ftys, fbds))
      | FFix((n,(na,tys,bds)), e, _must_unfold, _) ->
          let na = Array.Smart.map (usubst_binder e) na in
          let infobd = push_relevances info na in
          let ftys = Array.map (fun ty -> klt info tab ~rstks e ty) tys in
          let fbds = Array.map (fun bd -> klt infobd tab ~rstks (usubs_liftn (Array.length na) e) bd) bds in
          mkFix (n, (na, ftys, fbds))
      | FEvar(ev, args, env, repack) ->
          repack (ev, List.map (fun a -> klt info tab ~rstks env a) args)
      | FProj (p,r,c) ->
        mkProj (p, r, kl info tab ~rstks c)
      | FArray (u, a, ty) ->
        let a, def = Parray.to_array a in
        let a = Array.map (kl info tab ~rstks) a in
        let def = kl info tab ~rstks def in
        let ty = kl info tab ~rstks ty in
        mkArray (u, a, def, ty)
      | FRel _ | FAtom _ | FFlex _ | FInd _ | FConstruct _
      | FApp _ | FCaseT _ | FCaseInvert _ | FLIFT _ | FCLOS _ | FInt _
      | FFloat _ | FString _ -> term_of_fconstr m
      | FIrrelevant -> assert false (* only introduced when converting *)

let rec kl info tab ~rstks m =
  if is_val m then term_of_fconstr m
  else
    let (nm,s) = kni info tab m [] in
    zip_term kl klt info tab ~rstks (norm_head kl klt info tab ~rstks:(rstks) nm) s

and klt info tab ~rstks e t = match kind t with
| Rel i ->
  begin match expand_rel i (fst e) with
  | Inl (n, mt) -> kl info tab ~rstks @@ lift_fconstr n mt
  | Inr (k, None) -> if Int.equal k i then t else mkRel k
  | Inr (k, Some p) -> kl info tab ~rstks @@ lift_fconstr (k-p) {mark=Red;term=FFlex(RelKey p)}
  end
| App (hd, args) ->
  begin match kind hd with
  | Ind _ | Construct _ ->
    let args' = Array.Smart.map (fun c -> klt info tab ~rstks e c) args in
    let hd' = subst_instance_constr (snd e) hd in
    if hd' == hd && args' == args then t
    else mkApp (hd', args')
  | Var _ | Const _ | CoFix _ | Lambda _ | Fix _ | Prod _ | Evar _ | Case _
  | Cast _ | LetIn _ | Proj _ | Array _ | Rel _ | Meta _ | Sort _ | Int _
  | Float _ | String _ ->
    let (nm,s) = knit info tab e t [] in
    let rstks = s :: rstks in
    zip_term kl klt info tab ~rstks (norm_head kl klt info tab ~rstks nm) s
  | App _ -> assert false
  end
| Lambda (na, u, c) ->
  let na' = usubst_binder e na in
  let u' = klt info tab ~rstks e u in
  let c' = klt (push_relevance info na') tab ~rstks (usubs_lift e) c in
  if na' == na && u' == u && c' == c then t
  else mkLambda (na', u', c')
| Prod (na, u, v) ->
  let na' = usubst_binder e na in
  let u' = klt info tab ~rstks e u in
  let v' = klt (push_relevance info na') tab ~rstks (usubs_lift e) v in
  if na' == na && u' == u && v' == v then t
  else mkProd (na', u', v')
| Cast (t, _, _) -> klt info tab ~rstks e t
| Var _ | Const _ | CoFix _ | Fix _ | Evar _ | Case _ | LetIn _ | Proj _ | Array _ ->
  let (nm,s) = knit info tab e t [] in
  let rstks = s :: rstks in
  zip_term kl klt info tab ~rstks (norm_head kl klt info tab ~rstks nm) s
| Meta _ | Sort _ | Ind _ | Construct _ | Int _ | Float _ | String _ ->
  subst_instance_constr (snd e) t

(* Initialization and then normalization *)

(* weak reduction *)
let kh info tab ~rstks v stk =
  let v, stk = kni info tab v stk in
  let kl _ _ ~rstks m = ignore rstks; term_of_fconstr m in
  let klt info tab ~rstks e t = kl info tab ~rstks (mk_clos e t) in
  zip_term kl klt info tab ~rstks (term_of_fconstr v) stk
let whd_val info tab v = kh info tab ~rstks:[] v []

(* strong reduction *)
let norm_term info tab e t = klt info tab ~rstks:[] e t

let create_infos ?univs ?evars i_flags i_env =
  let evars = Option.default (CClosure.default_evar_handler i_env) evars in
  let i_univs = Option.default (Environ.universes i_env) univs in
  let i_share = (Environ.typing_flags i_env).Declarations.share_reduction in
  let i_cache = {i_env; i_sigma = evars; i_share; i_univs} in
  let i_cc_info_beta = CClosure.create_clos_infos ~evars RedFlags.beta i_env in
  let i_cc_tab = CClosure.create_tab () in
  {i_flags; i_relevances = Range.empty; i_cache; i_cc_info_beta; i_cc_tab}

let create_clos_infos = create_infos


(* adapt to restricted interface *)
let norm_term info tab t = norm_term info tab (subs_id 0, UVars.Instance.empty) t
let whd_term info tab t = whd_val info tab (mk_clos (subs_id 0, UVars.Instance.empty) t)


let norm reds env sigma t =
  let evars = Evd.evar_handler sigma in
  let info = create_clos_infos ~evars reds env in
  let tab = create_tab () in
  let t = EConstr.Unsafe.to_constr t in
  let t = norm_term info tab t in
  EConstr.of_constr t

let whd reds env sigma t =
  let evars = Evd.evar_handler sigma in
  let info = create_clos_infos ~evars reds env in
  let tab = create_tab () in
  let t = EConstr.Unsafe.to_constr t in
  let t = whd_val info tab (mk_clos (subs_id 0, UVars.Instance.empty) t) in
  EConstr.of_constr t
