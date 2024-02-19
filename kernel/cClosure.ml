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

type mode = Conversion | Reduction
(* In conversion mode we can introduce FIrrelevant terms.
   Invariants of the conversion mode:
   - the only irrelevant terms as returned by [knr] are either [FIrrelevant],
     [FLambda], [FFlex] or [FRel].
   - the stack never contains irrelevant-producing nodes i.e. [Zproj], [ZFix]
     and [ZcaseT] are all relevant
*)

(**********************************************************************)
(* Lazy reduction: the one used in kernel operations                  *)

(* type of shared terms. fconstr and frterm are mutually recursive.
 * Clone of the constr structure, but completely mutable, and
 * annotated with reduction state (reducible or not).
 *  - FLIFT is a delayed shift; allows sharing between 2 lifted copies
 *    of a given term.
 *  - FCLOS is a delayed substitution applied to a constr
 *  - FLOCKED is used to erase the content of a reference that must
 *    be updated. This is to allow the garbage collector to work
 *    before the term is computed.
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

type gfix = Constr.t option

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
  | FFix of fixpoint * usubs * gfix
  | FCoFix of cofixpoint * usubs
  | FCaseT of case_info * UVars.Instance.t * constr array * case_return * fconstr * case_branch array * usubs (* predicate and branches are closures *)
  | FCaseInvert of case_info * UVars.Instance.t * constr array * case_return * finvert * fconstr * case_branch array * usubs
  | FLambda of int * (Name.t Context.binder_annot * constr) list * constr * usubs
  | FProd of Name.t Context.binder_annot * fconstr * constr * usubs
  | FLetIn of Name.t Context.binder_annot * fconstr * fconstr * constr * usubs
  | FEvar of Evar.t * constr list * usubs * evar_repack
  | FInt of Uint63.t
  | FFloat of Float64.t
  | FArray of UVars.Instance.t * fconstr Parray.t * fconstr
  | FLIFT of int * fconstr
  | FCLOS of constr * usubs
  | FIrrelevant
  | FLOCKED

and usubs = fconstr subs UVars.puniverses

and finvert = fconstr array

let fterm_of v = v.term
let set_ntrl v = v.mark <- Ntrl

let mk_atom c = {mark=Ntrl;term=FAtom c}
let mk_red f = {mark=Red;term=f}

(* Could issue a warning if no is still Red, pointing out that we loose
   sharing. *)
let update v1 mark t =
  v1.mark <- mark; v1.term <- t

type 'a evar_expansion =
| EvarDefined of 'a
| EvarUndefined of Evar.t * 'a list

type 'constr evar_handler = {
  evar_expand : 'constr pexistential -> 'constr evar_expansion;
  evar_repack : Evar.t * 'constr list -> 'constr;
  evar_irrelevant : 'constr pexistential -> bool;
  qvar_irrelevant : Sorts.QVar.t -> bool;
}

let default_evar_handler env = {
  evar_expand = (fun _ -> assert false);
  evar_repack = (fun _ -> assert false);
  evar_irrelevant = (fun _ -> assert false);
  qvar_irrelevant = (fun q ->
      assert (Sorts.QVar.Set.mem q env.env_qualities);
      false);
}

(** Reduction cache *)
type infos_cache = {
  i_env : env;
  i_sigma : constr evar_handler;
  i_share : bool;
  i_univs : UGraph.t;
  i_mode : mode;
}

type clos_infos = {
  i_flags : reds;
  i_relevances : Sorts.relevance Range.t;
  i_cache : infos_cache }

let info_flags info = info.i_flags
let info_env info = info.i_cache.i_env
let info_univs info = info.i_cache.i_univs

let push_relevance infos x =
  { infos with i_relevances = Range.cons x.binder_relevance infos.i_relevances }

let push_relevances infos nas =
  { infos with
    i_relevances =
      Array.fold_left (fun l x -> Range.cons x.binder_relevance l)
        infos.i_relevances nas }

let set_info_relevances info r = { info with i_relevances = r }

let info_relevances info = info.i_relevances

(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *)
type 'a next_native_args = (CPrimitives.arg_kind * 'a) list

type stack_member =
  | Zapp of fconstr array
  | ZcaseT of case_info * UVars.Instance.t * constr array * case_return * case_branch array * usubs
  | Zproj of Projection.Repr.t * Sorts.relevance
  | Zfix of fconstr * stack
  | Zprimitive of CPrimitives.t * pconstant * fconstr list * fconstr next_native_args
       (* operator, constr def, arguments already seen (in rev order), next arguments *)
  | Zshift of int
  | Zupdate of fconstr

and stack = stack_member list

let empty_stack = []
let append_stack v s =
  if Int.equal (Array.length v) 0 then s else
  match s with
  | Zapp l :: s -> Zapp (Array.append v l) :: s
  | (ZcaseT _ | Zproj _ | Zfix _ | Zshift _ | Zupdate _ | Zprimitive _) :: _ | [] ->
    Zapp v :: s

(* Collapse the shifts in the stack *)
let zshift n s =
  match (n,s) with
      (0,_) -> s
    | (_,Zshift(k)::s) -> Zshift(n+k)::s
    | (_,(ZcaseT _ | Zproj _ | Zfix _ | Zapp _ | Zupdate _ | Zprimitive _) :: _) | _,[] -> Zshift(n)::s

let rec stack_args_size = function
  | Zapp v :: s -> Array.length v + stack_args_size s
  | Zshift(_)::s -> stack_args_size s
  | Zupdate(_)::s -> stack_args_size s
  | (ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | [] -> 0

let usubs_shft (n,(e,u)) = subs_shft (n, e), u

(* Lifting. Preserves sharing (useful only for cell with norm=Red).
   lft_fconstr always create a new cell, while lift_fconstr avoids it
   when the lift is 0. *)
let rec lft_fconstr n ft =
  match ft.term with
    | (FInd _|FConstruct _|FFlex(ConstKey _|VarKey _)|FInt _|FFloat _|FIrrelevant) -> ft
    | FRel i -> {mark=ft.mark;term=FRel(i+n)}
    | FLambda(k,tys,f,e) -> {mark=Cstr; term=FLambda(k,tys,f,usubs_shft(n,e))}
    | FFix(fx,e,gfix) ->
      {mark=Cstr; term=FFix(fx,usubs_shft(n,e),gfix)}
    | FCoFix(cfx,e) ->
      {mark=Cstr; term=FCoFix(cfx,usubs_shft(n,e))}
    | FLIFT(k,m) -> lft_fconstr (n+k) m
    | FLOCKED -> assert false
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

(* since the head may be reducible, we might introduce lifts of 0 *)
let compact_stack head stk =
  let rec strip_rec depth = function
    | Zshift(k)::s -> strip_rec (depth+k) s
    | Zupdate(m)::s ->
        (* Be sure to create a new cell otherwise sharing would be
           lost by the update operation *)
        let h' = lft_fconstr depth head in
        (** The stack contains [Zupdate] marks only if in sharing mode *)
        let () = update m h'.mark h'.term in
        strip_rec depth s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zapp _ | Zprimitive _) :: _ | []) as stk -> zshift depth stk
  in
  strip_rec 0 stk

(* Put an update mark in the stack, only if needed *)
let zupdate info m s =
  let share = info.i_cache.i_share in
  if share && is_red m.mark then
    let s' = compact_stack m s in
    let _ = m.term <- FLOCKED in
    Zupdate(m)::s'
  else s

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

(* t must be a FLambda and binding list cannot be empty *)
let destFLambda clos_fun t =
  match [@ocaml.warning "-4"] t.term with
  | FLambda(_,[(na,ty)],b,e) ->
    (usubst_binder e na,clos_fun e ty,clos_fun (usubs_lift e) b)
  | FLambda(n,(na,ty)::tys,b,e) ->
    (usubst_binder e na,clos_fun e ty,{mark=t.mark;term=FLambda(n-1,tys,b,usubs_lift e)})
  | _ -> assert false

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
    | (CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _|Proj _|Array _) ->
        {mark = Red; term = FCLOS(t,e)}

let injectu c u = mk_clos (subs_id 0, u) c

let inject c = injectu c UVars.Instance.empty

let mk_irrelevant = { mark = Cstr; term = FIrrelevant }

let is_irrelevant info r = match info.i_cache.i_mode with
| Reduction -> false
| Conversion -> match r with
  | Sorts.Irrelevant -> true
  | Sorts.RelevanceVar q -> info.i_cache.i_sigma.qvar_irrelevant q
  | Sorts.Relevant -> false

(************************************************************************)

type gfix_info = {
  gfix_nargs : int;
  gfix_tys : (Name.t Context.binder_annot * constr) list;
  gfix_univs : UVars.Instance.t;
  gfix_body : fixpoint;
  gfix_refold : Constr.t;
}

type table_val = (fconstr * gfix_info option, Empty.t) constant_def

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

  let expand_global_fixpoint info cst c = match info.i_cache.i_mode with
  | Conversion -> None
  | Reduction ->
    let ctx, body = Term.decompose_lambda c in
    match destFix body with
    | fix ->
      let nargs = List.length ctx in
      let args = Array.init nargs (fun i -> mkRel (nargs - i)) in
      let inst = UVars.Instance.abstract_instance @@ UVars.Instance.length @@ snd cst in
      let refold = mkApp (mkConstU (fst cst, inst), args) in
      Some {
        gfix_nargs = nargs;
        gfix_tys = List.rev ctx;
        gfix_univs = snd cst;
        gfix_body = fix;
        gfix_refold = refold;
      }
    | exception DestKO -> None

  let value_of info ref =
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
        if TransparentState.is_transparent_constant ts cst then
          let body = constant_value_in u cb.const_body in
          let gfix = expand_global_fixpoint info (cst, u) body in
          Def (injectu body u, gfix)
        else
          raise Not_found
    with
    | Irrelevant -> Def (mk_irrelevant, None)
    | NotEvaluableConst (IsPrimitive (_u,op)) (* Const *) -> Primitive op
    | Not_found (* List.assoc *)
    | NotEvaluableConst _ (* Const *) -> Undef None

  let lookup info tab ref =
    try Table.find tab ref with Not_found ->
    let v = value_of info ref in
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
    | FFix ((op,(lna,tys,bds)) as fx, e, _) ->
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
    | FCoFix ((op,(lna,tys,bds)) as cfx, e) ->
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
    | FLOCKED -> assert (!Flags.in_debugger); mkVar(Id.of_string"_LOCKED_")

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

(* fstrong applies unfreeze_fun recursively on the (freeze) term and
 * yields a term.  Assumes that the unfreeze_fun never returns a
 * FCLOS term.
let rec fstrong unfreeze_fun lfts v =
  to_constr (fstrong unfreeze_fun) lfts (unfreeze_fun v)
*)

let rec zip m stk =
  match stk with
    | [] -> m
    | Zapp args :: s -> zip {mark=neutr m.mark; term=FApp(m, args)} s
    | ZcaseT(ci, u, pms, p, br, e)::s ->
        let t = FCaseT(ci, u, pms, p, m, br, e) in
        let mark = (neutr m.mark) in
        zip {mark; term=t} s
    | Zproj (p,r) :: s ->
        let mark = (neutr m.mark) in
        zip {mark; term=FProj(Projection.make p true,r,m)} s
    | Zfix(fx,par)::s ->
        zip fx (par @ append_stack [|m|] s)
    | Zshift(n)::s ->
        zip (lift_fconstr n m) s
    | Zupdate(rf)::s ->
      (** The stack contains [Zupdate] marks only if in sharing mode *)
        let () = update rf m.mark m.term in
        zip rf s
    | Zprimitive(_op,c,rargs,kargs)::s ->
      let args = List.rev_append rargs (m::List.map snd kargs) in
      let f = {mark = Red; term = FFlex (ConstKey c)} in
      zip {mark=(neutr m.mark); term = FApp (f, Array.of_list args)} s

let fapp_stack (m,stk) = zip m stk

let term_of_process c stk = term_of_fconstr (zip c stk)

(*********************************************************************)

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
        strip_rec (Zapp args :: rstk)
          {mark=h.mark;term=FApp(h,args)} depth s
    | Zupdate(m)::s ->
      (** The stack contains [Zupdate] marks only if in sharing mode *)
        let () = update m h.mark h.term in
        strip_rec rstk m depth s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as stk ->
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
    | Zupdate(m)::s ->
        (** The stack contains [Zupdate] mark only if in sharing mode *)
        let () = update m h.mark h.term in
        strip_rec rstk m n s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as s -> (None, List.rev rstk @ s) in
  strip_rec [] head n stk

let usubs_cons x (s,u) = subs_cons x s, u

let rec subs_consn v i n s =
  if Int.equal i n then s
  else subs_consn v (i + 1) n (subs_cons v.(i) s)

let usubs_consn v i n s = on_fst (subs_consn v i n) s

let usubs_consv v s =
  usubs_consn v 0 (Array.length v) s

(* Beta reduction: look for an applied argument in the stack.
   Since the encountered update marks are removed, h must be a whnf *)
let rec get_args n tys f e = function
    | Zupdate r :: s ->
        (** The stack contains [Zupdate] mark only if in sharing mode *)
        let () = update r Cstr (FLambda(n,tys,f,e)) in
        get_args n tys f e s
    | Zshift k :: s ->
        get_args n tys f (usubs_shft (k,e)) s
    | Zapp l :: s ->
        let na = Array.length l in
        if n == na then (Inl (usubs_consn l 0 na e), s)
        else if n < na then (* more arguments *)
          let eargs = Array.sub l n (na-n) in
          (Inl (usubs_consn l 0 n e), Zapp eargs :: s)
        else (* more lambdas *)
          let etys = List.skipn na tys in
          get_args (n-na) etys f (usubs_consn l 0 na e) s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as stk ->
      (Inr {mark=Cstr; term=FLambda(n,tys,f,e)}, stk)

(* Eta expansion: add a reference to implicit surrounding lambda at end of stack *)
let rec eta_expand_stack info na = function
  | (Zapp _ | Zfix _ | ZcaseT _ | Zproj _
        | Zshift _ | Zupdate _ | Zprimitive _ as e) :: s ->
      e :: eta_expand_stack info na s
  | [] ->
    let arg =
      if is_irrelevant info na.binder_relevance then mk_irrelevant
      else {mark = Ntrl; term = FRel 1}
    in
    [Zshift 1; Zapp [|arg|]]

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
    | Zupdate(m) :: s ->
      let () = update m h.mark h.term in
      strip_rec rnargs m depth  kargs s
    | (Zprimitive _ | ZcaseT _ | Zproj _ | Zfix _) :: _ | [] -> assert false
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
  | ((ZcaseT _ | Zproj _ | Zfix _ | Zupdate _ | Zprimitive _) :: _ | []) as stk -> stk

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
    | (ZcaseT _ | Zproj _ | Zfix _ | Zupdate _ | Zprimitive _) :: _ -> assert false
        (* strip_update_shift_app only produces Zapp and Zshift items *)

let drop_parameters depth n argstk =
  try try_drop_parameters depth n argstk
  with Not_found ->
  (* we know that n < stack_args_size(argstk) (if well-typed term) *)
  anomaly (Pp.str "ill-typed term: found a match on a partially applied constructor.")

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
    let rec push e stk = match stk with
    | [] -> e
    | Zapp v :: stk -> push (usubs_consv v e) stk
    | (Zshift _ | ZcaseT _ | Zproj _ | Zfix _ | Zupdate _ | Zprimitive _) :: _ ->
      assert false
    in
    let e = push e args in
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
    | Zshift _ | ZcaseT _ | Zproj _ | Zfix _ | Zupdate _ | Zprimitive _ ->
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

(** [eta_expand_ind_stack env ind c s t] computes stacks corresponding
    to the conversion of the eta expansion of t, considered as an inhabitant
    of ind, and the Constructor c of this inductive type applied to arguments
    s.
    @assumes [t] is an irreducible term, and not a constructor. [ind] is the inductive
    of the constructor term [c]
    @raise Not_found if the inductive is not a primitive record, or if the
    constructor is partially applied.
 *)
let eta_expand_ind_stack env (ind,u) m s (f, s') =
  let open Declarations in
  let mib = lookup_mind (fst ind) env in
  (* disallow eta-exp for non-primitive records *)
  if not (mib.mind_finite == BiFinite) then raise Not_found;
  match Declareops.inductive_make_projections ind mib with
  | Some projs ->
    (* (Construct, pars1 .. parsm :: arg1...argn :: []) ~= (f, s') ->
           arg1..argn ~= (proj1 t...projn t) where t = zip (f,s') *)
    let pars = mib.Declarations.mind_nparams in
    let right = fapp_stack (f, s') in
    let (depth, args, _s) = strip_update_shift_app m s in
    (** Try to drop the params, might fail on partially applied constructors. *)
    let argss = try_drop_parameters depth pars args in
    let hstack = Array.map (fun (p,r) ->
        { mark = Red; (* right can't be a constructor though *)
          term = FProj (Projection.make p true, UVars.subst_instance_relevance u r, right) })
        projs
    in
    argss, [Zapp hstack]
  | None -> raise Not_found (* disallow eta-exp for non-primitive records *)

let rec project_nth_arg n = function
  | Zapp args :: s ->
      let q = Array.length args in
        if n >= q then project_nth_arg (n - q) s
        else (* n < q *) args.(n)
  | (ZcaseT _ | Zproj _ | Zfix _ | Zupdate _ | Zshift _ | Zprimitive _) :: _ | [] -> assert false
      (* After drop_parameters we have a purely applicative stack *)

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
      | FFix (((reci,i),(_,_,bds as rdcl)),env, None) ->
          (bds.(i),
           (fun j -> { mark = Cstr;
                       term = FFix (((reci,j),rdcl),env, None) }),
           env, Array.length bds)
      | FFix (((reci,i),(_,_,bds as rdcl)),env, Some refold) -> (* FIXME *)
          (bds.(i),
           (fun j -> if Int.equal i j then
              { mark = Cstr; term = FCLOS (refold, env) }
            else { mark = Cstr;
                       term = FFix (((reci,j),rdcl),env, None) }),
           env, Array.length bds)
      | FCoFix ((i,(_,_,bds as rdcl)),env) ->
          (bds.(i),
           (fun j -> { mark = Cstr;
                       term = FCoFix ((j,rdcl),env) }),
           env, Array.length bds)
      | _ -> assert false
  in
  let rec mk_subs env i =
    if Int.equal i nfix then env
    else mk_subs (subs_cons (make_body i) env) (i + 1)
  in
  (on_fst (fun env -> mk_subs env 0) env, thisbody)

let unfold_projection info p r =
  if red_projection info.i_flags p
  then
    Some (Zproj (Projection.repr p, r))
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
| Zupdate m :: s ->
  (** The stack contains [Zupdate] marks only if in sharing mode *)
  let () = update m mk_irrelevant.mark mk_irrelevant.term in
  skip_irrelevant_stack info s

let is_irrelevant_constructor infos ((ind,_),u) =
  match Indmap_env.find_opt ind (info_env infos).Environ.irr_inds with
  | None -> false
  | Some r ->
    is_irrelevant infos @@ UVars.subst_instance_relevance u r

(*********************************************************************)
(* A machine that inspects the head of a term until it finds an
   atom or a subterm that may produce a redex (abstraction,
   constructor, cofix, letin, constant), or a neutral term (product,
   inductive) *)
let rec knh info m stk =
  match m.term with
    | FLIFT(k,a) -> knh info a (zshift k stk)
    | FCLOS(t,e) -> knht info e t (zupdate info m stk)
    | FLOCKED -> assert false
    | FApp(a,b) -> knh info a (append_stack b (zupdate info m stk))
    | FCaseT(ci,u,pms,(_,r as p),t,br,e) ->
      let r' = usubst_relevance e r in
      if is_irrelevant info r' then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        knh info t (ZcaseT(ci,u,pms,p,br,e)::zupdate info m stk)
    | FFix (((ri, n), (lna, _, _)), e, _) ->
      if is_irrelevant info (usubst_relevance e (lna.(n)).binder_relevance) then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        (match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh info arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FProj (p,r,c) ->
      if is_irrelevant info r then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
      (match unfold_projection info p r with
       | None -> (m, stk)
       | Some s -> knh info c (s :: zupdate info m stk))

(* cases where knh stops *)
    | (FFlex _|FLetIn _|FConstruct _|FEvar _|FCaseInvert _|FIrrelevant|
       FCoFix _|FLambda _|FRel _|FAtom _|FInd _|FProd _|FInt _|FFloat _|FArray _) ->
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
        knh info { mark = Cstr; term = FFix (fx, e, None) } stk
    | Cast(a,_,_) -> knht info e a stk
    | Rel n -> knh info (clos_rel (fst e) n) stk
    | Proj (p, r, c) ->
      let r = usubst_relevance e r in
      if is_irrelevant info r then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else begin match unfold_projection info p r with
      | None -> ({ mark = Red; term = FProj (p, r, mk_clos e c) }, stk)
      | Some s -> knht info e c (s :: stk)
      end
    | (Ind _|Const _|Construct _|Var _|Meta _ | Sort _ | Int _|Float _) -> (mk_clos e t, stk)
    | CoFix cfx ->
      { mark = Cstr; term = FCoFix (cfx,e) }, stk
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
let set_conv f = conv := f

(* Computes a weak head normal form from the result of knh. *)
let rec knr info tab m stk =
  match m.term with
  | FLambda(n,tys,f,e) when red_set info.i_flags fBETA ->
      (match get_args n tys f e stk with
          Inl e', s -> knit info tab e' f s
        | Inr lam, s -> (lam,s))
  | FFlex fl when red_set info.i_flags fDELTA ->
      (match Table.lookup info tab fl with
        | Def (v, None) -> kni info tab v stk
        | Def (v, Some gfix) ->
          if Int.equal gfix.gfix_nargs 0 then
              let refold = Some gfix.gfix_refold in
              kni info tab { mark = Cstr; term = FFix (gfix.gfix_body, (subs_id 0, gfix.gfix_univs), refold) } stk
          else if red_set info.i_flags fBETA then
            match get_args gfix.gfix_nargs gfix.gfix_tys (mkFix gfix.gfix_body) (subs_id 0, gfix.gfix_univs) stk with
            | Inl e, stk ->
              let refold = Some gfix.gfix_refold in
              kni info tab { mark = Cstr; term = FFix (gfix.gfix_body, e, refold) } stk
            | Inr lam, stk -> (lam, stk)
          else kni info tab v stk
        | Primitive op ->
          if check_native_args op stk then
            let c = match fl with ConstKey c -> c | RelKey _ | VarKey _ -> assert false in
            let rargs, a, nargs, stk = get_native_args1 op c stk in
            kni info tab a (Zprimitive(op,c,rargs,nargs)::stk)
          else
            (* Similarly to fix, partially applied primitives are not Ntrl! *)
            (m, stk)
        | Undef _ | OpaqueDef _ -> (set_ntrl m; (m,stk)))
  | FConstruct c ->
     let use_match = red_set info.i_flags fMATCH in
     let use_fix = red_set info.i_flags fFIX in
     if use_match || use_fix then
      (match [@ocaml.warning "-4"] strip_update_shift_app m stk with
        | (depth, args, ZcaseT(ci,_,pms,_,br,e)::s) when use_match ->
            assert (ci.ci_npar>=0);
            (* instance on the case and instance on the constructor are compatible by typing *)
            let (br, e) = get_branch info depth ci pms c br e args in
            knit info tab e br s
        | (_, cargs, Zfix(fx,par)::s) when use_fix ->
            let rarg = fapp_stack(m,cargs) in
            let stk' = par @ append_stack [|rarg|] s in
            let (fxe,fxbd) = contract_fix_vect fx.term in
            knit info tab fxe fxbd stk'
        | (depth, args, Zproj (p,_)::s) when use_match ->
            let rargs = drop_parameters depth (Projection.Repr.npars p) args in
            let rarg = project_nth_arg (Projection.Repr.arg p) rargs in
            kni info tab rarg s
        | (_,args,s) ->
          if is_irrelevant_constructor info c then (mk_irrelevant, skip_irrelevant_stack info stk) else (m,args@s))
     else if is_irrelevant_constructor info c then
      (mk_irrelevant, skip_irrelevant_stack info stk)
     else
      (m, stk)
  | FCoFix ((i, (lna, _, _)), e) ->
    if is_irrelevant info (usubst_relevance e (lna.(i)).binder_relevance) then
      (mk_irrelevant, skip_irrelevant_stack info stk)
    else if red_set info.i_flags fCOFIX then
      (match strip_update_shift_app m stk with
        | (_, args, (((ZcaseT _|Zproj _)::_) as stk')) ->
            let (fxe,fxbd) = contract_fix_vect m.term in
            knit info tab fxe fxbd (args@stk')
        | (_,args, ((Zapp _ | Zfix _ | Zshift _ | Zupdate _ | Zprimitive _) :: _ | [] as s)) -> (m,args@s))
    else (m, stk)
  | FLetIn (_,v,_,bd,e) when red_set info.i_flags fZETA ->
      knit info tab (on_fst (subs_cons v) e) bd stk
  | FInt _ | FFloat _ | FArray _ ->
    (match [@ocaml.warning "-4"] strip_update_shift_app m stk with
     | (_, _, Zprimitive(op,(_,u as c),rargs,nargs)::s) ->
       let (rargs, nargs) = skip_native_args (m::rargs) nargs in
       begin match nargs with
         | [] ->
           let args = Array.of_list (List.rev rargs) in
           begin match FredNative.red_prim (info_env info) () op u args with
            | Some m -> kni info tab m s
            | None -> assert false
           end
         | (kd,a)::nargs ->
           assert (kd = CPrimitives.Kwhnf);
           kni info tab a (Zprimitive(op,c,rargs,nargs)::s)
             end
     | (_, _, s) -> (m, s))
  | FCaseInvert (ci, u, pms, _p,iv,_c,v,env) when red_set info.i_flags fMATCH ->
    let pms = mk_clos_vect env pms in
    let u = usubst_instance env u in
    begin match case_inversion info tab ci u pms iv v with
      | Some c -> knit info tab env c stk
      | None -> (m, stk)
    end
  | FIrrelevant ->
    let stk = skip_irrelevant_stack info stk in
    (m, stk)
  | FProd _ | FAtom _ | FInd _ (* relevant statically *)
  | FCaseInvert _ | FProj _ | FFix _ | FEvar _ (* relevant because of knh(t) *)
  | FLambda _ | FFlex _ | FRel _ (* irrelevance handled by conversion *)
  | FLetIn _ (* only happens in reduction mode *) ->
    (m, stk)
  | FLOCKED | FCLOS _ | FApp _ | FCaseT _ | FLIFT _ ->
    (* ruled out by knh(t) *)
    assert false

(* Computes the weak head normal form of a term *)
and kni info tab m stk =
  let (hm,s) = knh info m stk in
  knr info tab hm s
and knit info tab e t stk =
  let (ht,s) = knht info e t stk in
  knr info tab ht s

and case_inversion info tab ci u params indices v =
  let open Declarations in
  (* No binders / lets at all in the unique branch *)
  let v = match v with
  | [| [||], v |] -> v
  | _ -> assert false
  in
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
    let tab = if info.i_cache.i_mode == Conversion then tab else Table.create () in
    let info = {info with i_cache = { info.i_cache with i_mode = Conversion}; i_flags=all} in
    let check_index i index =
      let expected = expect_args.(ci.ci_npar + i) in
      let expected = mk_clos (psubst,u) expected in
      !conv info tab expected index
    in
    if Array.for_all_i check_index 0 indices
    then Some v else None

let kh info tab v stk = fapp_stack(kni info tab v stk)

(************************************************************************)

(* Computes the strong normal form of a term.
   1- Calls kni
   2- tries to rebuild the term. If a closure still has to be computed,
      calls itself recursively. *)

let is_val v = match v.term with
| FAtom _ | FRel _   | FInd _ | FConstruct _ | FInt _ | FFloat _ -> true
| FFlex _ -> v.mark == Ntrl
| FApp _ | FProj _ | FFix _ | FCoFix _ | FCaseT _ | FCaseInvert _ | FLambda _
| FProd _ | FLetIn _ | FEvar _ | FArray _ | FLIFT _ | FCLOS _ -> false
| FIrrelevant | FLOCKED -> assert false

let rec kl info tab m =
  let share = info.i_cache.i_share in
  if is_val m then term_of_fconstr m
  else
    let (nm,s) = kni info tab m [] in
    let () = if share then ignore (fapp_stack (nm, s)) in (* to unlock Zupdates! *)
    zip_term info tab (norm_head info tab nm) s

and klt info tab e t = match kind t with
| Rel i ->
  begin match expand_rel i (fst e) with
  | Inl (n, mt) -> kl info tab @@ lift_fconstr n mt
  | Inr (k, None) -> if Int.equal k i then t else mkRel k
  | Inr (k, Some p) -> kl info tab @@ lift_fconstr (k-p) {mark=Red;term=FFlex(RelKey p)}
  end
| App (hd, args) ->
  begin match kind hd with
  | Ind _ | Construct _ ->
    let args' = Array.Smart.map (fun c -> klt info tab e c) args in
    let hd' = subst_instance_constr (snd e) hd in
    if hd' == hd && args' == args then t
    else mkApp (hd', args')
  | Var _ | Const _ | CoFix _ | Lambda _ | Fix _ | Prod _ | Evar _ | Case _
  | Cast _ | LetIn _ | Proj _ | Array _ | Rel _ | Meta _ | Sort _ | Int _ | Float _ ->
    let share = info.i_cache.i_share in
    let (nm,s) = knit info tab e t [] in
    let () = if share then ignore (fapp_stack (nm, s)) in (* to unlock Zupdates! *)
    zip_term info tab (norm_head info tab nm) s
  | App _ -> assert false
  end
| Lambda (na, u, c) ->
  let na' = usubst_binder e na in
  let u' = klt info tab e u in
  let c' = klt (push_relevance info na') tab (usubs_lift e) c in
  if na' == na && u' == u && c' == c then t
  else mkLambda (na', u', c')
| Prod (na, u, v) ->
  let na' = usubst_binder e na in
  let u' = klt info tab e u in
  let v' = klt (push_relevance info na') tab (usubs_lift e) v in
  if na' == na && u' == u && v' == v then t
  else mkProd (na', u', v')
| Cast (t, _, _) -> klt info tab e t
| Var _ | Const _ | CoFix _ | Fix _ | Evar _ | Case _ | LetIn _ | Proj _ | Array _ ->
  let share = info.i_cache.i_share in
  let (nm,s) = knit info tab e t [] in
  let () = if share then ignore (fapp_stack (nm, s)) in (* to unlock Zupdates! *)
  zip_term info tab (norm_head info tab nm) s
| Meta _ | Sort _ | Ind _ | Construct _ | Int _ | Float _ -> subst_instance_constr (snd e) t

(* no redex: go up for atoms and already normalized terms, go down
   otherwise. *)
and norm_head info tab m =
  if is_val m then term_of_fconstr m else
    match m.term with
      | FLambda(_n,tys,f,e) ->
        let fold (e, info, ctxt) (na, ty) =
          let na = usubst_binder e na in
          let ty = klt info tab e ty in
          let info = push_relevance info na in
          (usubs_lift e, info, (na, ty) :: ctxt)
        in
        let (e', info, rvtys) = List.fold_left fold (e,info,[]) tys in
        let bd = klt info tab e' f in
        List.fold_left (fun b (na,ty) -> mkLambda(na,ty,b)) bd rvtys
      | FLetIn(na,a,b,f,e) ->
          let na = usubst_binder e na in
          let c = klt (push_relevance info na) tab (usubs_lift e) f in
          mkLetIn(na, kl info tab a, kl info tab b, c)
      | FProd(na,dom,rng,e) ->
        let na = usubst_binder e na in
        let rng = klt (push_relevance info na) tab (usubs_lift e) rng in
          mkProd(na, kl info tab dom, rng)
      | FCoFix((n,(na,tys,bds)),e) ->
          let na = Array.Smart.map (usubst_binder e) na in
          let infobd = push_relevances info na in
          let ftys = Array.map (fun ty -> klt info tab e ty) tys in
          let fbds = Array.map (fun bd -> klt infobd tab (usubs_liftn (Array.length na) e) bd) bds in
          mkCoFix (n, (na, ftys, fbds))
      | FFix((n,(na,tys,bds)), e, _) ->
          let na = Array.Smart.map (usubst_binder e) na in
          let infobd = push_relevances info na in
          let ftys = Array.map (fun ty -> klt info tab e ty) tys in
          let fbds = Array.map (fun bd -> klt infobd tab (usubs_liftn (Array.length na) e) bd) bds in
          mkFix (n, (na, ftys, fbds))
      | FEvar(ev, args, env, repack) ->
          repack (ev, List.map (fun a -> klt info tab env a) args)
      | FProj (p,r,c) ->
        mkProj (p, r, kl info tab c)
      | FArray (u, a, ty) ->
        let a, def = Parray.to_array a in
        let a = Array.map (kl info tab) a in
        let def = kl info tab def in
        let ty = kl info tab ty in
        mkArray (u, a, def, ty)
      | FLOCKED | FRel _ | FAtom _ | FFlex _ | FInd _ | FConstruct _
      | FApp _ | FCaseT _ | FCaseInvert _ | FLIFT _ | FCLOS _ | FInt _
      | FFloat _ -> term_of_fconstr m
      | FIrrelevant -> assert false (* only introduced when converting *)

and zip_term info tab m stk = match stk with
| [] -> m
| Zapp args :: s ->
    zip_term info tab (mkApp(m, Array.map (kl info tab) args)) s
| ZcaseT(ci, u, pms, (p,r), br, e) :: s ->
  let zip_ctx (nas, c) =
      let nas = Array.map (usubst_binder e) nas in
      let e = usubs_liftn (Array.length nas) e in
      (nas, klt info tab e c)
    in
    let r = usubst_relevance e r in
    let u = usubst_instance e u in
    let t = mkCase(ci, u, Array.map (fun c -> klt info tab e c) pms, (zip_ctx p, r),
      NoInvert, m, Array.map zip_ctx br) in
    zip_term info tab t s
| Zproj (p,r)::s ->
    let t = mkProj (Projection.make p true, r, m) in
    zip_term info tab t s
| Zfix(fx,par)::s ->
    let h = mkApp(zip_term info tab (kl info tab fx) par,[|m|]) in
    zip_term info tab h s
| Zshift(n)::s ->
    zip_term info tab (lift n m) s
| Zupdate(_rf)::s ->
    zip_term info tab m s
| Zprimitive(_,c,rargs, kargs)::s ->
    let kargs = List.map (fun (_,a) -> kl info tab a) kargs in
    let args =
      List.fold_left (fun args a -> kl info tab a ::args) (m::kargs) rargs in
    let h = mkApp (mkConstU c, Array.of_list args) in
    zip_term info tab h s

(* Initialization and then normalization *)

(* weak reduction *)
let whd_val info tab v = term_of_fconstr (kh info tab v [])

(* strong reduction *)
let norm_val info tab v = kl info tab v
let norm_term info tab e t = klt info tab e t

let whd_stack infos tab m stk = match m.mark with
| Ntrl ->
  (** No need to perform [kni] nor to unlock updates because
      every head subterm of [m] is [Ntrl] *)
  knh infos m stk
| Red | Cstr ->
  let k = kni infos tab m stk in
  let () =
    if infos.i_cache.i_share then
      (* to unlock Zupdates! *)
      let (m', stk') = k in
      if not (m == m' && stk == stk') then ignore (zip m' stk')
  in
  k

let create_infos i_mode ?univs ?evars i_flags i_env =
  let evars = Option.default (default_evar_handler i_env) evars in
  let i_univs = Option.default (Environ.universes i_env) univs in
  let i_share = (Environ.typing_flags i_env).Declarations.share_reduction in
  let i_cache = {i_env; i_sigma = evars; i_share; i_univs; i_mode} in
  {i_flags; i_relevances = Range.empty; i_cache}

let create_conv_infos = create_infos Conversion
let create_clos_infos = create_infos Reduction

let oracle_of_infos infos = Environ.oracle infos.i_cache.i_env

let infos_with_reds infos reds =
  { infos with i_flags = reds }

let unfold_ref_with_args infos tab fl v =
  match Table.lookup infos tab fl with
  | Def (def, None) -> Some (def, v)
  | Def (def, Some gfix) ->
    if Int.equal gfix.gfix_nargs 0 then
      let refold = Some gfix.gfix_refold in
      Some ({ mark = Cstr; term = FFix (gfix.gfix_body, (subs_id 0, gfix.gfix_univs), refold) }, v)
    else if red_set infos.i_flags fBETA then
      match get_args gfix.gfix_nargs gfix.gfix_tys (mkFix gfix.gfix_body) (subs_id 0, gfix.gfix_univs) v with
      | Inl e, stk ->
        let refold = Some gfix.gfix_refold in
        Some ({ mark = Cstr; term = FFix (gfix.gfix_body, e, refold) }, stk)
      | Inr _, _ -> Some (def, v)
    else Some (def, v)
  | Primitive op when check_native_args op v ->
    let c = match [@ocaml.warning "-4"] fl with ConstKey c -> c | _ -> assert false in
    let rargs, a, nargs, v = get_native_args1 op c v in
    Some (a, (Zupdate a::(Zprimitive(op,c,rargs,nargs)::v)))
  | Undef _ | OpaqueDef _ | Primitive _ -> None
