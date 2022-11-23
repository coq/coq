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
open Pp
open Names
open Constr
open Declarations
open Context
open Environ
open Vars
open Esubst

module RelDecl = Context.Rel.Declaration

let stats = ref false

(* Profiling *)
let beta = ref 0
let delta = ref 0
let zeta = ref 0
let evar = ref 0
let nb_match = ref 0
let fix = ref 0
let cofix = ref 0
let prune = ref 0

let reset () =
  beta := 0; delta := 0; zeta := 0; evar := 0; nb_match := 0; fix := 0;
  cofix := 0; evar := 0; prune := 0

let stop() =
  Feedback.msg_debug (str "[Reds: beta=" ++ int !beta ++ str" delta=" ++ int !delta ++
         str" zeta=" ++ int !zeta ++ str" evar=" ++
         int !evar ++ str" match=" ++ int !nb_match ++ str" fix=" ++ int !fix ++
         str " cofix=" ++ int !cofix ++ str" prune=" ++ int !prune ++
         str"]")

let incr_cnt red cnt =
  if red then begin
    if !stats then incr cnt;
    true
  end else
    false

let with_stats c =
  if !stats then begin
    reset();
    let r = Lazy.force c in
    stop();
    r
  end else
    Lazy.force c

let all_opaque = TransparentState.empty

module type RedFlagsSig = sig
  type reds
  type red_kind
  val fBETA : red_kind
  val fDELTA : red_kind
  val fMATCH : red_kind
  val fFIX : red_kind
  val fCOFIX : red_kind
  val fZETA : red_kind
  val fCONST : Constant.t -> red_kind
  val fVAR : Id.t -> red_kind
  val no_red : reds
  val red_add : reds -> red_kind -> reds
  val red_sub : reds -> red_kind -> reds
  val red_add_transparent : reds -> TransparentState.t -> reds
  val red_transparent : reds -> TransparentState.t
  val mkflags : red_kind list -> reds
  val mkfullflags : red_kind list -> reds
  val red_set : reds -> red_kind -> bool
  val red_projection : reds -> Projection.t -> bool
end

module RedFlags : RedFlagsSig = struct

  (* [r_const=(true,cl)] means all constants but those in [cl] *)
  (* [r_const=(false,cl)] means only those in [cl] *)
  (* [r_delta=true] just mean [r_const=(true,[])] *)

  open TransparentState

  type reds = {
    r_beta : bool;
    r_delta : bool;
    r_const : TransparentState.t;
    r_zeta : bool;
    r_match : bool;
    r_fix : bool;
    r_cofix : bool }

  type red_kind = BETA | DELTA | MATCH | FIX
              | COFIX | ZETA
              | CONST of Constant.t | VAR of Id.t
  let fBETA = BETA
  let fDELTA = DELTA
  let fMATCH = MATCH
  let fFIX = FIX
  let fCOFIX = COFIX
  let fZETA = ZETA
  let fCONST kn  = CONST kn
  let fVAR id  = VAR id
  let no_red = {
    r_beta = false;
    r_delta = false;
    r_const = all_opaque;
    r_zeta = false;
    r_match = false;
    r_fix = false;
    r_cofix = false }

  let red_add red = function
    | BETA -> { red with r_beta = true }
    | DELTA -> { red with r_delta = true }
    | CONST kn ->
      let r = red.r_const in
      { red with r_const = { r with tr_cst = Cpred.add kn r.tr_cst } }
    | MATCH -> { red with r_match = true }
    | FIX -> { red with r_fix = true }
    | COFIX -> { red with r_cofix = true }
    | ZETA -> { red with r_zeta = true }
    | VAR id ->
      let r = red.r_const in
      { red with r_const = { r with tr_var = Id.Pred.add id r.tr_var } }

  let red_sub red = function
    | BETA -> { red with r_beta = false }
    | DELTA -> { red with r_delta = false }
    | CONST kn ->
      let r = red.r_const in
      { red with r_const = { r with tr_cst = Cpred.remove kn r.tr_cst } }
    | MATCH -> { red with r_match = false }
    | FIX -> { red with r_fix = false }
    | COFIX -> { red with r_cofix = false }
    | ZETA -> { red with r_zeta = false }
    | VAR id ->
      let r = red.r_const in
      { red with r_const = { r with tr_var = Id.Pred.remove id r.tr_var } }

  let red_transparent red = red.r_const

  let red_add_transparent red tr =
    { red with r_const = tr }

  let mkflags = List.fold_left red_add no_red

  let mkfullflags = List.fold_left red_add { no_red with r_const = TransparentState.full }

  let red_set red = function
    | BETA -> incr_cnt red.r_beta beta
    | CONST kn ->
      let c = is_transparent_constant red.r_const kn in
        incr_cnt c delta
    | VAR id -> (* En attendant d'avoir des kn pour les Var *)
      let c = is_transparent_variable red.r_const id in
        incr_cnt c delta
    | ZETA -> incr_cnt red.r_zeta zeta
    | MATCH -> incr_cnt red.r_match nb_match
    | FIX -> incr_cnt red.r_fix fix
    | COFIX -> incr_cnt red.r_cofix cofix
    | DELTA -> (* Used for Rel/Var defined in context *)
        incr_cnt red.r_delta delta

  let red_projection red p =
    if Projection.unfolded p then true
    else red_set red (fCONST (Projection.constant p))

end

open RedFlags

let all = mkfullflags [fBETA;fDELTA;fZETA;fMATCH;fFIX;fCOFIX]
let allnolet = mkfullflags [fBETA;fDELTA;fMATCH;fFIX;fCOFIX]
let beta = mkflags [fBETA]
let betadeltazeta = mkfullflags [fBETA;fDELTA;fZETA]
let betaiota = mkflags [fBETA;fMATCH;fFIX;fCOFIX]
let betaiotazeta = mkflags [fBETA;fMATCH;fFIX;fCOFIX;fZETA]
let betazeta = mkflags [fBETA;fZETA]
let delta = mkfullflags [fDELTA]
let zeta = mkflags [fZETA]
let nored = no_red

(* Flags of reduction and cache of constants: 'a is a type that may be
 * mapped to constr. 'a infos implements a cache for constants and
 * abstractions, storing a representation (of type 'a) of the body of
 * this constant or abstraction.
 *  * i_tab is the cache table of the results
 *
 * ref_value_cache searches in the tab, otherwise uses i_repr to
 * compute the result and store it in the table. If the constant can't
 * be unfolded, returns None, but does not store this failure.  * This
 * doesn't take the RESET into account. You mustn't keep such a table
 * after a Reset.  * This type is not exported. Only its two
 * instantiations (cbv or lazy) are.
 *)

type table_key = Constant.t Univ.puniverses tableKey

let eq_pconstant_key (c,u) (c',u') =
  eq_constant_key c c' && Univ.Instance.equal u u'

module IdKeyHash =
struct
  open Hashset.Combine
  type t = table_key
  let equal = Names.eq_table_key eq_pconstant_key
  let hash = function
  | ConstKey (c, _) -> combinesmall 1 (Constant.UserOrd.hash c)
  | VarKey id -> combinesmall 2 (Id.hash id)
  | RelKey i -> combinesmall 3 (Int.hash i)
end

module KeyTable = Hashtbl.Make(IdKeyHash)

open Context.Named.Declaration

exception Irrelevant

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

(* Ntrl means the term is fully normalized and cannot create a redex
     when substituted
   Cstr means the term is in head normal form and that it can
     create a redex when substituted (i.e. constructor, fix, lambda)
   Whnf means we reached the head normal form and that it cannot
     create a redex when substituted
   Red is used for terms that might be reduced
*)
type red_state = Ntrl | Cstr | Whnf | Red

let neutr = function
  | Whnf|Ntrl -> Whnf
  | Red|Cstr -> Red

module Mark : sig

  type t

  val mark : red_state -> t
  val red_state : t -> red_state

  val neutr : t -> t

  val set_ntrl : t -> t

end = struct
  type t = red_state

  let[@inline] mark state = state

  let[@inline] red_state x = x

  let neutr = neutr

  let[@inline] set_ntrl _ = Ntrl
end
let mark = Mark.mark

type fconstr = {
  mutable mark : Mark.t;
  mutable term: fterm;
}

and fterm =
  | FRel of int
  | FAtom of constr (* Metas and Sorts *)
  | FFlex of table_key
  | FInd of pinductive
  | FConstruct of pconstructor
  | FApp of fconstr * fconstr array
  | FProj of Projection.t * fconstr
  | FFix of fixpoint * fconstr subs
  | FCoFix of cofixpoint * fconstr subs
  | FCaseT of case_info * Univ.Instance.t * constr array * case_return * fconstr * case_branch array * fconstr subs (* predicate and branches are closures *)
  | FCaseInvert of case_info * Univ.Instance.t * constr array * case_return * finvert * fconstr * case_branch array * fconstr subs
  | FLambda of int * (Name.t Context.binder_annot * constr) list * constr * fconstr subs
  | FProd of Name.t Context.binder_annot * fconstr * constr * fconstr subs
  | FLetIn of Name.t Context.binder_annot * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential * fconstr subs
  | FInt of Uint63.t
  | FFloat of Float64.t
  | FArray of Univ.Instance.t * fconstr Parray.t * fconstr
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs
  | FIrrelevant
  | FLOCKED

and finvert = fconstr array

let fterm_of v = v.term
let set_ntrl v = v.mark <- Mark.set_ntrl v.mark
let is_val v = match Mark.red_state v.mark with Ntrl -> true | Cstr | Whnf | Red -> false

let mk_atom c = {mark=mark Ntrl;term=FAtom c}
let mk_red f = {mark=mark Red;term=f}

(* Could issue a warning if no is still Red, pointing out that we loose
   sharing. *)
let update ~share v1 mark t =
  if share then
    (v1.mark <- mark;
     v1.term <- t;
     v1)
  else {mark;term=t;}

(** Reduction cache *)

type infos_cache = {
  i_env : env;
  i_sigma : existential -> constr option;
  i_share : bool;
  i_univs : UGraph.t;
  i_mode : mode;
}

type clos_infos = {
  i_flags : reds;
  i_relevances : Sorts.relevance Range.t;
  i_cache : infos_cache }

type clos_tab = (fconstr, Empty.t) constant_def KeyTable.t

let info_flags info = info.i_flags
let info_env info = info.i_cache.i_env
let info_univs info = info.i_cache.i_univs

let push_relevance infos r =
  { infos with i_relevances = Range.cons r.Context.binder_relevance infos.i_relevances }

let push_relevances infos nas =
  { infos with i_relevances = Array.fold_left (fun l x -> Range.cons x.Context.binder_relevance l)
                   infos.i_relevances nas }

let set_info_relevances info r = { info with i_relevances = r }

let info_relevances info = info.i_relevances

(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *)
type 'a next_native_args = (CPrimitives.arg_kind * 'a) list

type stack_member =
  | Zapp of fconstr array
  | ZcaseT of case_info * Univ.Instance.t * constr array * case_return * case_branch array * fconstr subs
  | Zproj of Projection.Repr.t
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

(* Lifting. Preserves sharing (useful only for cell with norm=Red).
   lft_fconstr always create a new cell, while lift_fconstr avoids it
   when the lift is 0. *)
let rec lft_fconstr n ft =
  match ft.term with
    | (FInd _|FConstruct _|FFlex(ConstKey _|VarKey _)|FInt _|FFloat _|FIrrelevant) -> ft
    | FRel i -> {mark=ft.mark;term=FRel(i+n)}
    | FLambda(k,tys,f,e) -> {mark=mark Cstr; term=FLambda(k,tys,f,subs_shft(n,e))}
    | FFix(fx,e) ->
      {mark=mark Cstr; term=FFix(fx,subs_shft(n,e))}
    | FCoFix(cfx,e) ->
      {mark=mark Cstr; term=FCoFix(cfx,subs_shft(n,e))}
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
    | Inr(k,None) -> {mark=mark Ntrl; term= FRel k}
    | Inr(k,Some p) ->
        lift_fconstr (k-p) {mark=mark Red;term=FFlex(RelKey p)}

(* since the head may be reducible, we might introduce lifts of 0 *)
let compact_stack head stk =
  let rec strip_rec depth = function
    | Zshift(k)::s -> strip_rec (depth+k) s
    | Zupdate(m)::s ->
        (* Be sure to create a new cell otherwise sharing would be
           lost by the update operation *)
        let h' = lft_fconstr depth head in
        (** The stack contains [Zupdate] marks only if in sharing mode *)
        let _ = update ~share:true m h'.mark h'.term in
        strip_rec depth s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zapp _ | Zprimitive _) :: _ | []) as stk -> zshift depth stk
  in
  strip_rec 0 stk

(* Put an update mark in the stack, only if needed *)
let zupdate info m s =
  let share = info.i_cache.i_share in
  if share && begin match Mark.red_state m.mark with Red -> true  | Ntrl | Whnf | Cstr -> false end
  then
    let s' = compact_stack m s in
    let _ = m.term <- FLOCKED in
    Zupdate(m)::s'
  else s

let mk_lambda env t =
  let (rvars,t') = Term.decompose_lam t in
  FLambda(List.length rvars, List.rev rvars, t', env)

let destFLambda clos_fun t =
  match [@ocaml.warning "-4"] t.term with
      FLambda(_,[(na,ty)],b,e) -> (na,clos_fun e ty,clos_fun (subs_lift e) b)
    | FLambda(n,(na,ty)::tys,b,e) ->
        (na,clos_fun e ty,{mark=t.mark;term=FLambda(n-1,tys,b,subs_lift e)})
    | _ -> assert false
        (* t must be a FLambda and binding list cannot be empty *)

(* Optimization: do not enclose variables in a closure.
   Makes variable access much faster *)
let mk_clos e t =
  match kind t with
    | Rel i -> clos_rel e i
    | Var x -> {mark = mark Red; term = FFlex (VarKey x) }
    | Const c -> {mark = mark Red; term = FFlex (ConstKey c) }
    | Meta _ | Sort _ ->  {mark = mark Ntrl; term = FAtom t }
    | Ind kn -> {mark = mark Ntrl; term = FInd kn }
    | Construct kn -> {mark = mark Cstr; term = FConstruct kn }
    | Int i -> {mark = mark Cstr; term = FInt i}
    | Float f -> {mark = mark Cstr; term = FFloat f}
    | (CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _|Proj _|Array _) ->
        {mark = mark Red; term = FCLOS(t,e)}

let inject c = mk_clos (subs_id 0) c

let mk_irrelevant = { mark = mark Cstr; term = FIrrelevant }

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

let is_irrelevant mode r = match mode, r with
| Conversion, Sorts.Irrelevant -> true
| (Conversion | Reduction), (Sorts.Relevant | Sorts.Irrelevant) -> false

let shortcut_irrelevant mode r =
  if is_irrelevant mode r then raise Irrelevant

let assoc_defined = function
| LocalDef (_, c, _) -> c
| LocalAssum (_, _) -> raise Not_found

let constant_value_in u = function
| Def b -> subst_instance_constr u b
| OpaqueDef _ -> raise (NotEvaluableConst Opaque)
| Undef _ -> raise (NotEvaluableConst NoBody)
| Primitive p -> raise (NotEvaluableConst (IsPrimitive (u,p)))

let ref_value_cache env flags mode tab ref =
  try
    KeyTable.find tab ref
  with Not_found ->
    let v =
      try
        let body =
          match ref with
          | RelKey n ->
            let open! Context.Rel.Declaration in
            let i = n - 1 in
            let (d, _) =
              try Range.get env.env_rel_context.env_rel_map i
              with Invalid_argument _ -> raise Not_found
            in
            (* First check for irrelevance *)
            let () = shortcut_irrelevant mode (get_relevance d) in
            begin match d with
              | LocalAssum _ -> raise Not_found
              | LocalDef (_, t, _) -> lift n t
            end
          | VarKey id ->
            let def = Environ.lookup_named id env in
            let () = shortcut_irrelevant mode (binder_relevance (get_annot def)) in
            if TransparentState.is_transparent_variable flags id then assoc_defined def
            else raise Not_found
          | ConstKey (cst,u) ->
            let cb = lookup_constant cst env in
            let () = shortcut_irrelevant mode (cb.const_relevance) in
            if TransparentState.is_transparent_constant flags cst then constant_value_in u cb.const_body
            else raise Not_found
        in
        Def (inject body)
      with
      | Irrelevant -> Def mk_irrelevant
      | NotEvaluableConst (IsPrimitive (_u,op)) (* Const *) -> Primitive op
      | Not_found (* List.assoc *)
      | NotEvaluableConst _ (* Const *)
        -> Undef None
    in
    KeyTable.add tab ref v; v

(* The inverse of mk_clos: move back to constr *)
let rec to_constr lfts v =
  match v.term with
    | FRel i -> mkRel (reloc_rel i lfts)
    | FFlex (RelKey p) -> mkRel (reloc_rel p lfts)
    | FFlex (VarKey x) -> mkVar x
    | FAtom c -> exliftn lfts c
    | FFlex (ConstKey op) -> mkConstU op
    | FInd op -> mkIndU op
    | FConstruct op -> mkConstructU op
    | FCaseT (ci, u, pms, p, c, ve, env) ->
      to_constr_case lfts ci u pms p NoInvert c ve env
    | FCaseInvert (ci, u, pms, p, indices, c, ve, env) ->
      let iv = CaseInvert {indices=Array.map (to_constr lfts) indices} in
      to_constr_case lfts ci u pms p iv c ve env
    | FFix ((op,(lna,tys,bds)) as fx, e) ->
      if is_subs_id e && is_lift_id lfts then
        mkFix fx
      else
        let n = Array.length bds in
        let subs_ty = comp_subs lfts e in
        let subs_bd = comp_subs (el_liftn n lfts) (subs_liftn n e) in
        let tys = Array.Fun1.map subst_constr subs_ty tys in
        let bds = Array.Fun1.map subst_constr subs_bd bds in
        mkFix (op, (lna, tys, bds))
    | FCoFix ((op,(lna,tys,bds)) as cfx, e) ->
      if is_subs_id e && is_lift_id lfts then
        mkCoFix cfx
      else
        let n = Array.length bds in
        let subs_ty = comp_subs lfts e in
        let subs_bd = comp_subs (el_liftn n lfts) (subs_liftn n e) in
        let tys = Array.Fun1.map subst_constr subs_ty tys in
        let bds = Array.Fun1.map subst_constr subs_bd bds in
        mkCoFix (op, (lna, tys, bds))
    | FApp (f,ve) ->
        mkApp (to_constr lfts f,
               Array.Fun1.map to_constr lfts ve)
    | FProj (p,c) ->
        mkProj (p,to_constr lfts c)

    | FLambda (len, tys, f, e) ->
      if is_subs_id e && is_lift_id lfts then
        Term.compose_lam (List.rev tys) f
      else
        let subs = comp_subs lfts e in
        let tys = List.mapi (fun i (na, c) -> na, subst_constr (subs_liftn i subs) c) tys in
        let f = subst_constr (subs_liftn len subs) f in
        Term.compose_lam (List.rev tys) f
    | FProd (n, t, c, e) ->
      if is_subs_id e && is_lift_id lfts then
        mkProd (n, to_constr lfts t, c)
      else
        let subs' = comp_subs lfts e in
        mkProd (n, to_constr lfts t, subst_constr (subs_lift subs') c)
    | FLetIn (n,b,t,f,e) ->
      let subs = comp_subs (el_lift lfts) (subs_lift e) in
        mkLetIn (n, to_constr lfts b,
                    to_constr lfts t,
                    subst_constr subs f)
    | FEvar ((ev,args),env) ->
      let subs = comp_subs lfts env in
        mkEvar(ev, List.map (fun a -> subst_constr subs a) args)
    | FLIFT (k,a) -> to_constr (el_shft k lfts) a

    | FInt i ->
       Constr.mkInt i
    | FFloat f ->
        Constr.mkFloat f

    | FArray (u,t,ty) ->
      let ty = to_constr lfts ty in
      let init i = to_constr lfts (Parray.get t (Uint63.of_int i)) in
      mkArray(u,Array.init (Parray.length_int t) init, to_constr lfts (Parray.default t),ty)

    | FCLOS (t,env) ->
      if is_subs_id env && is_lift_id lfts then t
      else
        let subs = comp_subs lfts env in
        subst_constr subs t

    | FIrrelevant -> assert (!Flags.in_debugger); mkVar(Id.of_string"_IRRELEVANT_")
    | FLOCKED -> assert (!Flags.in_debugger); mkVar(Id.of_string"_LOCKED_")

and to_constr_case lfts ci u pms p iv c ve env =
  if is_subs_id env && is_lift_id lfts then
    mkCase (ci, u, pms, p, iv, to_constr lfts c, ve)
  else
    let subs = comp_subs lfts env in
    let f_ctx (nas, c) =
      let c = subst_constr (Esubst.subs_liftn (Array.length nas) subs) c in
      (nas, c)
    in
    mkCase (ci, u, Array.map (fun c -> subst_constr subs c) pms,
        f_ctx p,
        iv,
        to_constr lfts c,
        Array.map f_ctx ve)

and subst_constr subst c = match [@ocaml.warning "-4"] Constr.kind c with
| Rel i ->
  begin match expand_rel i subst with
  | Inl (k, lazy v) -> Vars.lift k v
  | Inr (m, _) -> mkRel m
  end
| _ ->
  Constr.map_with_binders Esubst.subs_lift subst_constr subst c

and comp_subs el s =
  Esubst.lift_subst (fun el c -> lazy (to_constr el c)) el s

(* This function defines the correspondence between constr and
   fconstr. When we find a closure whose substitution is the identity,
   then we directly return the constr to avoid possibly huge
   reallocation. *)
let term_of_fconstr c = to_constr el_id c

(* fstrong applies unfreeze_fun recursively on the (freeze) term and
 * yields a term.  Assumes that the unfreeze_fun never returns a
 * FCLOS term.
let rec fstrong unfreeze_fun lfts v =
  to_constr (fstrong unfreeze_fun) lfts (unfreeze_fun v)
*)

let rec zip m stk =
  match stk with
    | [] -> m
    | Zapp args :: s -> zip {mark=Mark.neutr m.mark; term=FApp(m, args)} s
    | ZcaseT(ci, u, pms, p, br, e)::s ->
        let t = FCaseT(ci, u, pms, p, m, br, e) in
        let mark = mark (neutr (Mark.red_state m.mark)) in
        zip {mark; term=t} s
    | Zproj p :: s ->
        let mark = mark (neutr (Mark.red_state m.mark)) in
        zip {mark; term=FProj(Projection.make p true,m)} s
    | Zfix(fx,par)::s ->
        zip fx (par @ append_stack [|m|] s)
    | Zshift(n)::s ->
        zip (lift_fconstr n m) s
    | Zupdate(rf)::s ->
      (** The stack contains [Zupdate] marks only if in sharing mode *)
        zip (update ~share:true rf m.mark m.term) s
    | Zprimitive(_op,c,rargs,kargs)::s ->
      let args = List.rev_append rargs (m::List.map snd kargs) in
      let f = {mark = mark Red; term = FFlex (ConstKey c)} in
      zip {mark=mark (neutr (Mark.red_state m.mark)); term = FApp (f, Array.of_list args)} s

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
        strip_rec rstk (update ~share:true m h.mark h.term) depth s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as stk ->
      (depth,List.rev rstk, stk)
  in
  strip_rec [] head 0 stk

let strip_update_shift_app head stack =
  assert (match Mark.red_state head.mark with Red -> false | Ntrl | Cstr | Whnf -> true);
  strip_update_shift_app_red head stack

let get_nth_arg head n stk =
  assert (match Mark.red_state head.mark with Red -> false | Ntrl | Cstr | Whnf -> true);
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
        strip_rec rstk (update ~share:true m h.mark h.term) n s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as s -> (None, List.rev rstk @ s) in
  strip_rec [] head n stk

let rec subs_consn v i n s =
  if Int.equal i n then s
  else subs_consn v (i + 1) n (subs_cons v.(i) s)

let subs_consv v s =
  subs_consn v 0 (Array.length v) s

(* Beta reduction: look for an applied argument in the stack.
   Since the encountered update marks are removed, h must be a whnf *)
let rec get_args n tys f e = function
    | Zupdate r :: s ->
        (** The stack contains [Zupdate] mark only if in sharing mode *)
        let _hd = update ~share:true r (mark Cstr) (FLambda(n,tys,f,e)) in
        get_args n tys f e s
    | Zshift k :: s ->
        get_args n tys f (subs_shft (k,e)) s
    | Zapp l :: s ->
        let na = Array.length l in
        if n == na then (Inl (subs_consn l 0 na e), s)
        else if n < na then (* more arguments *)
          let eargs = Array.sub l n (na-n) in
          (Inl (subs_consn l 0 n e), Zapp eargs :: s)
        else (* more lambdas *)
          let etys = List.skipn na tys in
          get_args (n-na) etys f (subs_consn l 0 na e) s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as stk ->
      (Inr {mark=mark Cstr; term=FLambda(n,tys,f,e)}, stk)

(* Eta expansion: add a reference to implicit surrounding lambda at end of stack *)
let rec eta_expand_stack na = function
  | (Zapp _ | Zfix _ | ZcaseT _ | Zproj _
        | Zshift _ | Zupdate _ | Zprimitive _ as e) :: s ->
      e :: eta_expand_stack na s
  | [] ->
    let arg = match na.binder_relevance with
    | Sorts.Relevant -> {mark = mark Ntrl; term = FRel 1}
    | Sorts.Irrelevant -> mk_irrelevant
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
      strip_rec rnargs (update ~share:true m h.mark h.term) depth  kargs s
    | (Zprimitive _ | ZcaseT _ | Zproj _ | Zfix _) :: _ | [] -> assert false
  in strip_rec [] {mark = mark Red; term = FFlex(ConstKey c)} 0 kargs stk

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
    let c = Vars.subst_instance_constr u c in
    let subs = mk_pms i ctx in
    subs_cons (mk_clos subs c) subs
  in
  mk_pms (Array.length pms - 1) mib.mind_params_ctxt

(* Iota-reduction: feed the arguments of the constructor to the branch *)
let get_branch infos depth ci u pms (ind, c) br e args =
  let i = c - 1 in
  let args = drop_parameters depth ci.ci_npar args in
  let (_nas, br) = br.(i) in
  if Int.equal ci.ci_cstr_ndecls.(i) ci.ci_cstr_nargs.(i) then
    (* No let-bindings in the constructor, we don't have to fetch the
      environment to know the value of the branch. *)
    let rec push e stk = match stk with
    | [] -> e
    | Zapp v :: stk -> push (subs_consv v e) stk
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
      let e = subs_consv s ind_subst in
      let v = mk_clos e b in
      v :: ans
    in
    let ext = push (Array.length args - 1) [] ctx in
    (br, subs_consv (Array.rev_of_list ext) e)

(** [eta_expand_ind_stack env ind c s t] computes stacks corresponding
    to the conversion of the eta expansion of t, considered as an inhabitant
    of ind, and the Constructor c of this inductive type applied to arguments
    s.
    @assumes [t] is an irreducible term, and not a constructor. [ind] is the inductive
    of the constructor term [c]
    @raise Not_found if the inductive is not a primitive record, or if the
    constructor is partially applied.
 *)
let eta_expand_ind_stack env ind m s (f, s') =
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
    let hstack = Array.map (fun p ->
        { mark = mark Red; (* right can't be a constructor though *)
          term = FProj (Projection.make p true, right) })
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
      | FFix (((reci,i),(_,_,bds as rdcl)),env) ->
          (bds.(i),
           (fun j -> { mark = mark Cstr;
                       term = FFix (((reci,j),rdcl),env) }),
           env, Array.length bds)
      | FCoFix ((i,(_,_,bds as rdcl)),env) ->
          (bds.(i),
           (fun j -> { mark = mark Cstr;
                       term = FCoFix ((j,rdcl),env) }),
           env, Array.length bds)
      | _ -> assert false
  in
  let rec mk_subs env i =
    if Int.equal i nfix then env
    else mk_subs (subs_cons (make_body i) env) (i + 1)
  in
  (mk_subs env 0, thisbody)

let unfold_projection info p =
  if red_projection info.i_flags p
  then
    Some (Zproj (Projection.repr p))
  else None

(************************************************************************)
(* Reduction of Native operators                                        *)

open Primred

module FNativeEntries =
  struct
    type elem = fconstr
    type args = fconstr array
    type evd = unit
    type uinstance = Univ.Instance.t

    let mk_construct c =
      (* All constructors used in primitive functions are relevant *)
      { mark = mark Cstr; term = FConstruct (Univ.in_punivs c) }

    let get = Array.get

    let get_int () e =
      match [@ocaml.warning "-4"] e.term with
      | FInt i -> i
      | _ -> raise Primred.NativeDestKO

    let get_float () e =
      match [@ocaml.warning "-4"] e.term with
      | FFloat f -> f
      | _ -> raise Primred.NativeDestKO

    let get_parray () e =
      match [@ocaml.warning "-4"] e.term with
      | FArray (_u,t,_ty) -> t
      | _ -> raise Not_found

    let dummy = {mark = mark Ntrl; term = FRel 0}

    let current_retro = ref Retroknowledge.empty
    let defined_int = ref false
    let fint = ref dummy

    let init_int retro =
      match retro.Retroknowledge.retro_int63 with
      | Some c ->
        defined_int := true;
        fint := { mark = mark Ntrl; term = FFlex (ConstKey (Univ.in_punivs c)) }
      | None -> defined_int := false

    let defined_float = ref false
    let ffloat = ref dummy

    let init_float retro =
      match retro.Retroknowledge.retro_float64 with
      | Some c ->
        defined_float := true;
        ffloat := { mark = mark Ntrl; term = FFlex (ConstKey (Univ.in_punivs c)) }
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
        fcmp := { mark = mark Ntrl; term = FInd (Univ.in_punivs icmp) }
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
      { mark = mark Cstr; term = FInt i }

    let mkFloat env f =
      check_float env;
      { mark = mark Cstr; term = FFloat f }

    let mkBool env b =
      check_bool env;
      if b then !ftrue else !ffalse

    let mkCarry env b e =
      check_carry env;
      {mark = mark Cstr;
       term = FApp ((if b then !fC1 else !fC0),[|!fint;e|])}

    let mkIntPair env e1 e2 =
      check_pair env;
      { mark = mark Cstr; term = FApp(!fPair, [|!fint;!fint;e1;e2|]) }

    let mkFloatIntPair env f i =
      check_pair env;
      check_float env;
      { mark = mark Cstr; term = FApp(!fPair, [|!ffloat;!fint;f;i|]) }

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
      { mark = mark Whnf; term = FArray (u,t,ty)}

  end

module FredNative = RedNative(FNativeEntries)

let rec skip_irrelevant_stack stk = match stk with
| [] -> []
| (Zshift _ | Zapp _) :: s -> skip_irrelevant_stack s
| (Zfix _ | Zproj _) :: s ->
  (* Typing rules ensure that fix / proj over SProp is irrelevant *)
  skip_irrelevant_stack s
| ZcaseT (ci, _, _, _, _, _) :: s ->
  begin match ci.ci_relevance with
  | Sorts.Irrelevant -> skip_irrelevant_stack s
  | Sorts.Relevant -> stk
  end
| Zprimitive _ :: _ -> assert false (* no irrelevant primitives so far *)
| Zupdate m :: s ->
  (** The stack contains [Zupdate] marks only if in sharing mode *)
  let _ = update ~share:true m mk_irrelevant.mark mk_irrelevant.term in
  skip_irrelevant_stack s

let is_irrelevant_constructor infos (ind,_) = match infos.i_cache.i_mode with
| Conversion -> Indset_env.mem ind infos.i_cache.i_env.irr_inds
| Reduction -> false

let is_irrelevant_projection infos p = match infos.i_cache.i_mode with
| Conversion -> not @@ Projection.Repr.relevant @@ Projection.repr p
| Reduction -> false

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
    | FCaseT(ci,u,pms,p,t,br,e) ->
      if is_irrelevant info.i_cache.i_mode ci.ci_relevance then
        (mk_irrelevant, skip_irrelevant_stack stk)
      else
        knh info t (ZcaseT(ci,u,pms,p,br,e)::zupdate info m stk)
    | FFix (((ri, n), (lna, _, _)), _) ->
      if is_irrelevant info.i_cache.i_mode (lna.(n)).binder_relevance then
        (mk_irrelevant, skip_irrelevant_stack stk)
      else
        (match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh info arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FProj (p,c) ->
      if is_irrelevant_projection info p then
        (mk_irrelevant, skip_irrelevant_stack stk)
      else
      (match unfold_projection info p with
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
    | Case(ci,u,pms,p,NoInvert,t,br) ->
      if is_irrelevant info.i_cache.i_mode ci.ci_relevance then
        (mk_irrelevant, skip_irrelevant_stack stk)
      else
        knht info e t (ZcaseT(ci, u, pms, p, br, e)::stk)
    | Case(ci,u,pms,p,CaseInvert{indices},t,br) ->
      if is_irrelevant info.i_cache.i_mode ci.ci_relevance then
        (mk_irrelevant, skip_irrelevant_stack stk)
      else
        let term = FCaseInvert (ci, u, pms, p, (Array.map (mk_clos e) indices), mk_clos e t, br, e) in
        { mark = mark Red; term }, stk
    | Fix (((_, n), (lna, _, _)) as fx) ->
      if is_irrelevant info.i_cache.i_mode (lna.(n)).binder_relevance then
        (mk_irrelevant, skip_irrelevant_stack stk)
      else
        knh info { mark = mark Cstr; term = FFix (fx, e) } stk
    | Cast(a,_,_) -> knht info e a stk
    | Rel n -> knh info (clos_rel e n) stk
    | Proj (p, c) -> knh info { mark = mark Red; term = FProj (p, mk_clos e c) } stk
    | (Ind _|Const _|Construct _|Var _|Meta _ | Sort _ | Int _|Float _) -> (mk_clos e t, stk)
    | CoFix cfx -> { mark = mark Cstr; term = FCoFix (cfx,e) }, stk
    | Lambda _ -> { mark = mark Cstr ; term = mk_lambda e t }, stk
    | Prod (n, t, c) ->
      { mark = mark Whnf; term = FProd (n, mk_clos e t, c, e) }, stk
    | LetIn (n,b,t,c) ->
      { mark = mark Red; term = FLetIn (n, mk_clos e b, mk_clos e t, c, e) }, stk
    | Evar ev -> { mark = mark Red; term = FEvar (ev, e) }, stk
    | Array(u,t,def,ty) ->
      let len = Array.length t in
      let ty = mk_clos e ty in
      let t = Parray.init (Uint63.of_int len) (fun i -> mk_clos e t.(i)) (mk_clos e def) in
      let term = FArray (u,t,ty) in
      knh info { mark = mark Cstr; term } stk

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
      (match ref_value_cache info.i_cache.i_env (RedFlags.red_transparent info.i_flags) info.i_cache.i_mode tab fl with
        | Def v -> kni info tab v stk
        | Primitive op ->
          if check_native_args op stk then
            let c = match fl with ConstKey c -> c | RelKey _ | VarKey _ -> assert false in
            let rargs, a, nargs, stk = get_native_args1 op c stk in
            kni info tab a (Zprimitive(op,c,rargs,nargs)::stk)
          else
            (* Similarly to fix, partially applied primitives are not Ntrl! *)
            (m, stk)
        | Undef _ | OpaqueDef _ -> (set_ntrl m; (m,stk)))
  | FConstruct(c,_u) ->
     let use_match = red_set info.i_flags fMATCH in
     let use_fix = red_set info.i_flags fFIX in
     if use_match || use_fix then
      (match [@ocaml.warning "-4"] strip_update_shift_app m stk with
        | (depth, args, ZcaseT(ci,u,pms,_,br,e)::s) when use_match ->
            assert (ci.ci_npar>=0);
            let (br, e) = get_branch info depth ci u pms c br e args in
            knit info tab e br s
        | (_, cargs, Zfix(fx,par)::s) when use_fix ->
            let rarg = fapp_stack(m,cargs) in
            let stk' = par @ append_stack [|rarg|] s in
            let (fxe,fxbd) = contract_fix_vect fx.term in
            knit info tab fxe fxbd stk'
        | (depth, args, Zproj p::s) when use_match ->
            let rargs = drop_parameters depth (Projection.Repr.npars p) args in
            let rarg = project_nth_arg (Projection.Repr.arg p) rargs in
            kni info tab rarg s
        | (_,args,s) ->
          if is_irrelevant_constructor info c then (mk_irrelevant, skip_irrelevant_stack stk) else (m,args@s))
     else if is_irrelevant_constructor info c then
      (mk_irrelevant, skip_irrelevant_stack stk)
     else
      (m, stk)
  | FCoFix ((i, (lna, _, _)), _) ->
    if is_irrelevant info.i_cache.i_mode (lna.(i)).binder_relevance then
      (mk_irrelevant, skip_irrelevant_stack stk)
    else if red_set info.i_flags fCOFIX then
      (match strip_update_shift_app m stk with
        | (_, args, (((ZcaseT _|Zproj _)::_) as stk')) ->
            let (fxe,fxbd) = contract_fix_vect m.term in
            knit info tab fxe fxbd (args@stk')
        | (_,args, ((Zapp _ | Zfix _ | Zshift _ | Zupdate _ | Zprimitive _) :: _ | [] as s)) -> (m,args@s))
    else (m, stk)
  | FLetIn (_,v,_,bd,e) when red_set info.i_flags fZETA ->
      knit info tab (subs_cons v e) bd stk
  | FEvar(ev,env) ->
    (* FIXME: handle relevance *)
      (match info.i_cache.i_sigma ev with
          Some c -> knit info tab env c stk
        | None -> (m,stk))
  | FInt _ | FFloat _ | FArray _ ->
    (match [@ocaml.warning "-4"] strip_update_shift_app m stk with
     | (_, _, Zprimitive(op,(_,u as c),rargs,nargs)::s) ->
       let (rargs, nargs) = skip_native_args (m::rargs) nargs in
       begin match nargs with
         | [] ->
           let args = Array.of_list (List.rev rargs) in
           begin match FredNative.red_prim (info_env info) () op u args with
             | Some m ->
             kni info tab m s
             | None ->
               let f = {mark = mark Whnf; term = FFlex (ConstKey c)} in
               let m = {mark = mark Whnf; term = FApp(f,args)} in
               (m,s)
           end
         | (kd,a)::nargs ->
           assert (kd = CPrimitives.Kwhnf);
           kni info tab a (Zprimitive(op,c,rargs,nargs)::s)
             end
     | (_, _, s) -> (m, s))
  | FCaseInvert (ci, u, pms, _p,iv,_c,v,env) when red_set info.i_flags fMATCH ->
    let pms = mk_clos_vect env pms in
    begin match case_inversion info tab ci u pms iv v with
      | Some c -> knit info tab env c stk
      | None -> (m, stk)
    end
  | FIrrelevant ->
    let stk = skip_irrelevant_stack stk in
    (m, stk)
  | FProd _ | FAtom _ | FInd _ (* relevant statically *)
  | FCaseInvert _ | FProj _ | FFix _ (* relevant because of knh(t) *)
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
    let tab = if info.i_cache.i_mode == Conversion then tab else KeyTable.create 17 in
    let info = {info with i_cache = { info.i_cache with i_mode = Conversion}; i_flags=all} in
    let check_index i index =
      let expected = expect_args.(ci.ci_npar + i) in
      let expected = Vars.subst_instance_constr u expected in
      let expected = mk_clos psubst expected in
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
let rec kl info tab m =
  let share = info.i_cache.i_share in
  if is_val m then (incr prune; term_of_fconstr m)
  else
    let (nm,s) = kni info tab m [] in
    let () = if share then ignore (fapp_stack (nm, s)) in (* to unlock Zupdates! *)
    zip_term info tab (norm_head info tab nm) s

and klt info tab e t = match kind t with
| Rel i -> kl info tab (clos_rel e i)
| Var _ |Const _|CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _|Proj _|Array _ ->
  let share = info.i_cache.i_share in
  let (nm,s) = knit info tab e t [] in
  let () = if share then ignore (fapp_stack (nm, s)) in (* to unlock Zupdates! *)
  zip_term info tab (norm_head info tab nm) s
| Meta _ | Sort _ | Ind _ | Construct _ | Int _ | Float _ -> t

(* no redex: go up for atoms and already normalized terms, go down
   otherwise. *)
and norm_head info tab m =
  if is_val m then (incr prune; term_of_fconstr m) else
    match m.term with
      | FLambda(_n,tys,f,e) ->
        let fold (e, info, ctxt) (na, ty) =
          let ty = klt info tab e ty in
          let info = push_relevance info na in
          (subs_lift e, info, (na, ty) :: ctxt)
        in
        let (e', info, rvtys) = List.fold_left fold (e,info,[]) tys in
        let bd = klt info tab e' f in
        List.fold_left (fun b (na,ty) -> mkLambda(na,ty,b)) bd rvtys
      | FLetIn(na,a,b,f,e) ->
          let c = klt (push_relevance info na) tab (subs_lift e) f in
          mkLetIn(na, kl info tab a, kl info tab b, c)
      | FProd(na,dom,rng,e) ->
        let rng = klt (push_relevance info na) tab (subs_lift e) rng in
          mkProd(na, kl info tab dom, rng)
      | FCoFix((n,(na,tys,bds)),e) ->
          let infobd = push_relevances info na in
          let ftys = Array.map (fun ty -> klt info tab e ty) tys in
          let fbds = Array.map (fun bd -> klt infobd tab (subs_liftn (Array.length na) e) bd) bds in
          mkCoFix (n, (na, ftys, fbds))
      | FFix((n,(na,tys,bds)),e) ->
          let infobd = push_relevances info na in
          let ftys = Array.map (fun ty -> klt info tab e ty) tys in
          let fbds = Array.map (fun bd -> klt infobd tab (subs_liftn (Array.length na) e) bd) bds in
          mkFix (n, (na, ftys, fbds))
      | FEvar((i,args),env) ->
          mkEvar(i, List.map (fun a -> klt info tab env a) args)
      | FProj (p,c) ->
        mkProj (p, kl info tab c)
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
| ZcaseT(ci, u, pms, p, br, e) :: s ->
    let zip_ctx (nas, c) =
      let e = Esubst.subs_liftn (Array.length nas) e in
      (nas, klt info tab e c)
    in
    let t = mkCase(ci, u, Array.map (fun c -> klt info tab e c) pms, zip_ctx p,
      NoInvert, m, Array.map zip_ctx br) in
    zip_term info tab t s
| Zproj p::s ->
    let t = mkProj (Projection.make p true, m) in
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
let whd_val info tab v =
  with_stats (lazy (term_of_fconstr (kh info tab v [])))

(* strong reduction *)
let norm_val info tab v =
  with_stats (lazy (kl info tab v))

let whd_stack infos tab m stk = match Mark.red_state m.mark with
| Whnf | Ntrl ->
  (** No need to perform [kni] nor to unlock updates because
      every head subterm of [m] is [Whnf] or [Ntrl] *)
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

let create_conv_infos ?univs ?(evars=fun _ -> None) flgs env =
  let univs = Option.default (universes env) univs in
  let share = (Environ.typing_flags env).Declarations.share_reduction in
  let cache = {
    i_env = env;
    i_sigma = evars;
    i_share = share;
    i_univs = univs;
    i_mode = Conversion;
  } in
  { i_flags = flgs; i_relevances = Range.empty; i_cache = cache }

let create_clos_infos ?univs ?(evars=fun _ -> None) flgs env =
  let univs = Option.default (universes env) univs in
  let share = (Environ.typing_flags env).Declarations.share_reduction in
  let cache = {
    i_env = env;
    i_sigma = evars;
    i_share = share;
    i_univs = univs;
    i_mode = Reduction;
  } in
  { i_flags = flgs; i_relevances = Range.empty; i_cache = cache }

let create_tab () = KeyTable.create 17

let oracle_of_infos infos = Environ.oracle infos.i_cache.i_env

let infos_with_reds infos reds =
  { infos with i_flags = reds }

let unfold_reference env st tab key = ref_value_cache env st Conversion tab key

let unfold_ref_with_args infos tab fl v =
  let env = info_env infos in
  let flags = RedFlags.red_transparent (info_flags infos) in
  match ref_value_cache env flags infos.i_cache.i_mode tab fl with
  | Def def -> Some (def, v)
  | Primitive op when check_native_args op v ->
    let c = match [@ocaml.warning "-4"] fl with ConstKey c -> c | _ -> assert false in
    let rargs, a, nargs, v = get_native_args1 op c v in
    Some (a, (Zupdate a::(Zprimitive(op,c,rargs,nargs)::v)))
  | Undef _ | OpaqueDef _ | Primitive _ -> None
