(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

open CErrors
open Util
open Pp
open Names
open Constr
open Vars
open Environ
open Esubst

let stats = ref false

(* Profiling *)
let beta = ref 0
let delta = ref 0
let eta = ref 0
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
	 str " eta=" ++ int !eta ++ str" zeta=" ++ int !zeta ++ str" evar=" ++
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

let all_opaque = (Id.Pred.empty, Cpred.empty)
let all_transparent = (Id.Pred.full, Cpred.full)

let is_transparent_variable (ids, _) id = Id.Pred.mem id ids
let is_transparent_constant (_, csts) cst = Cpred.mem cst csts

module type RedFlagsSig = sig
  type reds
  type red_kind
  val fBETA : red_kind
  val fDELTA : red_kind
  val fETA : red_kind
  val fMATCH : red_kind
  val fFIX : red_kind
  val fCOFIX : red_kind
  val fZETA : red_kind
  val fCONST : Constant.t -> red_kind
  val fVAR : Id.t -> red_kind
  val no_red : reds
  val red_add : reds -> red_kind -> reds
  val red_sub : reds -> red_kind -> reds
  val red_add_transparent : reds -> transparent_state -> reds
  val red_transparent : reds -> transparent_state
  val mkflags : red_kind list -> reds
  val red_set : reds -> red_kind -> bool
  val red_projection : reds -> Projection.t -> bool
end

module RedFlags = (struct

  (* [r_const=(true,cl)] means all constants but those in [cl] *)
  (* [r_const=(false,cl)] means only those in [cl] *)
  (* [r_delta=true] just mean [r_const=(true,[])] *)

  type reds = {
    r_beta : bool;
    r_delta : bool;
    r_eta : bool;
    r_const : transparent_state;
    r_zeta : bool;
    r_match : bool;
    r_fix : bool;
    r_cofix : bool }

  type red_kind = BETA | DELTA | ETA | MATCH | FIX
              | COFIX | ZETA
	      | CONST of Constant.t | VAR of Id.t
  let fBETA = BETA
  let fDELTA = DELTA
  let fETA = ETA
  let fMATCH = MATCH
  let fFIX = FIX
  let fCOFIX = COFIX
  let fZETA = ZETA
  let fCONST kn  = CONST kn
  let fVAR id  = VAR id
  let no_red = {
    r_beta = false;
    r_delta = false;
    r_eta = false;
    r_const = all_opaque;
    r_zeta = false;
    r_match = false;
    r_fix = false;
    r_cofix = false }

  let red_add red = function
    | BETA -> { red with r_beta = true }
    | ETA -> { red with r_eta = true }
    | DELTA -> { red with r_delta = true; r_const = all_transparent }
    | CONST kn ->
	let (l1,l2) = red.r_const in
	{ red with r_const = l1, Cpred.add kn l2 }
    | MATCH -> { red with r_match = true }
    | FIX -> { red with r_fix = true }
    | COFIX -> { red with r_cofix = true }
    | ZETA -> { red with r_zeta = true }
    | VAR id ->
	let (l1,l2) = red.r_const in
	{ red with r_const = Id.Pred.add id l1, l2 }

  let red_sub red = function
    | BETA -> { red with r_beta = false }
    | ETA -> { red with r_eta = false }
    | DELTA -> { red with r_delta = false }
    | CONST kn ->
	let (l1,l2) = red.r_const in
	{ red with r_const = l1, Cpred.remove kn l2 }
    | MATCH -> { red with r_match = false }
    | FIX -> { red with r_fix = false }
    | COFIX -> { red with r_cofix = false }
    | ZETA -> { red with r_zeta = false }
    | VAR id ->
	let (l1,l2) = red.r_const in
	{ red with r_const = Id.Pred.remove id l1, l2 }

  let red_transparent red = red.r_const

  let red_add_transparent red tr =
    { red with r_const = tr }

  let mkflags = List.fold_left red_add no_red

  let red_set red = function
    | BETA -> incr_cnt red.r_beta beta
    | ETA -> incr_cnt red.r_eta eta
    | CONST kn ->
	let (_,l) = red.r_const in
	let c = Cpred.mem kn l in
	incr_cnt c delta
    | VAR id -> (* En attendant d'avoir des kn pour les Var *)
	let (l,_) = red.r_const in
	let c = Id.Pred.mem id l in
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

end : RedFlagsSig)

open RedFlags

let all = mkflags [fBETA;fDELTA;fZETA;fMATCH;fFIX;fCOFIX]
let allnolet = mkflags [fBETA;fDELTA;fMATCH;fFIX;fCOFIX]
let beta = mkflags [fBETA]
let betadeltazeta = mkflags [fBETA;fDELTA;fZETA]
let betaiota = mkflags [fBETA;fMATCH;fFIX;fCOFIX]
let betaiotazeta = mkflags [fBETA;fMATCH;fFIX;fCOFIX;fZETA]
let betazeta = mkflags [fBETA;fZETA]
let delta = mkflags [fDELTA]
let zeta = mkflags [fZETA]
let nored = no_red

(* Removing fZETA for finer behaviour would break many developments *)
let unfold_side_flags = [fBETA;fMATCH;fFIX;fCOFIX;fZETA]
let unfold_side_red = mkflags [fBETA;fMATCH;fFIX;fCOFIX;fZETA]
let unfold_red kn =
  let flag = match kn with
    | EvalVarRef id -> fVAR id
    | EvalConstRef kn -> fCONST kn in
  mkflags (flag::unfold_side_flags)

(* Flags of reduction and cache of constants: 'a is a type that may be
 * mapped to constr. 'a infos implements a cache for constants and
 * abstractions, storing a representation (of type 'a) of the body of
 * this constant or abstraction.
 *  * i_tab is the cache table of the results
 *  * i_repr is the function to get the representation from the current
 *         state of the cache and the body of the constant. The result
 *         is stored in the table.
 *  * i_rels is the array of free rel variables together with their optional
 *    body
 *
 * ref_value_cache searchs in the tab, otherwise uses i_repr to
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

let eq_table_key = IdKeyHash.equal

type 'a infos_tab = 'a KeyTable.t

type 'a infos_cache = {
  i_repr : 'a infos -> 'a infos_tab -> constr -> 'a;
  i_env : env;
  i_sigma : existential -> constr option;
  i_rels : (Constr.rel_declaration * lazy_val) Range.t;
  i_share : bool;
}

and 'a infos = {
  i_flags : reds;
  i_cache : 'a infos_cache }

let info_flags info = info.i_flags
let info_env info = info.i_cache.i_env

open Context.Named.Declaration

let assoc_defined id env = match Environ.lookup_named id env with
| LocalDef (_, c, _) -> c
| _ -> raise Not_found

let ref_value_cache ({i_cache = cache} as infos) tab ref =
  try
    Some (KeyTable.find tab ref)
  with Not_found ->
  try
    let body =
      match ref with
	| RelKey n ->
          let open Context.Rel.Declaration in
          let i = n - 1 in
          let (d, _) =
            try Range.get cache.i_rels i
            with Invalid_argument _ -> raise Not_found
          in
          begin match d with
          | LocalAssum _ -> raise Not_found
          | LocalDef (_, t, _) -> lift n t
          end
	| VarKey id -> assoc_defined id cache.i_env
	| ConstKey cst -> constant_value_in cache.i_env cst
    in
    let v = cache.i_repr infos tab body in
    KeyTable.add tab ref v;
    Some v
  with
    | Not_found (* List.assoc *)
    | NotEvaluableConst _ (* Const *)
      -> None

let evar_value cache ev =
  cache.i_sigma ev

let create ~repr ~share flgs env evars =
  let cache =
    { i_repr = repr;
      i_env = env;
      i_sigma = evars;
      i_rels = env.env_rel_context.env_rel_map;
      i_share = share;
    }
  in { i_flags = flgs; i_cache = cache }


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

(* Norm means the term is fully normalized and cannot create a redex
     when substituted
   Cstr means the term is in head normal form and that it can
     create a redex when substituted (i.e. constructor, fix, lambda)
   Whnf means we reached the head normal form and that it cannot
     create a redex when substituted
   Red is used for terms that might be reduced
*)
type red_state = Norm | Cstr | Whnf | Red

let neutr = function
  | (Whnf|Norm) -> Whnf
  | (Red|Cstr) -> Red

type fconstr = {
  mutable norm: red_state;
  mutable term: fterm }

and fterm =
  | FRel of int
  | FAtom of constr (* Metas and Sorts *)
  | FCast of fconstr * cast_kind * fconstr
  | FFlex of table_key
  | FInd of pinductive
  | FConstruct of pconstructor
  | FApp of fconstr * fconstr array
  | FProj of Projection.t * fconstr
  | FFix of fixpoint * fconstr subs
  | FCoFix of cofixpoint * fconstr subs
  | FCaseT of case_info * constr * fconstr * constr array * fconstr subs (* predicate and branches are closures *)
  | FLambda of int * (Name.t * constr) list * constr * fconstr subs
  | FProd of Name.t * fconstr * fconstr
  | FLetIn of Name.t * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential * fconstr subs
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs
  | FLOCKED

let fterm_of v = v.term
let set_norm v = v.norm <- Norm
let is_val v = match v.norm with Norm -> true | _ -> false

let mk_atom c = {norm=Norm;term=FAtom c}
let mk_red f = {norm=Red;term=f}

(* Could issue a warning if no is still Red, pointing out that we loose
   sharing. *)
let update ~share v1 no t =
  if share then
    (v1.norm <- no;
     v1.term <- t;
     v1)
  else {norm=no;term=t}

(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *)

type stack_member =
  | Zapp of fconstr array
  | ZcaseT of case_info * constr * constr array * fconstr subs
  | Zproj of Projection.Repr.t
  | Zfix of fconstr * stack
  | Zshift of int
  | Zupdate of fconstr

and stack = stack_member list

let empty_stack = []
let append_stack v s =
  if Int.equal (Array.length v) 0 then s else
  match s with
  | Zapp l :: s -> Zapp (Array.append v l) :: s
  | _ -> Zapp v :: s

(* Collapse the shifts in the stack *)
let zshift n s =
  match (n,s) with
      (0,_) -> s
    | (_,Zshift(k)::s) -> Zshift(n+k)::s
    | _ -> Zshift(n)::s

let rec stack_args_size = function
  | Zapp v :: s -> Array.length v + stack_args_size s
  | Zshift(_)::s -> stack_args_size s
  | Zupdate(_)::s -> stack_args_size s
  | _ -> 0

(* When used as an argument stack (only Zapp can appear) *)
let rec decomp_stack = function
  | Zapp v :: s ->
      (match Array.length v with
          0 -> decomp_stack s
        | 1 -> Some (v.(0), s)
        | _ ->
            Some (v.(0), (Zapp (Array.sub v 1 (Array.length v - 1)) :: s)))
  | _ -> None
let array_of_stack s =
  let rec stackrec = function
  | [] -> []
  | Zapp args :: s -> args :: (stackrec s)
  | _ -> assert false
  in Array.concat (stackrec s)
let rec stack_assign s p c = match s with
  | Zapp args :: s ->
      let q = Array.length args in
      if p >= q then
	Zapp args :: stack_assign s (p-q) c
      else
        (let nargs = Array.copy args in
         nargs.(p) <- c;
         Zapp nargs :: s)
  | _ -> s
let rec stack_tail p s =
  if Int.equal p 0 then s else
    match s with
      | Zapp args :: s ->
	  let q = Array.length args in
	  if p >= q then stack_tail (p-q) s
	  else Zapp (Array.sub args p (q-p)) :: s
      | _ -> failwith "stack_tail"
let rec stack_nth s p = match s with
  | Zapp args :: s ->
      let q = Array.length args in
      if p >= q then stack_nth s (p-q)
      else args.(p)
  | _ -> raise Not_found

(* Lifting. Preserves sharing (useful only for cell with norm=Red).
   lft_fconstr always create a new cell, while lift_fconstr avoids it
   when the lift is 0. *)
let rec lft_fconstr n ft =
  match ft.term with
    | (FInd _|FConstruct _|FFlex(ConstKey _|VarKey _)) -> ft
    | FRel i -> {norm=Norm;term=FRel(i+n)}
    | FLambda(k,tys,f,e) -> {norm=Cstr; term=FLambda(k,tys,f,subs_shft(n,e))}
    | FFix(fx,e) -> {norm=Cstr; term=FFix(fx,subs_shft(n,e))}
    | FCoFix(cfx,e) -> {norm=Cstr; term=FCoFix(cfx,subs_shft(n,e))}
    | FLIFT(k,m) -> lft_fconstr (n+k) m
    | FLOCKED -> assert false
    | FFlex _ | FAtom _ | FCast _ | FApp _ | FProj _ | FCaseT _ | FProd _
      | FLetIn _ | FEvar _ | FCLOS _ -> {norm=ft.norm; term=FLIFT(n,ft)}
let lift_fconstr k f =
  if Int.equal k 0 then f else lft_fconstr k f
let lift_fconstr_vect k v =
  if Int.equal k 0 then v else Array.Fun1.map lft_fconstr k v

let clos_rel e i =
  match expand_rel i e with
    | Inl(n,mt) -> lift_fconstr n mt
    | Inr(k,None) -> {norm=Norm; term= FRel k}
    | Inr(k,Some p) ->
        lift_fconstr (k-p) {norm=Red;term=FFlex(RelKey p)}

(* since the head may be reducible, we might introduce lifts of 0 *)
let compact_stack head stk =
  let rec strip_rec depth = function
    | Zshift(k)::s -> strip_rec (depth+k) s
    | Zupdate(m)::s ->
        (* Be sure to create a new cell otherwise sharing would be
           lost by the update operation *)
        let h' = lft_fconstr depth head in
        (** The stack contains [Zupdate] marks only if in sharing mode *)
        let _ = update ~share:true m h'.norm h'.term in
        strip_rec depth s
    | stk -> zshift depth stk in
  strip_rec 0 stk

(* Put an update mark in the stack, only if needed *)
let zupdate info m s =
  let share = info.i_cache.i_share in
  if share && begin match m.norm with Red -> true | _ -> false end
  then
    let s' = compact_stack m s in
    let _ = m.term <- FLOCKED in
    Zupdate(m)::s'
  else s

let mk_lambda env t =
  let (rvars,t') = Term.decompose_lam t in
  FLambda(List.length rvars, List.rev rvars, t', env)

let destFLambda clos_fun t =
  match t.term with
      FLambda(_,[(na,ty)],b,e) -> (na,clos_fun e ty,clos_fun (subs_lift e) b)
    | FLambda(n,(na,ty)::tys,b,e) ->
        (na,clos_fun e ty,{norm=Cstr;term=FLambda(n-1,tys,b,subs_lift e)})
    | _ -> assert false
	(* t must be a FLambda and binding list cannot be empty *)

(* Optimization: do not enclose variables in a closure.
   Makes variable access much faster *)
let mk_clos e t =
  match kind t with
    | Rel i -> clos_rel e i
    | Var x -> { norm = Red; term = FFlex (VarKey x) }
    | Const c -> { norm = Red; term = FFlex (ConstKey c) }
    | Meta _ | Sort _ ->  { norm = Norm; term = FAtom t }
    | Ind kn -> { norm = Norm; term = FInd kn }
    | Construct kn -> { norm = Cstr; term = FConstruct kn }
    | (CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _|Proj _) ->
        {norm = Red; term = FCLOS(t,e)}

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

(* Translate the head constructor of t from constr to fconstr. This
   function is parameterized by the function to apply on the direct
   subterms.
   Could be used insted of mk_clos. *)
let mk_clos_deep clos_fun env t =
  match kind t with
    | (Rel _|Ind _|Const _|Construct _|Var _|Meta _ | Sort _) ->
        mk_clos env t
    | Cast (a,k,b) ->
        { norm = Red;
          term = FCast (clos_fun env a, k, clos_fun env b)}
    | App (f,v) ->
        { norm = Red;
          term = FApp (clos_fun env f, Array.Fun1.map clos_fun env v) }
    | Proj (p,c) ->
	{ norm = Red;
	  term = FProj (p, clos_fun env c) }
    | Case (ci,p,c,v) ->
        { norm = Red;
	  term = FCaseT (ci, p, clos_fun env c, v, env) }
    | Fix fx ->
        { norm = Cstr; term = FFix (fx, env) }
    | CoFix cfx ->
        { norm = Cstr; term = FCoFix(cfx,env) }
    | Lambda _ ->
        { norm = Cstr; term = mk_lambda env t }
    | Prod (n,t,c)   ->
        { norm = Whnf;
	  term = FProd (n, clos_fun env t, clos_fun (subs_lift env) c) }
    | LetIn (n,b,t,c) ->
        { norm = Red;
	  term = FLetIn (n, clos_fun env b, clos_fun env t, c, env) }
    | Evar ev ->
	{ norm = Red; term = FEvar(ev,env) }

(* A better mk_clos? *)
let mk_clos2 = mk_clos_deep mk_clos

(* The inverse of mk_clos_deep: move back to constr *)
let rec to_constr lfts v =
  match v.term with
    | FRel i -> mkRel (reloc_rel i lfts)
    | FFlex (RelKey p) -> mkRel (reloc_rel p lfts)
    | FFlex (VarKey x) -> mkVar x
    | FAtom c -> exliftn lfts c
    | FCast (a,k,b) ->
      mkCast (to_constr lfts a, k, to_constr lfts b)
    | FFlex (ConstKey op) -> mkConstU op
    | FInd op -> mkIndU op
    | FConstruct op -> mkConstructU op
    | FCaseT (ci,p,c,ve,env) ->
      if is_subs_id env && is_lift_id lfts then
        mkCase (ci, p, to_constr lfts c, ve)
      else
        let subs = comp_subs lfts env in
        mkCase (ci, subst_constr subs p,
            to_constr lfts c,
            Array.map (fun b -> subst_constr subs b) ve)
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
    | FProd (n,t,c)   ->
        mkProd (n, to_constr lfts t,
                   to_constr (el_lift lfts) c)
    | FLetIn (n,b,t,f,e) ->
      let subs = comp_subs (el_lift lfts) (subs_lift e) in
        mkLetIn (n, to_constr lfts b,
                    to_constr lfts t,
                    subst_constr subs f)
    | FEvar ((ev,args),env) ->
      let subs = comp_subs lfts env in
        mkEvar(ev,Array.map (fun a -> subst_constr subs a) args)
    | FLIFT (k,a) -> to_constr (el_shft k lfts) a
    | FCLOS (t,env) ->
      if is_subs_id env && is_lift_id lfts then t
      else
        let subs = comp_subs lfts env in
        subst_constr subs t
    | FLOCKED -> assert false (*mkVar(Id.of_string"_LOCK_")*)

and subst_constr subst c = match Constr.kind c with
| Rel i ->
  begin match expand_rel i subst with
  | Inl (k, lazy v) -> Vars.lift k v
  | Inr (m, _) -> mkRel m
  end
| _ ->
  Constr.map_with_binders Esubst.subs_lift subst_constr subst c

and comp_subs el s =
  Esubst.lift_subst (fun el c -> lazy (to_constr el c)) el s

(* This function defines the correspondance between constr and
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
    | Zapp args :: s -> zip {norm=neutr m.norm; term=FApp(m, args)} s
    | ZcaseT(ci,p,br,e)::s ->
        let t = FCaseT(ci, p, m, br, e) in
        zip {norm=neutr m.norm; term=t} s
    | Zproj p :: s ->
        zip {norm=neutr m.norm; term=FProj(Projection.make p true,m)} s
    | Zfix(fx,par)::s ->
        zip fx (par @ append_stack [|m|] s)
    | Zshift(n)::s ->
        zip (lift_fconstr n m) s
    | Zupdate(rf)::s ->
      (** The stack contains [Zupdate] marks only if in sharing mode *)
        zip (update ~share:true rf m.norm m.term) s

let fapp_stack (m,stk) = zip m stk

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
          {norm=h.norm;term=FApp(h,args)} depth s
    | Zupdate(m)::s ->
      (** The stack contains [Zupdate] marks only if in sharing mode *)
        strip_rec rstk (update ~share:true m h.norm h.term) depth s
    | stk -> (depth,List.rev rstk, stk) in
  strip_rec [] head 0 stk

let strip_update_shift_app head stack =
  assert (match head.norm with Red -> false | _ -> true);
  strip_update_shift_app_red head stack

let get_nth_arg head n stk =
  assert (match head.norm with Red -> false | _ -> true);
  let rec strip_rec rstk h n = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) n s
    | Zapp args::s' ->
        let q = Array.length args in
        if n >= q
        then
          strip_rec (Zapp args::rstk) {norm=h.norm;term=FApp(h,args)} (n-q) s'
        else
          let bef = Array.sub args 0 n in
          let aft = Array.sub args (n+1) (q-n-1) in
          let stk' =
            List.rev (if Int.equal n 0 then rstk else (Zapp bef :: rstk)) in
          (Some (stk', args.(n)), append_stack aft s')
    | Zupdate(m)::s ->
        (** The stack contains [Zupdate] mark only if in sharing mode *)
        strip_rec rstk (update ~share:true m h.norm h.term) n s
    | s -> (None, List.rev rstk @ s) in
  strip_rec [] head n stk

(* Beta reduction: look for an applied argument in the stack.
   Since the encountered update marks are removed, h must be a whnf *)
let rec get_args n tys f e stk =
  match stk with
      Zupdate r :: s ->
        (** The stack contains [Zupdate] mark only if in sharing mode *)
        let _hd = update ~share:true r Cstr (FLambda(n,tys,f,e)) in
        get_args n tys f e s
    | Zshift k :: s ->
        get_args n tys f (subs_shft (k,e)) s
    | Zapp l :: s ->
        let na = Array.length l in
        if n == na then (Inl (subs_cons(l,e)),s)
        else if n < na then (* more arguments *)
          let args = Array.sub l 0 n in
          let eargs = Array.sub l n (na-n) in
          (Inl (subs_cons(args,e)), Zapp eargs :: s)
        else (* more lambdas *)
          let etys = List.skipn na tys in
          get_args (n-na) etys f (subs_cons(l,e)) s
    | _ -> (Inr {norm=Cstr;term=FLambda(n,tys,f,e)}, stk)

(* Eta expansion: add a reference to implicit surrounding lambda at end of stack *)
let rec eta_expand_stack = function
  | (Zapp _ | Zfix _ | ZcaseT _ | Zproj _
	| Zshift _ | Zupdate _ as e) :: s ->
      e :: eta_expand_stack s
  | [] ->
      [Zshift 1; Zapp [|{norm=Norm; term= FRel 1}|]]

(* Iota reduction: extract the arguments to be passed to the Case
   branches *)
let rec reloc_rargs_rec depth stk =
  match stk with
      Zapp args :: s ->
        Zapp (lift_fconstr_vect depth args) :: reloc_rargs_rec depth s
    | Zshift(k)::s -> if Int.equal k depth then s else reloc_rargs_rec (depth-k) s
    | _ -> stk

let reloc_rargs depth stk =
  if Int.equal depth 0 then stk else reloc_rargs_rec depth stk

let rec try_drop_parameters depth n argstk =
  match argstk with
      Zapp args::s ->
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
    | _ -> assert false
	(* strip_update_shift_app only produces Zapp and Zshift items *)

let drop_parameters depth n argstk =
  try try_drop_parameters depth n argstk
  with Not_found ->
  (* we know that n < stack_args_size(argstk) (if well-typed term) *)
  anomaly (Pp.str "ill-typed term: found a match on a partially applied constructor.")

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
    let (depth, args, s) = strip_update_shift_app m s in
    (** Try to drop the params, might fail on partially applied constructors. *)
    let argss = try_drop_parameters depth pars args in
    let hstack = Array.map (fun p ->
        { norm = Red; (* right can't be a constructor though *)
          term = FProj (Projection.make p true, right) })
        projs
    in
    argss, [Zapp hstack]
  | None -> raise Not_found (* disallow eta-exp for non-primitive records *)

let rec project_nth_arg n argstk =
  match argstk with
  | Zapp args :: s ->
      let q = Array.length args in
	if n >= q then project_nth_arg (n - q) s
	else (* n < q *) args.(n)
  | _ -> assert false
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
    match fix with
      | FFix (((reci,i),(_,_,bds as rdcl)),env) ->
          (bds.(i),
	   (fun j -> { norm = Cstr; term = FFix (((reci,j),rdcl),env) }),
	   env, Array.length bds)
      | FCoFix ((i,(_,_,bds as rdcl)),env) ->
          (bds.(i),
	   (fun j -> { norm = Cstr; term = FCoFix ((j,rdcl),env) }),
	   env, Array.length bds)
      | _ -> assert false
  in
  (subs_cons(Array.init nfix make_body, env), thisbody)

let unfold_projection info p =
  if red_projection info.i_flags p
  then
    Some (Zproj (Projection.repr p))
  else None

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
    | FCaseT(ci,p,t,br,e) -> knh info t (ZcaseT(ci,p,br,e)::zupdate info m stk)
    | FFix(((ri,n),(_,_,_)),_) ->
        (match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh info arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FCast(t,_,_) -> knh info t stk
    | FProj (p,c) ->
      (match unfold_projection info p with
       | None -> (m, stk)
       | Some s -> knh info c (s :: zupdate info m stk))

(* cases where knh stops *)
    | (FFlex _|FLetIn _|FConstruct _|FEvar _|
       FCoFix _|FLambda _|FRel _|FAtom _|FInd _|FProd _) ->
        (m, stk)

(* The same for pure terms *)
and knht info e t stk =
  match kind t with
    | App(a,b) ->
        knht info e a (append_stack (mk_clos_vect e b) stk)
    | Case(ci,p,t,br) ->
        knht info e t (ZcaseT(ci, p, br, e)::stk)
    | Fix _ -> knh info (mk_clos2 e t) stk
    | Cast(a,_,_) -> knht info e a stk
    | Rel n -> knh info (clos_rel e n) stk
    | Proj (p,c) -> knh info (mk_clos2 e t) stk
    | (Lambda _|Prod _|Construct _|CoFix _|Ind _|
       LetIn _|Const _|Var _|Evar _|Meta _|Sort _) ->
        (mk_clos2 e t, stk)


(************************************************************************)

(* Computes a weak head normal form from the result of knh. *)
let rec knr info tab m stk =
  match m.term with
  | FLambda(n,tys,f,e) when red_set info.i_flags fBETA ->
      (match get_args n tys f e stk with
          Inl e', s -> knit info tab e' f s
        | Inr lam, s -> (lam,s))
  | FFlex(ConstKey (kn,_ as c)) when red_set info.i_flags (fCONST kn) ->
      (match ref_value_cache info tab (ConstKey c) with
          Some v -> kni info tab v stk
        | None -> (set_norm m; (m,stk)))
  | FFlex(VarKey id) when red_set info.i_flags (fVAR id) ->
      (match ref_value_cache info tab (VarKey id) with
          Some v -> kni info tab v stk
        | None -> (set_norm m; (m,stk)))
  | FFlex(RelKey k) when red_set info.i_flags fDELTA ->
      (match ref_value_cache info tab (RelKey k) with
          Some v -> kni info tab v stk
        | None -> (set_norm m; (m,stk)))
  | FConstruct((ind,c),u) ->
     let use_match = red_set info.i_flags fMATCH in
     let use_fix = red_set info.i_flags fFIX in
     if use_match || use_fix then
      (match strip_update_shift_app m stk with
        | (depth, args, ZcaseT(ci,_,br,e)::s) when use_match ->
            assert (ci.ci_npar>=0);
            let rargs = drop_parameters depth ci.ci_npar args in
            knit info tab e br.(c-1) (rargs@s)
        | (_, cargs, Zfix(fx,par)::s) when use_fix ->
            let rarg = fapp_stack(m,cargs) in
            let stk' = par @ append_stack [|rarg|] s in
            let (fxe,fxbd) = contract_fix_vect fx.term in
            knit info tab fxe fxbd stk'
        | (depth, args, Zproj p::s) when use_match ->
            let rargs = drop_parameters depth (Projection.Repr.npars p) args in
            let rarg = project_nth_arg (Projection.Repr.arg p) rargs in
            kni info tab rarg s
        | (_,args,s) -> (m,args@s))
     else (m,stk)
  | FCoFix _ when red_set info.i_flags fCOFIX ->
      (match strip_update_shift_app m stk with
          (_, args, (((ZcaseT _|Zproj _)::_) as stk')) ->
            let (fxe,fxbd) = contract_fix_vect m.term in
            knit info tab fxe fxbd (args@stk')
        | (_,args,s) -> (m,args@s))
  | FLetIn (_,v,_,bd,e) when red_set info.i_flags fZETA ->
      knit info tab (subs_cons([|v|],e)) bd stk
  | FEvar(ev,env) ->
      (match evar_value info.i_cache ev with
          Some c -> knit info tab env c stk
        | None -> (m,stk))
  | FLOCKED | FRel _ | FAtom _ | FCast _ | FFlex _ | FInd _ | FApp _ | FProj _
    | FFix _ | FCoFix _ | FCaseT _ | FLambda _ | FProd _ | FLetIn _ | FLIFT _
    | FCLOS _ -> (m, stk)


(* Computes the weak head normal form of a term *)
and kni info tab m stk =
  let (hm,s) = knh info m stk in
  knr info tab hm s
and knit info tab e t stk =
  let (ht,s) = knht info e t stk in
  knr info tab ht s

let kh info tab v stk = fapp_stack(kni info tab v stk)

(************************************************************************)

let rec zip_term zfun m stk =
  match stk with
    | [] -> m
    | Zapp args :: s ->
        zip_term zfun (mkApp(m, Array.map zfun args)) s
    | ZcaseT(ci,p,br,e)::s ->
        let t = mkCase(ci, zfun (mk_clos e p), m,
		       Array.map (fun b -> zfun (mk_clos e b)) br) in
        zip_term zfun t s
    | Zproj p::s ->
        let t = mkProj (Projection.make p true, m) in
	zip_term zfun t s
    | Zfix(fx,par)::s ->
        let h = mkApp(zip_term zfun (zfun fx) par,[|m|]) in
        zip_term zfun h s
    | Zshift(n)::s ->
        zip_term zfun (lift n m) s
    | Zupdate(rf)::s ->
        zip_term zfun m s

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
    zip_term (kl info tab) (norm_head info tab nm) s

(* no redex: go up for atoms and already normalized terms, go down
   otherwise. *)
and norm_head info tab m =
  if is_val m then (incr prune; term_of_fconstr m) else
    match m.term with
      | FLambda(n,tys,f,e) ->
          let (e',rvtys) =
            List.fold_left (fun (e,ctxt) (na,ty) ->
              (subs_lift e, (na,kl info tab (mk_clos e ty))::ctxt))
              (e,[]) tys in
          let bd = kl info tab (mk_clos e' f) in
          List.fold_left (fun b (na,ty) -> mkLambda(na,ty,b)) bd rvtys
      | FLetIn(na,a,b,f,e) ->
          let c = mk_clos (subs_lift e) f in
          mkLetIn(na, kl info tab a, kl info tab b, kl info tab c)
      | FProd(na,dom,rng) ->
          mkProd(na, kl info tab dom, kl info tab rng)
      | FCoFix((n,(na,tys,bds)),e) ->
          let ftys = Array.Fun1.map mk_clos e tys in
          let fbds =
            Array.Fun1.map mk_clos (subs_liftn (Array.length na) e) bds in
          mkCoFix(n,(na, CArray.map (kl info tab) ftys, CArray.map (kl info tab) fbds))
      | FFix((n,(na,tys,bds)),e) ->
          let ftys = Array.Fun1.map mk_clos e tys in
          let fbds =
            Array.Fun1.map mk_clos (subs_liftn (Array.length na) e) bds in
          mkFix(n,(na, CArray.map (kl info tab) ftys, CArray.map (kl info tab) fbds))
      | FEvar((i,args),env) ->
          mkEvar(i, Array.map (fun a -> kl info tab (mk_clos env a)) args)
      | FProj (p,c) ->
          mkProj (p, kl info tab c)
      | FLOCKED | FRel _ | FAtom _ | FCast _ | FFlex _ | FInd _ | FConstruct _
        | FApp _ | FCaseT _ | FLIFT _ | FCLOS _ -> term_of_fconstr m

(* Initialization and then normalization *)

(* weak reduction *)
let whd_val info tab v =
  with_stats (lazy (term_of_fconstr (kh info tab v [])))

(* strong reduction *)
let norm_val info tab v =
  with_stats (lazy (kl info tab v))

let inject c = mk_clos (subs_id 0) c

let whd_stack infos tab m stk = match m.norm with
| Whnf | Norm ->
  (** No need to perform [kni] nor to unlock updates because
      every head subterm of [m] is [Whnf] or [Norm] *)
  knh infos m stk
| Red | Cstr ->
  let k = kni infos tab m stk in
  let () = if infos.i_cache.i_share then ignore (fapp_stack k) in (* to unlock Zupdates! *)
  k

(* cache of constants: the body is computed only when needed. *)
type clos_infos = fconstr infos

let create_clos_infos ?(evars=fun _ -> None) flgs env =
  let share = (Environ.typing_flags env).Declarations.share_reduction in
  create ~share ~repr:(fun _ _ c -> inject c) flgs env evars

let create_tab () = KeyTable.create 17

let oracle_of_infos infos = Environ.oracle infos.i_cache.i_env

let env_of_infos infos = infos.i_cache.i_env

let infos_with_reds infos reds =
  { infos with i_flags = reds }

let unfold_reference info tab key =
  match key with
  | ConstKey (kn,_) ->
    if red_set info.i_flags (fCONST kn) then
      ref_value_cache info tab key
    else None
  | VarKey i ->
    if red_set info.i_flags (fVAR i) then
      ref_value_cache info tab key
    else None
  | _ -> ref_value_cache info tab key
