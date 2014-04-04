(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Cic
open Term
open Esubst
open Environ

let stats = ref false
let share = ref true

(* Profiling *)
let beta = ref 0
let delta = ref 0
let zeta = ref 0
let evar = ref 0
let iota = ref 0
let prune = ref 0

let reset () =
  beta := 0; delta := 0; zeta := 0; evar := 0; iota := 0; prune := 0

let stop() =
  msg_debug (str "[Reds: beta=" ++ int !beta ++ str" delta=" ++ int !delta ++
	 str" zeta=" ++ int !zeta ++ str" evar=" ++ int !evar ++
         str" iota=" ++ int !iota ++ str" prune=" ++ int !prune ++ str"]")

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

type transparent_state = Id.Pred.t * Cpred.t
let all_opaque = (Id.Pred.empty, Cpred.empty)
let all_transparent = (Id.Pred.full, Cpred.full)

let is_transparent_variable (ids, _) id = Id.Pred.mem id ids
let is_transparent_constant (_, csts) cst = Cpred.mem cst csts

module type RedFlagsSig = sig
  type reds
  type red_kind
  val fBETA : red_kind
  val fDELTA : red_kind
  val fIOTA : red_kind
  val fZETA : red_kind
  val fCONST : constant -> red_kind
  val fVAR : Id.t -> red_kind
  val no_red : reds
  val red_add : reds -> red_kind -> reds
  val mkflags : red_kind list -> reds
  val red_set : reds -> red_kind -> bool
end

module RedFlags = (struct

  (* [r_const=(true,cl)] means all constants but those in [cl] *)
  (* [r_const=(false,cl)] means only those in [cl] *)
  (* [r_delta=true] just mean [r_const=(true,[])] *)

  type reds = {
    r_beta : bool;
    r_delta : bool;
    r_const : transparent_state;
    r_zeta : bool;
    r_evar : bool;
    r_iota : bool }

  type red_kind = BETA | DELTA | IOTA | ZETA
	      | CONST of constant | VAR of Id.t
  let fBETA = BETA
  let fDELTA = DELTA
  let fIOTA = IOTA
  let fZETA = ZETA
  let fCONST kn  = CONST kn
  let fVAR id  = VAR id
  let no_red = {
    r_beta = false;
    r_delta = false;
    r_const = all_opaque;
    r_zeta = false;
    r_evar = false;
    r_iota = false }

  let red_add red = function
    | BETA -> { red with r_beta = true }
    | DELTA -> { red with r_delta = true; r_const = all_transparent }
    | CONST kn ->
	let (l1,l2) = red.r_const in
	{ red with r_const = l1, Cpred.add kn l2 }
    | IOTA -> { red with r_iota = true }
    | ZETA -> { red with r_zeta = true }
    | VAR id ->
	let (l1,l2) = red.r_const in
	{ red with r_const = Id.Pred.add id l1, l2 }

  let mkflags = List.fold_left red_add no_red

  let red_set red = function
    | BETA -> incr_cnt red.r_beta beta
    | CONST kn ->
	let (_,l) = red.r_const in
	let c = Cpred.mem kn l in
	incr_cnt c delta
    | VAR id -> (* En attendant d'avoir des kn pour les Var *)
	let (l,_) = red.r_const in
	let c = Id.Pred.mem id l in
	incr_cnt c delta
    | ZETA -> incr_cnt red.r_zeta zeta
    | IOTA -> incr_cnt red.r_iota iota
    | DELTA -> (* Used for Rel/Var defined in context *)
	incr_cnt red.r_delta delta

end : RedFlagsSig)

open RedFlags

let betadeltaiota = mkflags [fBETA;fDELTA;fZETA;fIOTA]
let betadeltaiotanolet = mkflags [fBETA;fDELTA;fIOTA]
let betaiotazeta = mkflags [fBETA;fIOTA;fZETA]

(* specification of the reduction function *)


(* Flags of reduction and cache of constants: 'a is a type that may be
 * mapped to constr. 'a infos implements a cache for constants and
 * abstractions, storing a representation (of type 'a) of the body of
 * this constant or abstraction.
 *  * i_tab is the cache table of the results
 *  * i_repr is the function to get the representation from the current
 *         state of the cache and the body of the constant. The result
 *         is stored in the table.
 *  * i_rels = (4,[(1,c);(3,d)]) means there are 4 free rel variables
 *    and only those with index 1 and 3 have bodies which are c and d resp.
 *
 * ref_value_cache searchs in the tab, otherwise uses i_repr to
 * compute the result and store it in the table. If the constant can't
 * be unfolded, returns None, but does not store this failure.  * This
 * doesn't take the RESET into account. You mustn't keep such a table
 * after a Reset.  * This type is not exported. Only its two
 * instantiations (cbv or lazy) are.
 *)

type table_key =
  | ConstKey of constant
  | VarKey of Id.t
  | RelKey of int

module KeyHash =
struct
  type t = table_key
  let equal k1 k2 = match k1, k2 with
  | ConstKey c1, ConstKey c2 -> Constant.UserOrd.equal c1 c2
  | VarKey id1, VarKey id2 -> Id.equal id1 id2
  | RelKey i1, RelKey i2 -> Int.equal i1 i2
  | (ConstKey _ | VarKey _ | RelKey _), _ -> false

  open Hashset.Combine

  let hash = function
  | ConstKey c -> combinesmall 1 (Constant.UserOrd.hash c)
  | VarKey id -> combinesmall 2 (Id.hash id)
  | RelKey i -> combinesmall 3 (Int.hash i)
end

module KeyTable = Hashtbl.Make(KeyHash)

type 'a infos = {
  i_flags : reds;
  i_repr : 'a infos -> constr -> 'a;
  i_env : env;
  i_rels : int * (int * constr) list;
  i_tab : 'a KeyTable.t }

let ref_value_cache info ref =
  try
    Some (KeyTable.find info.i_tab ref)
  with Not_found ->
  try
    let body =
      match ref with
	| RelKey n ->
	    let (s,l) = info.i_rels in lift n (Int.List.assoc (s-n) l)
	| VarKey id -> raise Not_found
	| ConstKey cst -> constant_value info.i_env cst
    in
    let v = info.i_repr info body in
    KeyTable.add info.i_tab ref v;
    Some v
  with
    | Not_found (* List.assoc *)
    | NotEvaluableConst _ (* Const *)
      -> None

let defined_rels flags env =
(*  if red_local_const (snd flags) then*)
  fold_rel_context
      (fun (id,b,t) (i,subs) ->
	 match b with
	   | None -> (i+1, subs)
	   | Some body -> (i+1, (i,body) :: subs))
      (rel_context env) ~init:(0,[])
(*  else (0,[])*)

let mind_equiv_infos info = mind_equiv info.i_env

let eq_table_key k1 k2 = 
 match k1,k2 with
   | ConstKey con1 ,ConstKey con2 -> eq_con_chk con1 con2
   | _,_  -> k1=k2

let create mk_cl flgs env =
  { i_flags = flgs;
    i_repr = mk_cl;
    i_env = env;
    i_rels = defined_rels flgs env;
    i_tab = KeyTable.create 17 }


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
  | FInd of inductive
  | FConstruct of constructor
  | FApp of fconstr * fconstr array
  | FFix of fixpoint * fconstr subs
  | FCoFix of cofixpoint * fconstr subs
  | FCases of case_info * fconstr * fconstr * fconstr array
  | FLambda of int * (name * constr) list * constr * fconstr subs
  | FProd of name * fconstr * fconstr
  | FLetIn of name * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential_key * fconstr array
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs
  | FLOCKED

let fterm_of v = v.term
let set_norm v = v.norm <- Norm

(* Could issue a warning if no is still Red, pointing out that we loose
   sharing. *)
let update v1 (no,t) =
  if !share then
    (v1.norm <- no;
     v1.term <- t;
     v1)
  else {norm=no;term=t}

(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *)

type stack_member =
  | Zapp of fconstr array
  | Zcase of case_info * fconstr * fconstr array
  | Zfix of fconstr * stack
  | Zshift of int
  | Zupdate of fconstr

and stack = stack_member list

let append_stack v s =
  if Array.length v = 0 then s else
  match s with
  | Zapp l :: s -> Zapp (Array.append v l) :: s
  | _ -> Zapp v :: s

(* Collapse the shifts in the stack *)
let zshift n s =
  match (n,s) with
      (0,_) -> s
    | (_,Zshift(k)::s) -> Zshift(n+k)::s
    | _ -> Zshift(n)::s

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
    | _ -> {norm=ft.norm; term=FLIFT(n,ft)}
let lift_fconstr k f =
  if k=0 then f else lft_fconstr k f
let lift_fconstr_vect k v =
  if k=0 then v else Array.map (fun f -> lft_fconstr k f) v

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
        let _ = update m (h'.norm,h'.term) in
        strip_rec depth s
    | stk -> zshift depth stk in
  strip_rec 0 stk

(* Put an update mark in the stack, only if needed *)
let zupdate m s =
  if !share && m.norm = Red
  then
    let s' = compact_stack m s in
    let _ = m.term <- FLOCKED in
    Zupdate(m)::s'
  else s

(* Closure optimization: *)
let rec compact_constr (lg, subs as s) c k =
  match c with
      Rel i ->
        if i < k then c,s else
          (try Rel (k + lg - List.index Int.equal (i-k+1) subs), (lg,subs)
          with Not_found -> Rel (k+lg), (lg+1, (i-k+1)::subs))
    | (Sort _|Var _|Meta _|Ind _|Const _|Construct _) -> c,s
    | Evar(ev,v) ->
        let (v',s) = compact_vect s v k in
        if v==v' then c,s else Evar(ev,v'),s
    | Cast(a,ck,b) ->
        let (a',s) = compact_constr s a k in
        let (b',s) = compact_constr s b k in
        if a==a' && b==b' then c,s else Cast(a', ck, b'), s
    | App(f,v) ->
        let (f',s) = compact_constr s f k in
        let (v',s) = compact_vect s v k in
        if f==f' && v==v' then c,s else App(f',v'), s
    | Lambda(n,a,b) ->
        let (a',s) = compact_constr s a k in
        let (b',s) = compact_constr s b (k+1) in
        if a==a' && b==b' then c,s else Lambda(n,a',b'), s
    | Prod(n,a,b) ->
        let (a',s) = compact_constr s a k in
        let (b',s) = compact_constr s b (k+1) in
        if a==a' && b==b' then c,s else Prod(n,a',b'), s
    | LetIn(n,a,ty,b) ->
        let (a',s) = compact_constr s a k in
        let (ty',s) = compact_constr s ty k in
        let (b',s) = compact_constr s b (k+1) in
        if a==a' && ty==ty' && b==b' then c,s else LetIn(n,a',ty',b'), s
    | Fix(fi,(na,ty,bd)) ->
        let (ty',s) = compact_vect s ty k in
        let (bd',s) = compact_vect s bd (k+Array.length ty) in
        if ty==ty' && bd==bd' then c,s else Fix(fi,(na,ty',bd')), s
    | CoFix(i,(na,ty,bd)) ->
        let (ty',s) = compact_vect s ty k in
        let (bd',s) = compact_vect s bd (k+Array.length ty) in
        if ty==ty' && bd==bd' then c,s else CoFix(i,(na,ty',bd')), s
    | Case(ci,p,a,br) ->
        let (p',s) = compact_constr s p k in
        let (a',s) = compact_constr s a k in
        let (br',s) = compact_vect s br k in
        if p==p' && a==a' && br==br' then c,s else Case(ci,p',a',br'),s
and compact_vect s v k = compact_v [] s v k (Array.length v - 1)
and compact_v acc s v k i =
  if i < 0 then
    let v' = Array.of_list acc in
    if Array.for_all2 (==) v v' then v,s else v',s
  else
    let (a',s') = compact_constr s v.(i) k in
    compact_v (a'::acc) s' v k (i-1)

(* Computes the minimal environment of a closure.
   Idea: if the subs is not identity, the term will have to be
   reallocated entirely (to propagate the substitution). So,
   computing the set of free variables does not change the
   complexity. *)
let optimise_closure env c =
  if is_subs_id env then (env,c) else
    let (c',(_,s)) = compact_constr (0,[]) c 1 in
    let env' =
      Array.map (fun i -> clos_rel env i) (Array.of_list s) in
    (subs_cons (env', subs_id 0),c')

let mk_lambda env t =
  let (env,t) = optimise_closure env t in
  let (rvars,t') = decompose_lam t in
  FLambda(List.length rvars, List.rev rvars, t', env)

let destFLambda clos_fun t =
  match t.term with
      FLambda(_,[(na,ty)],b,e) -> (na,clos_fun e ty,clos_fun (subs_lift e) b)
    | FLambda(n,(na,ty)::tys,b,e) ->
        (na,clos_fun e ty,{norm=Cstr;term=FLambda(n-1,tys,b,subs_lift e)})
    | _ -> assert false

(* Optimization: do not enclose variables in a closure.
   Makes variable access much faster *)
let mk_clos e t =
  match t with
    | Rel i -> clos_rel e i
    | Var x -> { norm = Red; term = FFlex (VarKey x) }
    | Const c -> { norm = Red; term = FFlex (ConstKey c) }
    | Meta _ | Sort _ ->  { norm = Norm; term = FAtom t }
    | Ind kn -> { norm = Norm; term = FInd kn }
    | Construct kn -> { norm = Cstr; term = FConstruct kn }
    | (CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _) ->
        {norm = Red; term = FCLOS(t,e)}

let mk_clos_vect env v = Array.map (mk_clos env) v

(* Translate the head constructor of t from constr to fconstr. This
   function is parameterized by the function to apply on the direct
   subterms.
   Could be used insted of mk_clos. *)
let mk_clos_deep clos_fun env t =
  match t with
    | (Rel _|Ind _|Const _|Construct _|Var _|Meta _ | Sort _) ->
        mk_clos env t
    | Cast (a,k,b) ->
        { norm = Red;
          term = FCast (clos_fun env a, k, clos_fun env b)}
    | App (f,v) ->
        { norm = Red;
	  term = FApp (clos_fun env f, Array.map (clos_fun env) v) }
    | Case (ci,p,c,v) ->
        { norm = Red;
	  term = FCases (ci, clos_fun env p, clos_fun env c,
			 Array.map (clos_fun env) v) }
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
    | Evar(ev,args) ->
	{ norm = Whnf; term = FEvar(ev,Array.map (clos_fun env) args) }

(* A better mk_clos? *)
let mk_clos2 = mk_clos_deep mk_clos

(* The inverse of mk_clos_deep: move back to constr *)
let rec to_constr constr_fun lfts v =
  match v.term with
    | FRel i -> Rel (reloc_rel i lfts)
    | FFlex (RelKey p) -> Rel (reloc_rel p lfts)
    | FFlex (VarKey x) -> Var x
    | FAtom c -> exliftn lfts c
    | FCast (a,k,b) ->
        Cast (constr_fun lfts a, k, constr_fun lfts b)
    | FFlex (ConstKey op) -> Const op
    | FInd op -> Ind op
    | FConstruct op -> Construct op
    | FCases (ci,p,c,ve) ->
	Case (ci, constr_fun lfts p,
              constr_fun lfts c,
	      Array.map (constr_fun lfts) ve)
    | FFix ((op,(lna,tys,bds)),e) ->
        let n = Array.length bds in
        let ftys = Array.map (mk_clos e) tys in
        let fbds = Array.map (mk_clos (subs_liftn n e)) bds in
	let lfts' = el_liftn n lfts in
	Fix (op, (lna, Array.map (constr_fun lfts) ftys,
	               Array.map (constr_fun lfts') fbds))
    | FCoFix ((op,(lna,tys,bds)),e) ->
        let n = Array.length bds in
        let ftys = Array.map (mk_clos e) tys in
        let fbds = Array.map (mk_clos (subs_liftn n e)) bds in
	let lfts' = el_liftn (Array.length bds) lfts in
	CoFix (op, (lna, Array.map (constr_fun lfts) ftys,
	                 Array.map (constr_fun lfts') fbds))
    | FApp (f,ve) ->
	App (constr_fun lfts f,
	       Array.map (constr_fun lfts) ve)
    | FLambda _ ->
        let (na,ty,bd) = destFLambda mk_clos2 v in
	Lambda (na, constr_fun lfts ty,
	            constr_fun (el_lift lfts) bd)
    | FProd (n,t,c)   ->
	Prod (n, constr_fun lfts t,
	         constr_fun (el_lift lfts) c)
    | FLetIn (n,b,t,f,e) ->
        let fc = mk_clos2 (subs_lift e) f in
	LetIn (n, constr_fun lfts b,
	          constr_fun lfts t,
	          constr_fun (el_lift lfts) fc)
    | FEvar (ev,args) -> Evar(ev,Array.map (constr_fun lfts) args)
    | FLIFT (k,a) -> to_constr constr_fun (el_shft k lfts) a
    | FCLOS (t,env) ->
        let fr = mk_clos2 env t in
        let unfv = update v (fr.norm,fr.term) in
        to_constr constr_fun lfts unfv
    | FLOCKED -> assert false (*mkVar(Id.of_string"_LOCK_")*)

(* This function defines the correspondance between constr and
   fconstr. When we find a closure whose substitution is the identity,
   then we directly return the constr to avoid possibly huge
   reallocation. *)
let term_of_fconstr =
  let rec term_of_fconstr_lift lfts v =
    match v.term with
      | FCLOS(t,env) when is_subs_id env && is_lift_id lfts -> t
      | FLambda(_,tys,f,e) when is_subs_id e && is_lift_id lfts ->
          compose_lam (List.rev tys) f
      | FFix(fx,e) when is_subs_id e && is_lift_id lfts -> Fix fx
      | FCoFix(cfx,e) when is_subs_id e && is_lift_id lfts -> CoFix cfx
      | _ -> to_constr term_of_fconstr_lift lfts v in
  term_of_fconstr_lift el_id



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
    | Zcase(ci,p,br)::s ->
        let t = FCases(ci, p, m, br) in
        zip {norm=neutr m.norm; term=t} s
    | Zfix(fx,par)::s ->
        zip fx (par @ append_stack [|m|] s)
    | Zshift(n)::s ->
        zip (lift_fconstr n m) s
    | Zupdate(rf)::s ->
        zip (update rf (m.norm,m.term)) s

let fapp_stack (m,stk) = zip m stk

(*********************************************************************)

(* The assertions in the functions below are granted because they are
   called only when m is a constructor, a cofix
   (strip_update_shift_app), a fix (get_nth_arg) or an abstraction
   (strip_update_shift, through get_arg). *)

(* optimised for the case where there are no shifts... *)
let strip_update_shift_app head stk =
  assert (head.norm <> Red);
  let rec strip_rec rstk h depth = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) (depth+k) s
    | (Zapp args :: s) ->
        strip_rec (Zapp args :: rstk)
          {norm=h.norm;term=FApp(h,args)} depth s
    | Zupdate(m)::s ->
        strip_rec rstk (update m (h.norm,h.term)) depth s
    | stk -> (depth,List.rev rstk, stk) in
  strip_rec [] head 0 stk


let get_nth_arg head n stk =
  assert (head.norm <> Red);
  let rec strip_rec rstk h n = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) n s
    | Zapp args::s' ->
        let q = Array.length args in
        if n >= q
        then
          strip_rec (Zapp args::rstk)
            {norm=h.norm;term=FApp(h,args)} (n-q) s'
        else
          let bef = Array.sub args 0 n in
          let aft = Array.sub args (n+1) (q-n-1) in
          let stk' =
            List.rev (if n = 0 then rstk else (Zapp bef :: rstk)) in
          (Some (stk', args.(n)), append_stack aft s')
    | Zupdate(m)::s ->
        strip_rec rstk (update m (h.norm,h.term)) n s
    | s -> (None, List.rev rstk @ s) in
  strip_rec [] head n stk

(* Beta reduction: look for an applied argument in the stack.
   Since the encountered update marks are removed, h must be a whnf *)
let rec get_args n tys f e stk =
  match stk with
      Zupdate r :: s ->
        let _hd = update r (Cstr,FLambda(n,tys,f,e)) in
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
  | (Zapp _ | Zfix _ | Zcase _ | Zshift _ | Zupdate _ as e) :: s ->
      e :: eta_expand_stack s
  | [] ->
      [Zshift 1; Zapp [|{norm=Norm; term= FRel 1}|]]

(* Iota reduction: extract the arguments to be passed to the Case
   branches *)
let rec reloc_rargs_rec depth stk =
  match stk with
      Zapp args :: s ->
        Zapp (lift_fconstr_vect depth args) :: reloc_rargs_rec depth s
    | Zshift(k)::s -> if k=depth then s else reloc_rargs_rec (depth-k) s
    | _ -> stk

let reloc_rargs depth stk =
  if depth = 0 then stk else reloc_rargs_rec depth stk

let rec drop_parameters depth n stk =
  match stk with
      Zapp args::s ->
        let q = Array.length args in
        if n > q then drop_parameters depth (n-q) s
        else if n = q then reloc_rargs depth s
        else
          let aft = Array.sub args n (q-n) in
          reloc_rargs depth (append_stack aft s)
    | Zshift(k)::s -> drop_parameters (depth-k) n s
    | [] -> assert (n=0); []
    | _ -> assert false (* we know that n < stack_args_size(stk) *)


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


(*********************************************************************)
(* A machine that inspects the head of a term until it finds an
   atom or a subterm that may produce a redex (abstraction,
   constructor, cofix, letin, constant), or a neutral term (product,
   inductive) *)
let rec knh m stk =
  match m.term with
    | FLIFT(k,a) -> knh a (zshift k stk)
    | FCLOS(t,e) -> knht e t (zupdate m stk)
    | FLOCKED -> assert false
    | FApp(a,b) -> knh a (append_stack b (zupdate m stk))
    | FCases(ci,p,t,br) -> knh t (Zcase(ci,p,br)::zupdate m stk)
    | FFix(((ri,n),(_,_,_)),_) ->
        (match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FCast(t,_,_) -> knh t stk
(* cases where knh stops *)
    | (FFlex _|FLetIn _|FConstruct _|FEvar _|
       FCoFix _|FLambda _|FRel _|FAtom _|FInd _|FProd _) ->
        (m, stk)

(* The same for pure terms *)
and knht e t stk =
  match t with
    | App(a,b) ->
        knht e a (append_stack (mk_clos_vect e b) stk)
    | Case(ci,p,t,br) ->
        knht e t (Zcase(ci, mk_clos e p, mk_clos_vect e br)::stk)
    | Fix _ -> knh (mk_clos2 e t) stk
    | Cast(a,_,_) -> knht e a stk
    | Rel n -> knh (clos_rel e n) stk
    | (Lambda _|Prod _|Construct _|CoFix _|Ind _|
       LetIn _|Const _|Var _|Evar _|Meta _|Sort _) ->
        (mk_clos2 e t, stk)


(************************************************************************)

(* Computes a weak head normal form from the result of knh. *)
let rec knr info m stk =
  match m.term with
  | FLambda(n,tys,f,e) when red_set info.i_flags fBETA ->
      (match get_args n tys f e stk with
          Inl e', s -> knit info e' f s
        | Inr lam, s -> (lam,s))
  | FFlex(ConstKey kn) when red_set info.i_flags (fCONST kn) ->
      (match ref_value_cache info (ConstKey kn) with
          Some v -> kni info v stk
        | None -> (set_norm m; (m,stk)))
  | FFlex(VarKey id) when red_set info.i_flags (fVAR id) ->
      (match ref_value_cache info (VarKey id) with
          Some v -> kni info v stk
        | None -> (set_norm m; (m,stk)))
  | FFlex(RelKey k) when red_set info.i_flags fDELTA ->
      (match ref_value_cache info (RelKey k) with
          Some v -> kni info v stk
        | None -> (set_norm m; (m,stk)))
  | FConstruct(ind,c) when red_set info.i_flags fIOTA ->
      (match strip_update_shift_app m stk with
          (depth, args, Zcase(ci,_,br)::s) ->
            assert (ci.ci_npar>=0);
            let rargs = drop_parameters depth ci.ci_npar args in
            kni info br.(c-1) (rargs@s)
        | (_, cargs, Zfix(fx,par)::s) ->
            let rarg = fapp_stack(m,cargs) in
            let stk' = par @ append_stack [|rarg|] s in
            let (fxe,fxbd) = contract_fix_vect fx.term in
            knit info fxe fxbd stk'
        | (_,args,s) -> (m,args@s))
  | FCoFix _ when red_set info.i_flags fIOTA ->
      (match strip_update_shift_app m stk with
          (_, args, ((Zcase _::_) as stk')) ->
            let (fxe,fxbd) = contract_fix_vect m.term in
            knit info fxe fxbd (args@stk')
        | (_,args,s) -> (m,args@s))
  | FLetIn (_,v,_,bd,e) when red_set info.i_flags fZETA ->
      knit info (subs_cons([|v|],e)) bd stk
  | _ -> (m,stk)

(* Computes the weak head normal form of a term *)
and kni info m stk =
  let (hm,s) = knh m stk in
  knr info hm s
and knit info e t stk =
  let (ht,s) = knht e t stk in
  knr info ht s

let kh info v stk = fapp_stack(kni info v stk)

(************************************************************************)
(* Initialization and then normalization *)

(* weak reduction *)
let whd_val info v =
  with_stats (lazy (term_of_fconstr (kh info v [])))

let inject = mk_clos (subs_id 0)

let whd_stack infos m stk =
  let k = kni infos m stk in
  let _ = fapp_stack k in (* to unlock Zupdates! *)
  k

(* cache of constants: the body is computed only when needed. *)
type clos_infos = fconstr infos

let create_clos_infos flgs env =
  create (fun _ -> inject) flgs env

let unfold_reference = ref_value_cache
