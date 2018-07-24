(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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
  Feedback.msg_debug (str "[Reds: beta=" ++ int !beta ++ str" delta=" ++ int !delta ++
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

module type RedFlagsSig = sig
  type reds
  type red_kind
  val fBETA : red_kind
  val fDELTA : red_kind
  val fIOTA : red_kind
  val fZETA : red_kind
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
    r_zeta : bool;
    r_evar : bool;
    r_iota : bool }

  type red_kind = BETA | DELTA | IOTA | ZETA

  let fBETA = BETA
  let fDELTA = DELTA
  let fIOTA = IOTA
  let fZETA = ZETA
  let no_red = {
    r_beta = false;
    r_delta = false;
    r_zeta = false;
    r_evar = false;
    r_iota = false }

  let red_add red = function
    | BETA -> { red with r_beta = true }
    | DELTA -> { red with r_delta = true}
    | IOTA -> { red with r_iota = true }
    | ZETA -> { red with r_zeta = true }

  let mkflags = List.fold_left red_add no_red

  let red_set red = function
    | BETA -> incr_cnt red.r_beta beta
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

type table_key = Constant.t puniverses tableKey


let eq_pconstant_key (c,u) (c',u') =
  eq_constant_key c c' && Univ.Instance.equal u u'

module KeyHash =
struct
  type t = table_key
  let equal = Names.eq_table_key eq_pconstant_key

  open Hashset.Combine

  let hash = function
  | ConstKey (c,u) -> combinesmall 1 (Constant.UserOrd.hash c)
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
      (fun decl (i,subs) ->
	 match decl with
	   | LocalAssum _ -> (i+1, subs)
	   | LocalDef (_,body,_) -> (i+1, (i,body) :: subs))
      (rel_context env) ~init:(0,[])
(*  else (0,[])*)

let mind_equiv_infos info = mind_equiv info.i_env

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
  | FEvar of existential_key * fconstr array (* why diff from kernel/closure? *)
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
  | ZcaseT of case_info * constr * constr array * fconstr subs
  | Zproj of Projection.Repr.t
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

let rec stack_args_size = function
  | Zapp v :: s -> Array.length v + stack_args_size s
  | Zshift(_)::s -> stack_args_size s
  | Zupdate(_)::s -> stack_args_size s
  | _ -> 0

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

let mk_lambda env t =
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
    | (CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _|Proj _) ->
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
    | Proj (p,c) ->
	{ norm = Red;
	  term = FProj (p, clos_fun env c) }
    | Case (ci,p,c,v) ->
        { norm = Red; term = FCaseT (ci, p, clos_fun env c, v, env) }
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
    | FCaseT (ci,p,c,ve,e) ->
       let fp = mk_clos2 e p in
       let fve = mk_clos_vect e ve in
       Case (ci, constr_fun lfts fp, constr_fun lfts c, Array.map (constr_fun lfts) fve)
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
    | FProj (p,c) ->
        Proj (p,constr_fun lfts c)
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
      | FCaseT(ci,p,c,b,env) when is_subs_id env && is_lift_id lfts ->
          Case(ci,p,term_of_fconstr_lift lfts c,b)
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
    | ZcaseT(ci,p,br,e)::s ->
        let t = FCaseT(ci, p, m, br, e) in
        zip {norm=neutr m.norm; term=t} s
    | Zproj p :: s ->
        zip {norm=neutr m.norm; term=FProj (Projection.make p true,m)} s
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
    | Zshift(k)::s -> if k=depth then s else reloc_rargs_rec (depth-k) s
    | _ -> stk

let reloc_rargs depth stk =
  if depth = 0 then stk else reloc_rargs_rec depth stk

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
  with Not_found -> assert false
    (* we know that n < stack_args_size(argstk) (if well-typed term) *) 

(** Projections and eta expansion *)

let eta_expand_ind_stack env ind m s (f, s') =
  let mib = lookup_mind (fst ind) env in
  (* disallow eta-exp for non-primitive records *)
  if not (mib.mind_finite == BiFinite) then raise Not_found;
  match Declarations.inductive_make_projections ind mib with
  | Some projs ->
    (* (Construct, pars1 .. parsm :: arg1...argn :: []) ~= (f, s') ->
       arg1..argn ~= (proj1 t...projn t) where t = zip (f,s') *)
    let pars = mib.mind_nparams in
    let right = fapp_stack (f, s') in
    let (depth, args, s) = strip_update_shift_app m s in
    (** Try to drop the params, might fail on partially applied constructors. *)
    let argss = try_drop_parameters depth pars args in
    let hstack =
      Array.map (fun p ->
          { norm = Red; (* right can't be a constructor though *)
            term = FProj (Projection.make p false, right) })
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

let unfold_projection env p =
  Zproj (Projection.repr p)

(*********************************************************************)
(* A machine that inspects the head of a term until it finds an
   atom or a subterm that may produce a redex (abstraction,
   constructor, cofix, letin, constant), or a neutral term (product,
   inductive) *)
let rec knh info m stk =
  match m.term with
    | FLIFT(k,a) -> knh info a (zshift k stk)
    | FCLOS(t,e) -> knht info e t (zupdate m stk)
    | FLOCKED -> assert false
    | FApp(a,b) -> knh info a (append_stack b (zupdate m stk))
    | FCaseT(ci,p,t,br,env) -> knh info t (ZcaseT(ci,p,br,env)::zupdate m stk)
    | FFix(((ri,n),(_,_,_)),_) ->
        (match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh info arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FCast(t,_,_) -> knh info t stk

    | FProj (p,c) ->
      if red_set info.i_flags fDELTA then
        let s = unfold_projection info.i_env p in
        knh info c (s :: zupdate m stk)
      else (m,stk)

(* cases where knh stops *)
    | (FFlex _|FLetIn _|FConstruct _|FEvar _|
       FCoFix _|FLambda _|FRel _|FAtom _|FInd _|FProd _) ->
        (m, stk)

(* The same for pure terms *)
and knht info e t stk =
  match t with
    | App(a,b) ->
        knht info e a (append_stack (mk_clos_vect e b) stk)
    | Case(ci,p,t,br) -> knht info e t (ZcaseT(ci, p, br, e)::stk)
    | Fix _ -> knh info (mk_clos2 e t) stk (* laziness *)
    | Cast(a,_,_) -> knht info  e a stk
    | Rel n -> knh info (clos_rel e n) stk
    | Proj (p,c) -> knh info (mk_clos2 e t) stk (* laziness *)
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
  | FFlex(ConstKey kn) when red_set info.i_flags fDELTA ->
      (match ref_value_cache info (ConstKey kn) with
          Some v -> kni info v stk
        | None -> (set_norm m; (m,stk)))
  | FFlex(VarKey id) when red_set info.i_flags fDELTA ->
      (match ref_value_cache info (VarKey id) with
          Some v -> kni info v stk
        | None -> (set_norm m; (m,stk)))
  | FFlex(RelKey k) when red_set info.i_flags fDELTA ->
      (match ref_value_cache info (RelKey k) with
          Some v -> kni info v stk
        | None -> (set_norm m; (m,stk)))
  | FConstruct((ind,c),u) when red_set info.i_flags fIOTA ->
      (match strip_update_shift_app m stk with
       | (depth, args, ZcaseT(ci,_,br,env)::s) ->
            assert (ci.ci_npar>=0);
            let rargs = drop_parameters depth ci.ci_npar args in
            knit info env br.(c-1) (rargs@s)
       | (_, cargs, Zfix(fx,par)::s) ->
            let rarg = fapp_stack(m,cargs) in
            let stk' = par @ append_stack [|rarg|] s in
            let (fxe,fxbd) = contract_fix_vect fx.term in
            knit info fxe fxbd stk'
       | (depth, args, Zproj p::s) ->
            let rargs = drop_parameters depth (Projection.Repr.npars p) args in
            let rarg = project_nth_arg (Projection.Repr.arg p) rargs in
	    kni info rarg s
       | (_,args,s) -> (m,args@s))
  | FCoFix _ when red_set info.i_flags fIOTA ->
      (match strip_update_shift_app m stk with
          (_, args, (((ZcaseT _|Zproj _)::_) as stk')) ->
            let (fxe,fxbd) = contract_fix_vect m.term in
            knit info fxe fxbd (args@stk')
        | (_,args,s) -> (m,args@s))
  | FLetIn (_,v,_,bd,e) when red_set info.i_flags fZETA ->
      knit info (subs_cons([|v|],e)) bd stk
  | _ -> (m,stk)

(* Computes the weak head normal form of a term *)
and kni info m stk =
  let (hm,s) = knh info m stk in
  knr info hm s
and knit info e t stk =
  let (ht,s) = knht info e t stk in
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

let infos_env x = x.i_env
let infos_flags x = x.i_flags
let oracle_of_infos x = x.i_env.env_conv_oracle

let create_clos_infos flgs env =
  create (fun _ -> inject) flgs env

let unfold_reference = ref_value_cache
