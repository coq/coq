(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created under Benjamin Werner account by Bruno Barras to implement
   a call-by-value conversion algorithm and a lazy reduction machine
   with sharing, Nov 1996 *)
(* Addition of zeta-reduction (let-in contraction) by Hugo Herbelin, Oct 2000 *)
(* Irreversibility of opacity by Bruno Barras *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)
(* Equal inductive types by Jacek Chrzaszcz as part of the module
   system, Aug 2002 *)

open CErrors
open Util
open Names
open Constr
open Declarations
open Environ
open CClosure
open Esubst

let rec is_empty_stack = function
  [] -> true
  | Zupdate _::s -> is_empty_stack s
  | Zshift _::s -> is_empty_stack s
  | _ -> false

(* Compute the lift to be performed on a term placed in a given stack *)
let el_stack el stk =
  let n =
    List.fold_left
      (fun i z ->
        match z with
            Zshift n -> i+n
          | _ -> i)
      0
      stk in
  el_shft n el

let compare_stack_shape stk1 stk2 =
  let rec compare_rec bal stk1 stk2 =
  match (stk1,stk2) with
      ([],[]) -> Int.equal bal 0
    | ((Zupdate _|Zshift _)::s1, _) -> compare_rec bal s1 stk2
    | (_, (Zupdate _|Zshift _)::s2) -> compare_rec bal stk1 s2
    | (Zapp l1::s1, _) -> compare_rec (bal+Array.length l1) s1 stk2
    | (_, Zapp l2::s2) -> compare_rec (bal-Array.length l2) stk1 s2
    | (Zproj _::s1, Zproj _::s2) ->
        Int.equal bal 0 && compare_rec 0 s1 s2
    | (ZcaseT(_c1,_,_,_,_,_)::s1, ZcaseT(_c2,_,_,_,_,_)::s2) ->
        Int.equal bal 0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
    | (Zfix(_,a1)::s1, Zfix(_,a2)::s2) ->
        Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
    | Zprimitive(op1,_,rargs1, _kargs1)::s1, Zprimitive(op2,_,rargs2, _kargs2)::s2 ->
        bal=0 && op1=op2 && List.length rargs1=List.length rargs2 &&
        compare_rec 0 s1 s2
    | [], _ :: _
    | (Zproj _ | ZcaseT _ | Zfix _ | Zprimitive _) :: _, _ -> false
  in
  compare_rec 0 stk1 stk2

type lft_fconstr = lift * fconstr

type lft_constr_stack_elt =
    Zlapp of (lift * fconstr) array
  | Zlproj of Projection.Repr.t * lift
  | Zlfix of (lift * fconstr) * lft_constr_stack
  | Zlcase of case_info * lift * UVars.Instance.t * constr array * case_return * case_branch array * usubs
  | Zlprimitive of
     CPrimitives.t * pconstant * lft_fconstr list * lft_fconstr next_native_args
and lft_constr_stack = lft_constr_stack_elt list

let rec zlapp v = function
    Zlapp v2 :: s -> zlapp (Array.append v v2) s
  | s -> Zlapp v :: s

(** Hand-unrolling of the map function to bypass the call to the generic array
    allocation. Type annotation is required to tell OCaml that the array does
    not contain floats. *)
let map_lift (l : lift) (v : fconstr array) = match v with
| [||] -> assert false
| [|c0|] -> [|(l, c0)|]
| [|c0; c1|] -> [|(l, c0); (l, c1)|]
| [|c0; c1; c2|] -> [|(l, c0); (l, c1); (l, c2)|]
| [|c0; c1; c2; c3|] -> [|(l, c0); (l, c1); (l, c2); (l, c3)|]
| v -> Array.Fun1.map (fun l t -> (l, t)) l v

let pure_stack lfts stk =
  let rec pure_rec lfts stk =
    match stk with
        [] -> (lfts,[])
      | zi::s ->
          (match (zi,pure_rec lfts s) with
              (Zupdate _,lpstk)  -> lpstk
            | (Zshift n,(l,pstk)) -> (el_shft n l, pstk)
            | (Zapp a, (l,pstk)) ->
                (l,zlapp (map_lift l a) pstk)
            | (Zproj (p,_), (l,pstk)) ->
                (l, Zlproj (p,l)::pstk)
            | (Zfix(fx,a),(l,pstk)) ->
                let (lfx,pa) = pure_rec l a in
                (l, Zlfix((lfx,fx),pa)::pstk)
            | (ZcaseT(ci,u,pms,p,br,e),(l,pstk)) ->
                (l,Zlcase(ci,l,u,pms,p,br,e)::pstk)
            | (Zprimitive(op,c,rargs,kargs),(l,pstk)) ->
                (l,Zlprimitive(op,c,List.map (fun t -> (l,t)) rargs,
                            List.map (fun (k,t) -> (k,(l,t))) kargs)::pstk))
  in
  snd (pure_rec lfts stk)

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

(* Conversion utility functions *)

(* functions of this type are called from the kernel *)
type 'a kernel_conversion_function = env -> 'a -> 'a -> (unit, unit) result

(* functions of this type can be called from outside the kernel *)
type 'a extended_conversion_function =
  ?l2r:bool -> ?reds:TransparentState.t -> env ->
  ?evars:evar_handler ->
  'a -> 'a -> (unit, unit) result

type payload = ..

exception NotConvertible
exception NotConvertibleTrace of payload

(* Convertibility of sorts *)

(* The sort cumulativity is

    Prop <= Set <= Type 1 <= ... <= Type i <= ...

    and this holds whatever Set is predicative or impredicative
*)

type conv_pb =
  | CONV
  | CUMUL

type ('a, 'err) universe_compare = {
  compare_sorts : conv_pb -> Sorts.t -> Sorts.t -> 'a -> ('a, 'err option) result;
  compare_instances: flex:bool -> UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
  compare_cumul_instances : conv_pb -> UVars.Variance.t array ->
    UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
  compare_irrelevant : bool;
}

type ('a, 'err) universe_state = 'a * ('a, 'err) universe_compare

type ('a, 'err) generic_conversion_function = ('a, 'err) universe_state -> constr -> constr -> ('a, 'err option) result

let sort_cmp_universes pb s0 s1 (u, check) =
  (check.compare_sorts pb s0 s1 u, check)

(* [flex] should be true for constants, false for inductive types and
   constructors. *)
let convert_instances ~flex u u' (s, check) =
  (check.compare_instances ~flex u u' s, check)

exception MustExpand

let convert_instances_cumul pb var u u' (s, check) =
  (check.compare_cumul_instances pb var u u' s, check)

let get_cumulativity_constraints cv_pb variance u u' =
  match cv_pb with
  | CONV ->
    UVars.enforce_eq_variance_instances variance u u' (UVars.QPairSet.empty, Univ.UnivConstraints.empty)
  | CUMUL ->
    UVars.enforce_leq_variance_instances variance u u' (UVars.QPairSet.empty, Univ.UnivConstraints.empty)

let inductive_cumulativity_arguments (mind,ind) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_nrealargs

let convert_inductives_gen cmp_instances cmp_cumul cv_pb (mind,ind) nargs u1 u2 s =
  match mind.Declarations.mind_variance with
  | None -> cmp_instances u1 u2 s
  | Some variances ->
    let num_param_arity = inductive_cumulativity_arguments (mind,ind) in
    if not (Int.equal num_param_arity nargs) then
      (* shortcut, not sure if worth doing, could use perf data *)
      if UVars.Instance.equal u1 u2 then Result.Ok s else raise MustExpand
    else
      cmp_cumul cv_pb variances u1 u2 s

(* Conversion result cache. Within one conversion session the same pair of
   cells is typically compared many times over, because β-substitution
   shares payload cells across all the occurrences of a variable. Entries
   record the outcome (success or failure) for a pair of cells — identified
   by their stable ids, modulo FLIFT wrappers — at a given lift pair and
   conversion problem. Lifts are interned to small ids so that keys and
   payloads fit in machine integers, stored in a flat open-addressing
   table. Only sound for checked conversion, where results are
   deterministic and no universe constraints are accumulated. *)

module LiftTbl = Hashtbl.Make(struct
  type t = lift
  let equal = eq_lift
  let hash = hash_lift
end)

(* (node, subst)-keyed closure-pair memo: the second level of the
   conversion cache. Probed for FCLOS/FCLOS pairs when the cell-id lookup
   misses: keyed on the identity of the closure components (body constr by
   pointer, substitution by the spine of cells it contains), so distinct
   cells rebuilt over the same closure still hit. Session-scoped like the
   first level. On by default; ROCQ_CLOS_MEMO=0 disables it, =stats counts
   hits without acting on them (diagnostics); ROCQ_CLOS_MEMO_STATS=1
   prints the counters at exit. *)

type clos_pair_key = {
  ck_hash : int; (* precomputed [clos_pair_hash], stable: see below *)
  ck_c1 : Constr.t;
  ck_s1 : subs_content Esubst.subs;
  ck_u1 : UVars.Instance.t;
  ck_c2 : Constr.t;
  ck_s2 : subs_content Esubst.subs;
  ck_u2 : UVars.Instance.t;
  ck_lid1 : int;
  ck_lid2 : int;
  ck_pb : int;
}

(* Substitutions are fingerprinted and compared through the stable fids of
   the cells on their spine: keys with the same spine denote the same
   substitution (the cells are shared), and fids survive the in-place cell
   updates that make content hashing unstable. Content hashing would also
   collide massively here, since keys typically differ only in their
   substitutions. The fingerprint and the comparison go through
   [Esubst.Internal.fold]/[equal] rather than [repr] to avoid
   materializing the spine as a list on every probe. *)
let subs_hash_rel h i = h * 0x9E3779B9 + (i * 2 + 1)
let subs_hash_val h k sc = h * 0x9E3779B9 + ((subs_content_fid sc lsl 5) lxor (k * 2))

let subs_hash s =
  let (h, shft) = Esubst.Internal.fold subs_hash_rel subs_hash_val 0 s in
  h * 0x9E3779B9 + shft

let subs_equal s1 s2 = Esubst.Internal.equal subs_content_equal s1 s2

(* Computed once per probe, at key construction: the deep body traversals
   dominate the probe cost, and the [find]-then-[add] pattern would
   otherwise hash the same key twice on the insert path. Stability: bodies
   are immutable constrs and the substitution fingerprint only reads cell
   fids, which survive in-place cell updates. *)
let clos_pair_hash c1 s1 c2 s2 lid1 lid2 pb =
  (* The default shallow constr hash (10 meaningful nodes) collides on
     self-similar telescope terms; traverse deeper at bounded cost. *)
  Stdlib.Hashtbl.hash
    (Stdlib.Hashtbl.hash_param 128 256 c1,
     Stdlib.Hashtbl.hash_param 128 256 c2,
     subs_hash s1, subs_hash s2,
     lid1, lid2, pb)

module ClosPairKey = struct
  type t = clos_pair_key
  let equal (a : t) (b : t) =
    Int.equal a.ck_hash b.ck_hash
    && a.ck_c1 == b.ck_c1 && a.ck_c2 == b.ck_c2
    && Int.equal a.ck_lid1 b.ck_lid1 && Int.equal a.ck_lid2 b.ck_lid2
    && Int.equal a.ck_pb b.ck_pb
    && subs_equal a.ck_s1 b.ck_s1 && subs_equal a.ck_s2 b.ck_s2
    && (a.ck_u1 == b.ck_u1 || UVars.Instance.equal a.ck_u1 b.ck_u1)
    && (a.ck_u2 == b.ck_u2 || UVars.Instance.equal a.ck_u2 b.ck_u2)
end

(* Bounded structural hashes can coincide for many distinct body pointers.
   Keep at most 16 full keys per hash so these collisions cannot cause
   unbounded full-key scans. Saturated buckets lose memoization entries;
   every hit still requires the complete key comparison. *)
module ClosHashTbl = Hashtbl.Make(struct
  type t = int
  let equal = Int.equal
  let hash h = h
end)
module ClosPairTbl = struct
  type 'a bucket = { mutable count : int; mutable entries : (clos_pair_key * 'a) list }
  type 'a t = 'a bucket ClosHashTbl.t
  let create = ClosHashTbl.create
  let find_opt table key =
    match ClosHashTbl.find_opt table key.ck_hash with
    | None -> None
    | Some bucket ->
      let rec find = function
      | [] -> None
      | (k, v) :: rest ->
        if ClosPairKey.equal k key then Some v else find rest
      in
      find bucket.entries
  (* Conversion between lookup and insertion may have filled the bucket. *)
  let add table key value =
    match ClosHashTbl.find_opt table key.ck_hash with
    | None ->
      ClosHashTbl.add table key.ck_hash { count = 1; entries = [key, value] };
      true
    | Some bucket ->
      if bucket.count < 16 then begin
        bucket.count <- bucket.count + 1;
        bucket.entries <- (key, value) :: bucket.entries;
        true
      end else false
end

(* Pointer pair of bodies only: upper bound on what any (node, subst)
   design could hit, however clever its substitution comparison. *)
module BodyPairTbl = Hashtbl.Make(struct
  type t = Constr.t * Constr.t
  let equal (a1, b1) (a2, b2) = a1 == a2 && b1 == b2
  let hash (a, b) =
    Stdlib.Hashtbl.hash
      (Stdlib.Hashtbl.hash_param 128 256 a, Stdlib.Hashtbl.hash_param 128 256 b)
end)

type clos_pair_tables = {
  cp_full : int ClosPairTbl.t;
  cp_bodies : unit BodyPairTbl.t;
}

let clos_memo_mode = (* 0 = off, 1 = stats only, 2 = active (default) *)
  match Sys.getenv "ROCQ_CLOS_MEMO" with
  | "stats" -> 1
  | "0" -> 0
  | _ -> 2
  | exception Not_found -> 2

let clos_memo_print_stats =
  match Sys.getenv "ROCQ_CLOS_MEMO_STATS" with
  | "0" -> false
  | _ -> true
  | exception Not_found -> false

let clos_memo_probes = ref 0
let clos_memo_full_hits = ref 0
let clos_memo_body_hits = ref 0
let clos_memo_inserts = ref 0

let () =
  if clos_memo_mode = 1 || clos_memo_print_stats then
    at_exit (fun () ->
      Printf.eprintf
        "[clos-memo] probes %d full-hits %d body-hits %d inserts %d\n%!"
        !clos_memo_probes !clos_memo_full_hits !clos_memo_body_hits
        !clos_memo_inserts)

type conv_cache = {
  (* cc_key.(i) = (fid1 lsl 31) lor fid2; 0 = empty slot *)
  mutable cc_key : int array;
  (* cc_meta.(i) = (lid1 lsl 18) lor (lid2 lsl 3) lor (pb lsl 1) lor result *)
  mutable cc_meta : int array;
  mutable cc_cnt : int;
  cc_lifts : int LiftTbl.t;
  mutable cc_nlifts : int;
  cc_clos : clos_pair_tables option;
  mutable max_uid : int;
}

let cc_intern cache l = match l with
| ELID -> 0
| _ ->
  match LiftTbl.find_opt cache.cc_lifts l with
  | Some id -> id
  | None ->
    let id = cache.cc_nlifts in
    if id >= 1 lsl 15 then -1
    else begin
      cache.cc_nlifts <- id + 1;
      LiftTbl.add cache.cc_lifts l id;
      id
    end

let cc_mix pk m =
  let h = pk + m * 0x9E3779B97F4A7C1 in
  let h = h lxor (h lsr 29) in
  let h = h * 0x3F58476D1CE4E5B9 in
  h lxor (h lsr 32)

(* -1 = absent, 0 = cached failure, 1 = cached success.
   [meta0] must have the result bit clear. *)
let cc_find cache pk meta0 =
  if pk lsr 31 > cache.max_uid || pk land 0x7fffffff > cache.max_uid then -1
  else
  let mask = Array.length cache.cc_key - 1 in
  let rec go i =
    let k = Array.unsafe_get cache.cc_key i in
    if k == 0 then -1
    else if k == pk
         && (Array.unsafe_get cache.cc_meta i) lor 1 == meta0 lor 1 then
      (Array.unsafe_get cache.cc_meta i) land 1
    else go ((i + 1) land mask)
  in
  go ((cc_mix pk meta0) land mask)

let cc_insert_raw key meta pk m =
  let mask = Array.length key - 1 in
  let rec go i =
    if Array.unsafe_get key i == 0 then begin
      Array.unsafe_set key i pk;
      Array.unsafe_set meta i m
    end else go ((i + 1) land mask)
  in
  go ((cc_mix pk (m land lnot 1)) land mask)

let cc_resize cache =
  let old_k = cache.cc_key and old_m = cache.cc_meta in
  let n = Array.length old_k * 2 in
  let key = Array.make n 0 and meta = Array.make n 0 in
  for i = 0 to Array.length old_k - 1 do
    let pk = Array.unsafe_get old_k i in
    if pk != 0 then cc_insert_raw key meta pk (Array.unsafe_get old_m i)
  done;
  cache.cc_key <- key;
  cache.cc_meta <- meta

type 'e conv_tab = {
  cnv_inf : clos_infos;
  cnv_typ : bool; (* true if the input terms were well-typed *)
  lft_tab : clos_tab;
  rgt_tab : clos_tab;
  err_ret : 'e -> payload;
  cnv_cache : conv_cache option;
}
(** Invariant: for any tl ∈ lft_tab and tr ∈ rgt_tab, there is no mutable memory
    location contained both in tl and in tr. *)

let fail_check (infos : 'err conv_tab) (state, check) = match state with
| Result.Ok state -> (state, check)
| Result.Error None -> raise NotConvertible
| Result.Error (Some err) -> raise (NotConvertibleTrace (infos.err_ret err))

let convert_inductives cv_pb ind nargs u1 u2 (s, check) =
  convert_inductives_gen (check.compare_instances ~flex:false) check.compare_cumul_instances
    cv_pb ind nargs u1 u2 s, check

let constructor_cumulativity_arguments (mind, ind, ctor) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_consnrealargs.(ctor - 1)

let convert_constructors_gen cmp_instances cmp_cumul (mind, ind, cns) nargs u1 u2 s =
  match mind.Declarations.mind_variance with
  | None -> cmp_instances u1 u2 s
  | Some _ ->
    let num_cnstr_args = constructor_cumulativity_arguments (mind,ind,cns) in
    if not (Int.equal num_cnstr_args nargs) then
      if UVars.Instance.equal u1 u2 then Result.Ok s else raise MustExpand
    else
      (** By invariant, both constructors have a common supertype,
          so they are convertible _at that type_. *)
      (* NB: no variance for qualities *)
      let variance = Array.make (snd (UVars.Instance.length u1)) UVars.Variance.Irrelevant in
      cmp_cumul CONV variance u1 u2 s

let convert_constructors ctor nargs u1 u2 (s, check) =
  convert_constructors_gen (check.compare_instances ~flex:false) check.compare_cumul_instances
    ctor nargs u1 u2 s, check

let conv_table_key infos ~nargs k1 k2 cuniv =
  if k1 == k2 then cuniv else
  match k1, k2 with
  | ConstKey (cst, u), ConstKey (cst', u') when Constant.CanOrd.equal cst cst' ->
    if UVars.Instance.equal u u' then cuniv
    else if Int.equal nargs 1 && is_array_type (info_env infos.cnv_inf) cst then cuniv
    else
      let flex = evaluable_constant cst (info_env infos.cnv_inf)
        && RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST cst)
      in fail_check infos @@ convert_instances ~flex u u' cuniv
  | VarKey id, VarKey id' when Id.equal id id' -> cuniv
  | RelKey n, RelKey n' when Int.equal n n' -> cuniv
  | _ -> raise NotConvertible

let same_args_size sk1 sk2 =
  let n = CClosure.stack_args_size sk1 in
  if Int.equal n (CClosure.stack_args_size sk2) then n
  else raise NotConvertible

(** The same heap separation invariant must hold for the fconstr arguments
    passed to each respective side of the conversion function below. *)

let push_relevance infos r =
  { infos with cnv_inf = CClosure.push_relevance infos.cnv_inf r }

let push_relevances infos nas =
  { infos with cnv_inf = CClosure.push_relevances infos.cnv_inf nas }

let identity_of_ctx (ctx:Constr.rel_context) =
  Context.Rel.instance mkRel 0 ctx

let get_template_instance mib u = match mib.mind_template with
| None -> u
| Some templ ->
  let () = assert (UVars.Instance.is_empty u) in
  templ.template_defaults

(* ind -> fun args => ind args *)
let eta_expand_ind env (ind,u as pind) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context (get_template_instance mib u) mip.mind_arity_ctxt in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkIndU pind, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  inject c

let eta_expand_constructor env ((ind,ctor),u as pctor) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context (get_template_instance mib u) (fst mip.mind_nf_lc.(ctor-1)) in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkConstructU pctor, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  inject c

let irr_flex infos = function
  | ConstKey (con,u) -> is_irrelevant infos @@ UVars.subst_instance_relevance u @@ Environ.constant_relevance con (info_env infos)
  | VarKey x -> is_irrelevant infos @@ Context.Named.Declaration.get_relevance (Environ.lookup_named x (info_env infos))
  | RelKey x -> is_irrelevant infos @@ Context.Rel.Declaration.get_relevance (Environ.lookup_rel x (info_env infos))

let eq_universes (_,e1) (_,e2) u1 u2 =
  let subst e u = if UVars.Instance.is_empty e then u else UVars.subst_instance_instance e u in
  UVars.Instance.equal (subst e1 u1) (subst e2 u2)

let eq_usubs_fast (s1, u1) (s2, u2) =
  (s1 == s2 || (Esubst.is_subs_id s1 && Esubst.is_subs_id s2)) &&
  (u1 == u2 || UVars.Instance.equal u1 u2)

let rec compare_under e1 c1 e2 c2 =
  (c1 == c2 && eq_usubs_fast e1 e2)
  ||
  match Constr.kind c1, Constr.kind c2 with
  | Cast (c1, _, _), _ -> compare_under e1 c1 e2 c2
  | _, Cast (c2, _, _) -> compare_under e1 c1 e2 c2
  | Rel i, Rel j -> begin match Esubst.expand_rel i (fst e1) with
      | Inl _ -> false
      | Inr (k, _) -> begin match Esubst.expand_rel j (fst e2) with
          | Inl _ -> false
          | Inr (k', _) -> Int.equal k k'
        end
    end
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Id.equal id1 id2
  | Int i1, Int i2 -> Uint63.equal i1 i2
  | Float f1, Float f2 -> Float64.equal f1 f2
  | String s1, String s2 -> Pstring.equal s1 s2
  | Sort s1, Sort s2 ->
    let subst_instance_sort u s =
      if UVars.Instance.is_empty u then s else UVars.subst_instance_sort u s
    in
    let s1 = subst_instance_sort (snd e1) s1
    and s2 = subst_instance_sort (snd e2) s2 in
    Sorts.equal s1 s2
  | Prod (_,t1,c1), Prod (_,t2,c2) ->
    compare_under e1 t1 e2 t2
    && compare_under (usubs_lift e1) c1 (usubs_lift e2) c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
    compare_under e1 t1 e2 t2
    && compare_under (usubs_lift e1) c1 (usubs_lift e2) c2
  | LetIn (_,b1,_,c1), LetIn (_,b2,_,c2) ->
    (* don't care about types when bodies are equal *)
    compare_under e1 b1 e2 b2
    && compare_under (usubs_lift e1) c1 (usubs_lift e2) c2
  | App (c1, l1), App (c2, l2) ->
    let len = Array.length l1 in
    Int.equal len (Array.length l2)
    && compare_under e1 c1 e2 c2
    && Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) l1 l2
  | Proj (p1,_,c1), Proj (p2,_,c2) ->
    Projection.UserOrd.equal p1 p2 && compare_under e1 c1 e2 c2
  | Evar _, Evar _ -> false
  | Const (c1,u1), Const (c2,u2) ->
    (* The args length currently isn't used but may as well pass it. *)
    Constant.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Ind (c1,u1), Ind (c2,u2) -> Ind.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Construct (c1,u1), Construct (c2,u2) ->
    Construct.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Case (ci1, u1, pms1, ((nas1, p1), _), _, s1, br1),
    Case (ci2, u2, pms2, ((nas2, p2), _), _, s2, br2) ->
    Ind.UserOrd.equal ci1.ci_ind ci2.ci_ind
    && eq_universes e1 e2 u1 u2
    && Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) pms1 pms2
    && Int.equal (Array.length nas1) (Array.length nas2)
    && compare_under (usubs_liftn (Array.length nas1) e1) p1
         (usubs_liftn (Array.length nas2) e2) p2
    && compare_under e1 s1 e2 s2
    && Array.equal_norefl (fun (nas1, b1) (nas2, b2) ->
         Int.equal (Array.length nas1) (Array.length nas2)
         && compare_under (usubs_liftn (Array.length nas1) e1) b1
              (usubs_liftn (Array.length nas2) e2) b2) br1 br2
  | Fix ((ln1, i1), (_, tl1, bl1)), Fix ((ln2, i2), (_, tl2, bl2)) ->
    Int.equal i1 i2 && Array.equal Int.equal ln1 ln2
    && Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) tl1 tl2
    && (let n = Array.length tl1 in
        Array.equal_norefl (fun c1 c2 ->
          compare_under (usubs_liftn n e1) c1 (usubs_liftn n e2) c2) bl1 bl2)
  | CoFix (i1, (_, tl1, bl1)), CoFix (i2, (_, tl2, bl2)) ->
    Int.equal i1 i2
    && Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) tl1 tl2
    && (let n = Array.length tl1 in
        Array.equal_norefl (fun c1 c2 ->
          compare_under (usubs_liftn n e1) c1 (usubs_liftn n e2) c2) bl1 bl2)
  | Array(_,t1,def1,ty1), Array(_,t2,def2,ty2) ->
    Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) t1 t2
    && compare_under e1 def1 e2 def2
    && compare_under e1 ty1 e2 ty2
  | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false


let rec fast_test lft1 term1 lft2 term2 = match fterm_of term1, fterm_of term2 with
  | FLIFT (i, term1), (FLIFT _ | FCLOS _) -> fast_test (el_shft i lft1) term1 lft2 term2
  | FCLOS _, FLIFT (j, term2) -> fast_test lft1 term1 (el_shft j lft2) term2
  | FCLOS (c1, (e1,u1)), FCLOS (c2, (e2,u2)) ->
    eq_lift lft1 lft2 &&
    compare_under (e1, u1) c1 (e2, u2) c2
  | _ -> false

let assert_reduced_constructor s =
  if not @@ CList.is_empty s then
    CErrors.anomaly Pp.(str "conversion was given unreduced term (FConstruct).")

let rec strip_flift k v = match fterm_of v with
| FLIFT (n, v') -> strip_flift (k + n) v'
| _ -> (k, v)

(* Optional cap on cached entries per session (ROCQ_CONV_CACHE_MAX; 0 means
   unlimited). Unbounded by default: like [clos_tab], the table is
   session-scoped, so its lifetime bounds memory. *)
let cc_max_size =
  match int_of_string (Sys.getenv "ROCQ_CONV_CACHE_MAX") with
  | 0 -> max_int
  | n -> n
  | exception _ -> max_int

(* The cache is enabled by default; set ROCQ_CONV_CACHE=0 to disable. *)
let cc_enabled =
  match Sys.getenv "ROCQ_CONV_CACHE" with
  | "0" -> false
  | _ -> true
  | exception Not_found -> true

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv ~cache:docache cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
  let fast = fast_test lft1 term1 lft2 term2 in
  if fast then cuniv
  else
    (* NOTE: entry-wise first-order comparison of same-body FCLOS pairs was
       tried here and regressed badly (failing entries ground then thrown
       away by the fallback); do not re-add without a failure cache. *)
    match infos.cnv_cache with
    | None ->
      eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv
    | Some cache ->
      let (k1, v1) = strip_flift 0 term1 in
      let (k2, v2) = strip_flift 0 term2 in
      (* The two levels are keyed differently, so they must be gated
         separately. Level 1 is keyed on cell identity: a cell nobody else
         references gets a brand new id, so the probe can never hit and the
         insert is pure bookkeeping -- skip it, and leave the cell uninterned.
         Level 2 is keyed on (node, subst) and needs no id for [v1]/[v2]
         themselves (only for the substitution entries, which are shared by
         construction), so it applies to freshly built closures too -- exactly
         the population level 1 has to give up on. *)
      let usefid =
        docache || not (CClosure.has_default_fid v1 || CClosure.has_default_fid v2)
      in
      let useclos = match cache.cc_clos with
        | None -> false
        | Some _ ->
          match fterm_of v1, fterm_of v2 with
          | FCLOS _, FCLOS _ -> true
          | _ -> false
      in
      if not usefid && not useclos then
        (* neither level can hit: run uncached and assign no ids *)
        eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv
      else
      let lid1 = cc_intern cache (el_shft k1 lft1) in
      let lid2 = if lid1 < 0 then -1 else cc_intern cache (el_shft k2 lft2) in
      if lid2 < 0 then
        (* out of lift interning range: run uncached *)
        eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv
      else begin
        let fid1 = if usefid then CClosure.get_fid v1 else 0 in
        let fid2 = if usefid then CClosure.get_fid v2 else 0 in
        (* out of packing range: fall back to level 2 alone *)
        let usefid = usefid && fid1 < 1 lsl 31 && fid2 < 1 lsl 31 in
        let pk = (fid1 lsl 31) lor fid2 in
        let pb = match cv_pb with CONV -> 0 | CUMUL -> 1 in
        let meta0 = (lid1 lsl 18) lor (lid2 lsl 3) lor (pb lsl 1) in
        match (if usefid then cc_find cache pk meta0 else -1) with
        | 1 -> cuniv
        | 0 -> raise NotConvertible
        | _ ->
          let add r =
            if usefid then begin
              let maxid = if fid1 > fid2 then fid1 else fid2 in
              let () = if maxid > cache.max_uid then cache.max_uid <- maxid in
              if cache.cc_cnt < cc_max_size then begin
                if 2 * (cache.cc_cnt + 1) > Array.length cache.cc_key then
                  cc_resize cache;
                cache.cc_cnt <- cache.cc_cnt + 1;
                cc_insert_raw cache.cc_key cache.cc_meta pk (meta0 lor r)
              end
            end
          in
          (* (node, subst) closure-pair probe: only reached when the cell-id
             lookup was absent or skipped, so any hit here is coverage the
             cell-id cache cannot express. The key is captured before
             [eqappr] runs, since reduction updates cells in place. *)
          let ckey = match cache.cc_clos with
            | None -> None
            | Some cp ->
              match fterm_of v1, fterm_of v2 with
              | FCLOS (c1, (s1, u1)), FCLOS (c2, (s2, u2)) ->
                (* Hashing the whole substitution at each binder becomes
                   quadratic in the context depth. Bound the combined size
                   before constructing a key; [size] uses cached subtree
                   sizes and leaves compact identity substitutions intact. *)
                let size1 = Esubst.Internal.size s1 in
                if size1 > 256 || Esubst.Internal.size s2 > 256 - size1 then None
                else Some (cp,
                      { ck_hash = clos_pair_hash c1 s1 c2 s2 lid1 lid2 pb;
                        ck_c1 = c1; ck_s1 = s1; ck_u1 = u1;
                        ck_c2 = c2; ck_s2 = s2; ck_u2 = u2;
                        ck_lid1 = lid1; ck_lid2 = lid2; ck_pb = pb })
              | _ -> None
          in
          let cached = match ckey with
            | None -> -1
            | Some (cp, k) ->
              incr clos_memo_probes;
              (* body-pair upper-bound bookkeeping: diagnostics only *)
              if clos_memo_mode = 1 then begin
                if BodyPairTbl.mem cp.cp_bodies (k.ck_c1, k.ck_c2)
                then incr clos_memo_body_hits
                else BodyPairTbl.add cp.cp_bodies (k.ck_c1, k.ck_c2) ()
              end;
              match ClosPairTbl.find_opt cp.cp_full k with
              | Some r -> incr clos_memo_full_hits; r
              | None -> -1
          in
          if cached >= 0 && clos_memo_mode = 2 then begin
            add cached;
            if cached = 1 then cuniv else raise NotConvertible
          end else begin
            let addc r = match ckey with
              | Some (cp, k) when cached < 0 ->
                if ClosPairTbl.add cp.cp_full k r then incr clos_memo_inserts
              | _ -> ()
            in
            (* NOTE: a post-whd second cache probe on the reduced bare states
               was tried here and measured useless (2 hits in 13.2M probes). *)
            match eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv with
            | cuniv -> add 1; addc 1; cuniv
            | exception NotConvertible -> add 0; addc 0; raise NotConvertible
          end
      end

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb l2r infos (lft1,st1) (lft2,st2) cuniv =
  Control.check_for_interrupt ();
  (* First head reduce both terms *)
  let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
  let appr1 = whd_stack ninfos infos.lft_tab (fst st1) (snd st1) in
  let appr2 = whd_stack ninfos infos.rgt_tab (fst st2) (snd st2) in
  eqwhnf cv_pb l2r infos (lft1, appr1) (lft2, appr2) cuniv

(* assumes that appr1 and appr2 are in whnf *)
and eqwhnf cv_pb l2r infos (lft1, (hd1, v1) as appr1) (lft2, (hd2, v2) as appr2) cuniv =
  (** We delay the computation of the lifts that apply to the head of the term
      with [el_stack] inside the branches where they are actually used. *)
  (** Irrelevant terms are guaranteed to be [FIrrelevant], except for [FFlex],
      [FRel] and [FLambda]. Those ones are handled specifically below. *)
  match (fterm_of hd1, fterm_of hd2) with
    (* case of leaves *)
    | (FAtom a1, FAtom a2) ->
        (match kind a1, kind a2 with
           | (Sort s1, Sort s2) ->
               if not (is_empty_stack v1 && is_empty_stack v2) then
                 (* May happen because we convert application right to left *)
                 raise NotConvertible;
              fail_check infos @@ sort_cmp_universes cv_pb s1 s2 cuniv
           | (Meta n, Meta m) ->
               if Int.equal n m
               then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
               else raise NotConvertible
           | _ -> raise NotConvertible)
    | (FEvar (ev1, args1, env1, _), FEvar (ev2, args2, env2, _)) ->
        if Evar.equal ev1 ev2 then
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_stacks l2r infos lft1 lft2 v1 v2 cuniv in
          convert_list ~cache:false l2r infos el1 el2
            (List.map (mk_clos env1) args1)
            (List.map (mk_clos env2) args2) cuniv
        else raise NotConvertible

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) ->
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let n = reloc_rel n el1 in
        let m = reloc_rel m el2 in
        let rn = Range.get (info_relevances infos.cnv_inf) (n - 1) in
        let rm = Range.get (info_relevances infos.cnv_inf) (m - 1) in
        if is_irrelevant infos.cnv_inf rn && is_irrelevant infos.cnv_inf rm then
          let v1 = CClosure.skip_irrelevant_stack infos.cnv_inf v1 in
          let v2 = CClosure.skip_irrelevant_stack infos.cnv_inf v2 in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else if Int.equal n m then
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          raise NotConvertible

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
      (try
         let nargs = same_args_size v1 v2 in
         let cuniv = conv_table_key infos ~nargs fl1 fl2 cuniv in
         let () = if irr_flex infos.cnv_inf fl1 then raise NotConvertible (* trigger the fallback *) in
         let mask = if infos.cnv_typ then match fl1 with
         | ConstKey _ -> get_ref_mask infos.cnv_inf infos.lft_tab fl1
         | RelKey _ | VarKey _ -> [||]
         else [||]
         in
         convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv
       with NotConvertible | NotConvertibleTrace _ ->
        let r1 = unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 in
        let r2 = unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 in
        match r1, r2 with
        | None, None -> raise NotConvertible
        | Some (t1, v1), Some (t2, v2) ->
          (* else the oracle tells which constant is to be expanded *)
          let oracle = CClosure.oracle_of_infos infos.cnv_inf in
          let to_er fl =
            match fl with
            | ConstKey (c, _) -> Some (Conv_oracle.EvalConstRef c)
            | VarKey id -> Some (Conv_oracle.EvalVarRef id)
            | RelKey _ -> None
          in
          let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
          let () = Control.check_for_interrupt () in
          (* Determine which constant to unfold first *)
          let unfold_left =
            let order = Conv_oracle.oracle_compare oracle (to_er fl1) (to_er fl2) in
            match order with
            | Conv_oracle.Left -> true
            | Conv_oracle.Right -> false
            | Conv_oracle.Same ->
              (* When oracle doesn't prefer either, optionally use dependency heuristic *)
              let env = CClosure.info_env infos.cnv_inf in
              if (Environ.typing_flags env).unfold_dep_heuristic then
                match fl1, fl2 with
                | ConstKey (cst1, _), ConstKey (cst2, _) ->
                  if Environ.constant_depends_on env cst1 cst2 then true
                  else if Environ.constant_depends_on env cst2 cst1 then false
                  else l2r
                | _ -> l2r
              else l2r
          in
          if unfold_left then
            let appr1 = whd_stack ninfos infos.lft_tab t1 v1 in
            eqwhnf cv_pb l2r infos (lft1, appr1) appr2 cuniv
          else
            let appr2 = whd_stack ninfos infos.rgt_tab t2 v2 in
            eqwhnf cv_pb l2r infos appr1 (lft2, appr2) cuniv
        | Some (t1, v1), None ->
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let t1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab t1 v1 in
          eqwhnf cv_pb l2r infos (lft1, t1) appr2 cuniv
        | None, Some (t2, v2) ->
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let t2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab t2 v2 in
          eqwhnf cv_pb l2r infos appr1 (lft2, t2) cuniv
        )

    | (FProj (p1,r1,c1), FProj (p2, r2, c2)) ->
      (* Projections: prefer unfolding to first-order unification,
         which will happen naturally if the terms c1, c2 are not in constructor
         form *)
      (match unfold_projection infos.cnv_inf p1 r1 with
      | Some s1 ->
        eqappr cv_pb l2r infos (lft1, (c1, (s1 :: v1))) appr2 cuniv
      | None ->
        match unfold_projection infos.cnv_inf p2 r2 with
        | Some s2 ->
          eqappr cv_pb l2r infos appr1 (lft2, (c2, (s2 :: v2))) cuniv
        | None ->
          if Projection.Repr.CanOrd.equal (Projection.repr p1) (Projection.repr p2)
             && compare_stack_shape v1 v2 then
            let el1 = el_stack lft1 v1 in
            let el2 = el_stack lft2 v2 in
            let u1 = ccnv ~cache:true CONV l2r infos el1 el2 c1 c2 cuniv in
              convert_stacks l2r infos lft1 lft2 v1 v2 u1
          else (* Two projections in WHNF: unfold *)
            raise NotConvertible)

    | (FProj (p1,r1,c1), t2) ->
      begin match unfold_projection infos.cnv_inf p1 r1 with
       | Some s1 ->
         eqappr cv_pb l2r infos (lft1, (c1, (s1 :: v1))) appr2 cuniv
       | None ->
         begin match t2 with
          | FFlex fl2 ->
            begin match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 with
             | Some t2 ->
               eqappr cv_pb l2r infos appr1 (lft2, t2) cuniv
             | None -> raise NotConvertible
            end
          | _ -> raise NotConvertible
         end
      end

    | (t1, FProj (p2,r2,c2)) ->
      begin match unfold_projection infos.cnv_inf p2 r2 with
       | Some s2 ->
         eqappr cv_pb l2r infos appr1 (lft2, (c2, (s2 :: v2))) cuniv
       | None ->
         begin match t1 with
          | FFlex fl1 ->
            begin match unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 with
             | Some t1 ->
               eqappr cv_pb l2r infos (lft1, t1) appr2 cuniv
             | None -> raise NotConvertible
            end
          | _ -> raise NotConvertible
         end
      end

    (* other constructors *)
    | (FLambda _, FLambda _) ->
        (* Inconsistency: we tolerate that v1, v2 contain shift and update but
           we throw them away *)
        if not (is_empty_stack v1 && is_empty_stack v2) then
          anomaly (Pp.str "conversion was given ill-typed terms (FLambda).");
        let (x1,ty1,bd1) = destFLambda mk_clos hd1 in
        let (_,ty2,bd2) = destFLambda mk_clos hd2 in
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv ~cache:false CONV l2r infos el1 el2 ty1 ty2 cuniv in (* FIXME ty1 / ty2 fresh *)
        ccnv ~cache:false CONV l2r (push_relevance infos x1) (el_lift el1) (el_lift el2) bd1 bd2 cuniv

    | (FProd (x1, c1, c2, e), FProd (_, c'1, c'2, e')) ->
        if not (is_empty_stack v1 && is_empty_stack v2) then
          (* May happen because we convert application right to left *)
          raise NotConvertible;
        (* Luo's system *)
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv ~cache:true CONV l2r infos el1 el2 c1 c'1 cuniv in
        let x1 = usubst_binder e x1 in
        ccnv ~cache:false cv_pb l2r (push_relevance infos x1) (el_lift el1) (el_lift el2) (mk_clos (usubs_lift e) c2) (mk_clos (usubs_lift e') c'2) cuniv

    (* Eta-expansion on the fly *)
    | (FLambda _, _) ->
        let () = match v1 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x1,_ty1,bd1) = destFLambda mk_clos hd1 in
        let infos = push_relevance infos x1 in
        eqappr CONV l2r infos
          (el_lift lft1, (bd1, [])) (el_lift lft2, (hd2, eta_expand_stack infos.cnv_inf x1 v2)) cuniv
    | (_, FLambda _) ->
        let () = match v2 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x2,_ty2,bd2) = destFLambda mk_clos hd2 in
        let infos = push_relevance infos x2 in
        eqappr CONV l2r infos
          (el_lift lft1, (hd1, eta_expand_stack infos.cnv_inf x2 v1)) (el_lift lft2, (bd2, [])) cuniv

    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, c2)      ->
      begin match unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 with
        | Some (def1,v1) ->
          (** By virtue of the previous case analyses, we know [c2] is rigid.
              Conversion check to rigid terms eventually implies full weak-head
              reduction, so instead of repeatedly performing small-step
              unfoldings, we perform reduction with all flags on. *)
            let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
            let r1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab def1 v1 in
            eqwhnf cv_pb l2r infos (lft1, r1) appr2 cuniv
        | None ->
          (match c2 with
           | FConstruct (((ind2, 1), u2), args2) ->
             let () = assert_reduced_constructor v2 in
             (try
                let v2, v1 =
                  eta_expand_ind_stack (info_env infos.cnv_inf) (ind2,u2) args2 (snd appr1)
                in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
              with Not_found -> raise NotConvertible)
           | _ -> raise NotConvertible)
      end

    | (c1, FFlex fl2)      ->
       begin match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 with
        | Some (def2, v2) ->
          (** Symmetrical case of above. *)
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let r2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab def2 v2 in
          eqwhnf cv_pb l2r infos appr1 (lft2, r2) cuniv
        | None ->
          match c1 with
          | FConstruct (((ind1, 1), u1), args1) ->
            let () = assert_reduced_constructor v1 in
            (try let v1, v2 =
                   eta_expand_ind_stack (info_env infos.cnv_inf) (ind1,u1) args1 (snd appr2)
               in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
             with Not_found -> raise NotConvertible)
          | _ -> raise NotConvertible
       end

    (* Inductive types:  MutInd MutConstruct Fix Cofix *)
    | (FInd (ind1,u1 as pind1), FInd (ind2,u2 as pind2)) ->
      if Ind.CanOrd.equal ind1 ind2 then
        if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
          let cuniv = fail_check infos @@ convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
          let nargs = same_args_size v1 v2 in
          match fail_check infos @@ convert_inductives cv_pb (mind, snd ind1) nargs u1 u2 cuniv with
          | cuniv -> convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
          | exception MustExpand ->
            let env = info_env infos.cnv_inf in
            let hd1 = eta_expand_ind env pind1 in
            let hd2 = eta_expand_ind env pind2 in
            eqappr cv_pb l2r infos (lft1,(hd1,v1)) (lft2,(hd2,v2)) cuniv
      else raise NotConvertible

    | (FConstruct (((ind1,j1),u1 as pctor1,args1)), FConstruct (((ind2,j2),u2 as pctor2),args2)) ->
      let () = assert_reduced_constructor v1 in
      let () = assert_reduced_constructor v2 in
      let nargs = Array.length args1 in
      let () = if not @@ Int.equal nargs (Array.length args2) then raise NotConvertible in
      let v1 = append_stack args1 v1 in
      let v2 = append_stack args2 v2 in
      if Int.equal j1 j2 && Ind.CanOrd.equal ind1 ind2 then
        if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
          let cuniv = fail_check infos @@ convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
          match fail_check infos @@ convert_constructors (mind, snd ind1, j1) nargs u1 u2 cuniv with
          | cuniv -> convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
          | exception MustExpand ->
            let env = info_env infos.cnv_inf in
            let hd1 = eta_expand_constructor env pctor1 in
            let hd2 = eta_expand_constructor env pctor2 in
            eqappr cv_pb l2r infos (lft1,(hd1,v1)) (lft2,(hd2,v2)) cuniv
      else raise NotConvertible

    (* Eta expansion of records *)
    | (FConstruct (((ind1, j1), u1), args1), _) ->
      let () = assert_reduced_constructor v1 in
      (* records only have 1 constructor *)
      let () = if not @@ Int.equal j1 1 then raise NotConvertible in
      (try
         let v1, v2 =
            eta_expand_ind_stack (info_env infos.cnv_inf) (ind1,u1) args1 (snd appr2)
         in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (_, FConstruct (((ind2, j2), u2), args2)) ->
      let () = assert_reduced_constructor v2 in
      (* records only have 1 constructor *)
      let () = if not @@ Int.equal j2 1 then raise NotConvertible in
      (try
         let v2, v1 =
            eta_expand_ind_stack (info_env infos.cnv_inf) (ind2,u2) args2 (snd appr1)
         in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (FFix (((op1, i1),(na1,tys1,cl1)),e1), FFix(((op2, i2),(_,tys2,cl2)),e2)) ->
        if Int.equal i1 i2 && Array.equal Int.equal op1 op2
        then
          let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (usubs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (usubs_liftn n e2)) cl2 in
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_vect ~cache:false l2r infos el1 el2 fty1 fty2 cuniv in (*FIXME*)
          let cuniv =
            let na1 = Array.map (usubst_binder e1) na1 in
            let infos = push_relevances infos na1 in
            convert_vect ~cache:false l2r infos
                         (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 cuniv (*FIXME*)
          in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | (FCoFix ((op1,(na1,tys1,cl1)),e1), FCoFix((op2,(_,tys2,cl2)),e2)) ->
        if Int.equal op1 op2
        then
          let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (usubs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (usubs_liftn n e2)) cl2 in
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_vect ~cache:false l2r infos el1 el2 fty1 fty2 cuniv in (*FIXME*)
          let cuniv =
            let na1 = Array.map (usubst_binder e1) na1 in
            let infos = push_relevances infos na1 in
            convert_vect ~cache:false l2r infos
                         (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 cuniv (*FIXME*)
          in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | FInt i1, FInt i2 ->
       if Uint63.equal i1 i2 then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       else raise NotConvertible

    | FFloat f1, FFloat f2 ->
        if Float64.equal f1 f2 then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | FString s1, FString s2 ->
        if Pstring.equal s1 s2 then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | FCaseInvert (ci1,u1,pms1,p1,iv1,_,br1,e1), FCaseInvert (ci2,u2,pms2,p2,iv2,_,br2,e2) ->
      (if not (Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind) then raise NotConvertible);
      let el1 = el_stack lft1 v1 and el2 = el_stack lft2 v2 in
      let fold c1 c2 cuniv = ccnv ~cache:true CONV l2r infos el1 el2 c1 c2 cuniv in
      (** FIXME: cache the presence of let-bindings in the case_info *)
      let mind = Environ.lookup_mind (fst ci1.ci_ind) (info_env infos.cnv_inf) in
      let mip = mind.Declarations.mind_packets.(snd ci1.ci_ind) in
      let u1 = CClosure.usubst_instance e1 u1 in
      let u2 = CClosure.usubst_instance e2 u2 in
      let cuniv =
        let ind = (mind,snd ci1.ci_ind) in
        let nargs = inductive_cumulativity_arguments ind in
        fail_check infos @@ convert_inductives CONV ind nargs u1 u2 cuniv
      in
      let pms1 = mk_clos_vect e1 pms1 in
      let pms2 = mk_clos_vect e2 pms2 in
      let cuniv = Array.fold_right2 fold pms1 pms2 cuniv in
      let cuniv = Array.fold_right2 fold (get_invert iv1) (get_invert iv2) cuniv in
      let cuniv = convert_return_clause ~cache:true mind mip l2r infos e1 e2 el1 el2 u1 u2 pms1 pms2 p1 p2 cuniv in (* FIXME *)
      (* not clear if we need to pass both u1 and u2 as
         convert_inductives should have enforced that they are
         equivalent when used to instantiate this inductive's
         components, but we may as well *)
      let cuniv = convert_branches ~cache:true mind mip l2r infos e1 e2 el1 el2 u1 u2 pms1 pms2 br1 br2 cuniv in
      convert_stacks l2r infos lft1 lft2 v1 v2 cuniv

    | FArray (u1,t1,ty1), FArray (u2,t2,ty2) ->
      let len = Parray.length_int t1 in
      if not (Int.equal len (Parray.length_int t2)) then raise NotConvertible;
      let cuniv = fail_check infos @@ convert_instances_cumul CONV [|UVars.Variance.Irrelevant|] u1 u2 cuniv in
      let el1 = el_stack lft1 v1 in
      let el2 = el_stack lft2 v2 in
      let cuniv = ccnv ~cache:true CONV l2r infos el1 el2 ty1 ty2 cuniv in
      let cuniv = Parray.fold_left2 (fun u v1 v2 -> ccnv ~cache:true CONV l2r infos el1 el2 v1 v2 u) cuniv t1 t2 in
      convert_stacks l2r infos lft1 lft2 v1 v2 cuniv

    | (FRel n1, FIrrelevant) ->
      let n1 = reloc_rel n1 (el_stack lft1 v1) in
      let r1 = Range.get (info_relevances infos.cnv_inf) (n1 - 1) in
      if is_irrelevant infos.cnv_inf r1 then
        let v1 = CClosure.skip_irrelevant_stack infos.cnv_inf v1 in
        convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible

    | (FIrrelevant, FRel n2) ->
      let n2 = reloc_rel n2 (el_stack lft2 v2) in
      let r2 = Range.get (info_relevances infos.cnv_inf) (n2 - 1) in
      if is_irrelevant infos.cnv_inf r2 then
        let v2 = CClosure.skip_irrelevant_stack infos.cnv_inf v2 in
        convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible

    | FIrrelevant, FIrrelevant ->
      convert_stacks l2r infos lft1 lft2 v1 v2 cuniv

     (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
     | ( (FLetIn _, _) | (FCaseT _,_) | (FApp _,_) | (FCLOS _,_) | (FLIFT _,_)
       | (_, FLetIn _) | (_,FCaseT _) | (_,FApp _) | (_,FCLOS _) | (_,FLIFT _)
       | (FLOCKED,_) | (_,FLOCKED) ) -> assert false

     | (FRel _ | FAtom _ | FInd _ | FFix _ | FCoFix _ | FCaseInvert _
       | FProd _ | FEvar _ | FInt _ | FFloat _ | FString _
       | FArray _ | FIrrelevant), _ -> raise NotConvertible

and convert_stacks ?(mask = [||]) l2r infos lft1 lft2 stk1 stk2 cuniv =
  let f (l1, t1) (l2, t2) cuniv = ccnv ~cache:true CONV l2r infos l1 l2 t1 t2 cuniv in
  let rec cmp_rec nargs pstk1 pstk2 cuniv =
    match (pstk1,pstk2) with
      | (z1::s1, z2::s2) ->
          (* Stacks are known to have the same argument size *)
          let rnargs = match z1 with
          | Zlapp a -> if nargs < 0 then -1 else nargs + Array.length a
          | Zlproj _ | Zlfix _ | Zlcase _ | Zlprimitive _ -> -1
          in
          let cu1 = cmp_rec rnargs s1 s2 cuniv in
          (match (z1,z2) with
            | (Zlapp a1,Zlapp a2) ->
              if nargs < 0 then
               Array.fold_right2 f a1 a2 cu1
              else
                let rec fold i cu =
                  if i < 0 then cu
                  else if nargs + i < Array.length mask && not mask.(nargs + i) then
                    fold (i - 1) cu (* skip runtime irrelevant argument *)
                  else
                    let cu = f a1.(i) a2.(i) cu in
                    fold (i - 1) cu
                in
                fold (Array.length a1 - 1) cu1
            | (Zlproj (c1,_l1),Zlproj (c2,_l2)) ->
              if not (Projection.Repr.CanOrd.equal c1 c2) then
                raise NotConvertible
              else cu1
            | (Zlfix(fx1,a1),Zlfix(fx2,a2)) ->
                let cu2 = f fx1 fx2 cu1 in
                cmp_rec (-1) a1 a2 cu2
            | (Zlcase(ci1,l1,u1,pms1,p1,br1,e1),Zlcase(ci2,l2,u2,pms2,p2,br2,e2)) ->
                if not (Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind) then
                  raise NotConvertible;
                let cu = cu1 in
                (** FIXME: cache the presence of let-bindings in the case_info *)
                let mind = Environ.lookup_mind (fst ci1.ci_ind) (info_env infos.cnv_inf) in
                let mip = mind.Declarations.mind_packets.(snd ci1.ci_ind) in
                let u1 = CClosure.usubst_instance e1 u1 in
                let u2 = CClosure.usubst_instance e2 u2 in
                let cu =
                  if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
                    convert_instances ~flex:false u1 u2 cu
                  else
                    match mind.Declarations.mind_variance with
                    | None -> convert_instances ~flex:false u1 u2 cu
                    | Some variances -> convert_instances_cumul CONV variances u1 u2 cu
                in
                let cu = fail_check infos cu in
                (* FIXME: do not cache when parameters not needed *)
                let pms1 = mk_clos_vect e1 pms1 in
                let pms2 = mk_clos_vect e2 pms2 in
                let fold_params c1 c2 accu = ccnv ~cache:false CONV l2r infos l1 l2 c1 c2 accu in
                let cu = Array.fold_right2 fold_params pms1 pms2 cu in
                let cu = convert_return_clause ~cache:false mind mip l2r infos e1 e2 l1 l2 u1 u2 pms1 pms2 p1 p2 cu in
                convert_branches ~cache:false mind mip l2r infos e1 e2 l1 l2 u1 u2 pms1 pms2 br1 br2 cu (* FIXME *)
            | (Zlprimitive(op1,_,rargs1,kargs1),Zlprimitive(op2,_,rargs2,kargs2)) ->
              if not (CPrimitives.equal op1 op2) then raise NotConvertible else
                let cu2 = List.fold_right2 f rargs1 rargs2 cu1 in
                let fk (_,a1) (_,a2) cu = f a1 a2 cu in
                List.fold_right2 fk kargs1 kargs2 cu2
            | ((Zlapp _ | Zlproj _ | Zlfix _| Zlcase _| Zlprimitive _), _) -> assert false)
      | _ -> cuniv in
  if compare_stack_shape stk1 stk2 then
    let nargs = if Array.is_empty mask then -1 else 0 in
    cmp_rec nargs (pure_stack lft1 stk1) (pure_stack lft2 stk2) cuniv
  else raise NotConvertible

and convert_vect ~cache l2r infos lft1 lft2 v1 v2 cuniv =
  let lv1 = Array.length v1 in
  let lv2 = Array.length v2 in
  if Int.equal lv1 lv2
  then
    let rec fold n cuniv =
      if n >= lv1 then cuniv
      else
        let cuniv = ccnv ~cache CONV l2r infos lft1 lft2 v1.(n) v2.(n) cuniv in
        fold (n+1) cuniv in
    fold 0 cuniv
  else raise NotConvertible

and convert_under_context ~cache l2r infos e1 e2 lft1 lft2 ctx (nas1, c1) (nas2, c2) cu =
  let n = Array.length nas1 in
  let () = assert (Int.equal n (Array.length nas2)) in
  let n, e1, e2 = match ctx with
  | None -> (* nolet *)
    let e1 = usubs_liftn n e1 in
    let e2 = usubs_liftn n e2 in
    (n, e1, e2)
  | Some (ctx, args1, args2) ->
    let n1, e1 = esubst_of_context ctx args1 e1 in
    let n2, e2 = esubst_of_context ctx args2 e2 in
    let () = assert (Int.equal n1 n2) in
    n1, e1, e2
  in
  let lft1 = el_liftn n lft1 in
  let lft2 = el_liftn n lft2 in
  let infos = push_relevances infos (Array.map (usubst_binder e1) nas1) in
  ccnv ~cache CONV l2r infos lft1 lft2 (mk_clos e1 c1) (mk_clos e2 c2) cu

and convert_return_clause ~cache mib mip l2r infos e1 e2 l1 l2 u1 u2 pms1 pms2 p1 p2 cu =
  let ctx =
    if Int.equal mip.mind_nrealargs mip.mind_nrealdecls then None
    else
      let ctx, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
      let pms1 = inductive_subst mib u1 pms1 in
      let pms2 = inductive_subst mib u2 pms2 in
      let open Context.Rel.Declaration in
      (* Add the inductive binder *)
      let ctx = None :: List.map get_value ctx in
      Some (ctx, pms1, pms2)
  in
  convert_under_context ~cache l2r infos e1 e2 l1 l2 ctx (fst p1) (fst p2) cu

and convert_branches ~cache mib mip l2r infos e1 e2 lft1 lft2 u1 u2 pms1 pms2 br1 br2 cuniv =
  let fold i (ctx, _) cuniv =
    let ctx =
      if Int.equal mip.mind_consnrealdecls.(i) mip.mind_consnrealargs.(i) then None
      else
        let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
        let ctx = List.map Context.Rel.Declaration.get_value ctx in
        let pms1 = inductive_subst mib u1 pms1 in
        let pms2 = inductive_subst mib u2 pms2 in
        Some (ctx, pms1, pms2)
    in
    let c1 = br1.(i) in
    let c2 = br2.(i) in
    convert_under_context ~cache l2r infos e1 e2 lft1 lft2 ctx c1 c2 cuniv
  in
  Array.fold_right_i fold mip.mind_nf_lc cuniv

and convert_list ~cache l2r infos lft1 lft2 v1 v2 cuniv = match v1, v2 with
| [], [] -> cuniv
| c1 :: v1, c2 :: v2 ->
  let cuniv = ccnv ~cache CONV l2r infos lft1 lft2 c1 c2 cuniv in
  convert_list ~cache l2r infos lft1 lft2 v1 v2 cuniv
| _, _ -> raise NotConvertible

let clos_gen_conv (type err) ~typed ~use_cache trans cv_pb l2r evars env graph univs t1 t2 =
  NewProfile.profile "Conversion" begin fun () ->
      let reds = RedFlags.red_add_transparent RedFlags.betaiotazeta trans in
      let infos = create_conv_infos ~univs:graph ~evars reds env in
      let module Error = struct type payload += Error of err end in
      let box e = Error.Error e in
      let cache =
        if use_cache && cc_enabled then
          Some { cc_key = Array.make 256 0; cc_meta = Array.make 256 0;
                 cc_cnt = 0; cc_lifts = LiftTbl.create 16; cc_nlifts = 1;
                 max_uid = 0;
                 cc_clos =
                   if clos_memo_mode > 0 then
                     Some { cp_full = ClosPairTbl.create 256;
                            cp_bodies =
                              BodyPairTbl.create
                                (if clos_memo_mode = 1 then 256 else 1) }
                   else None }
        else None
      in
      let infos = {
        cnv_inf = infos;
        cnv_typ = typed;
        lft_tab = create_tab ();
        rgt_tab = create_tab ();
        err_ret = box;
        cnv_cache = cache;
      } in
      try Result.Ok (ccnv ~cache:false cv_pb l2r infos el_id el_id (inject t1) (inject t2) univs)
      with
      | NotConvertible -> Result.Error None
      | NotConvertibleTrace (Error.Error e) -> Result.Error (Some e)
      | NotConvertibleTrace _ -> assert false
  end ()

let check_eq qeq state u u' =
  if UGraph.check_eq_sort qeq state u u'
  then Result.Ok state
  else Result.Error None

let check_leq qeq state u u' =
  if UGraph.check_leq_sort qeq state u u'
  then Result.Ok state
  else Result.Error None

let checked_sort_cmp_universes qeq = (); fun pb s0 s1 state ->
  match pb with
  | CUMUL -> check_leq qeq state s0 s1
  | CONV -> check_eq qeq state s0 s1

let check_convert_instances qeq = (); fun ~flex:_ u u' state ->
  if UGraph.check_eq_instances qeq state u u' then Result.Ok state
  else Result.Error None

(* general conversion and inference functions *)
let check_inductive_instances qeq = (); fun cv_pb variance u1 u2 state ->
  let qcsts, ucsts = get_cumulativity_constraints cv_pb variance u1 u2 in
  let check_quality (q1, q2) = qeq q1 q2 in
  if UVars.QPairSet.for_all check_quality qcsts && UGraph.check_constraints ucsts state
  then Result.Ok state
  else Result.Error None

let checked_universes_gen irr qeq =
  { compare_sorts = checked_sort_cmp_universes qeq;
    compare_instances = check_convert_instances qeq;
    compare_cumul_instances = check_inductive_instances qeq;
    compare_irrelevant = irr }

let checked_universes = checked_universes_gen true Sorts.Quality.equal

let () =
  let conv infos tab a b =
    try
      let box = Empty.abort in
      let state = info_univs infos in
      let qual_equal q1 q2 = CClosure.eq_quality infos q1 q2 in
      let infos = { cnv_inf = infos; cnv_typ = true; lft_tab = tab; rgt_tab = tab; err_ret = box; cnv_cache = None; } in
      let state', _ = ccnv ~cache:true CONV false infos el_id el_id a b (state, checked_universes_gen false qual_equal) in
      assert (state==state');
      true
    with
    | NotConvertible -> false
    | NotConvertibleTrace _ -> assert false
  in
  CClosure.set_conv conv

let gen_conv ~typed cv_pb ?(l2r=false) ?(reds=TransparentState.full) env ?(evars=default_evar_handler env) t1 t2 =
  let univs = Environ.universes env in
  let state = univs in
  let b =
    if cv_pb = CUMUL then leq_constr_univs univs t1 t2
    else eq_constr_univs univs t1 t2
  in
    if b then Result.Ok ()
    else match clos_gen_conv ~typed ~use_cache:true reds cv_pb l2r evars env univs (state, checked_universes) t1 t2 with
    | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare)-> Result.Ok ()
    | Result.Error None -> Result.Error ()
    | Result.Error (Some e) -> Empty.abort e

let conv = gen_conv ~typed:false CONV
let conv_leq = gen_conv ~typed:false CUMUL

let generic_conv cv_pb ~l2r reds env ?(evars=default_evar_handler env) state t1 t2 =
  let graph = Environ.universes env in
  let use_cache = (snd state).compare_irrelevant in
  match clos_gen_conv ~typed:false ~use_cache reds cv_pb l2r evars env graph state t1 t2 with
  | Result.Ok (s, _) -> Result.Ok s
  | Result.Error e -> Result.Error e

let default_conv cv_pb env t1 t2 =
    gen_conv ~typed:true cv_pb env t1 t2

let default_conv_leq = default_conv CUMUL

type graph_inconsistency = Univ of UGraph.univ_inconsistency | Qual of QGraph.elimination_error
