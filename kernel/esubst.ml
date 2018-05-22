(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Bruno Barras for Coq V7.0, Mar 2001 *)

(* Support for explicit substitutions *)

open Util

(*********************)
(*      Lifting      *)
(*********************)

(* Explicit lifts and basic operations *)
(* Invariant to preserve in this module: no lift contains two consecutive
    [ELSHFT] nor two consecutive [ELLFT]. *)
type lift =
  | ELID
  | ELSHFT of lift * int (* ELSHFT(l,n) == lift of n, then apply lift l *)
  | ELLFT of int * lift  (* ELLFT(n,l)  == apply l to de Bruijn > n *)
                         (*                 i.e under n binders *)

let el_id = ELID

(* compose a relocation of magnitude n *)
let el_shft_rec n = function
  | ELSHFT(el,k) -> ELSHFT(el,k+n)
  | el           -> ELSHFT(el,n)
let el_shft n el = if Int.equal n 0 then el else el_shft_rec n el

(* cross n binders *)
let el_liftn_rec n = function
  | ELID        -> ELID
  | ELLFT(k,el) -> ELLFT(n+k, el)
  | el          -> ELLFT(n, el)
let el_liftn n el = if Int.equal n 0 then el else el_liftn_rec n el

let el_lift el = el_liftn_rec 1 el

(* relocation of de Bruijn n in an explicit lift *)
let rec reloc_rel n = function
  | ELID -> n
  | ELLFT(k,el) ->
      if n <= k then n else (reloc_rel (n-k) el) + k
  | ELSHFT(el,k) -> (reloc_rel (n+k) el)

let rec is_lift_id = function
  | ELID -> true
  | ELSHFT(e,n) -> Int.equal n 0 && is_lift_id e
  | ELLFT (_,e) -> is_lift_id e

(*********************)
(*  Substitutions    *)
(*********************)

(* (bounded) explicit substitutions of type 'a *)
type 'a subs =
  | ESID of int            (* ESID(n)    = %n END   bounded identity *)
  | CONS of 'a array * 'a subs
                           (* CONS([|t1..tn|],S)  =
                              (S.t1...tn)    parallel substitution
                              beware of the order *)
  | SHIFT of int * 'a subs (* SHIFT(n,S) = (^n o S) terms in S are relocated *)
                           (*                        with n vars *)
  | LIFT of int * 'a subs  (* LIFT(n,S) = (%n S) stands for ((^n o S).n...1) *)

(* operations of subs: collapses constructors when possible.
 * Needn't be recursive if we always use these functions
 *)

let subs_id i = ESID i

let subs_cons(x,s) = if Int.equal (Array.length x) 0 then s else CONS(x,s)

let subs_liftn n = function
  | ESID p        -> ESID (p+n) (* bounded identity lifted extends by p *)
  | LIFT (p,lenv) -> LIFT (p+n, lenv)
  | lenv          -> LIFT (n,lenv)

let subs_lift a = subs_liftn 1 a
let subs_liftn n a = if Int.equal n 0 then a else subs_liftn n a

let subs_shft = function
  | (0, s)            -> s
  | (n, SHIFT (k,s1)) -> SHIFT (k+n, s1)
  | (n, s)            -> SHIFT (n,s)
let subs_shft s = if Int.equal (fst s) 0 then snd s else subs_shft s

let subs_shift_cons = function
  (0, s, t)           -> CONS(t,s)
| (k, SHIFT(n,s1), t) -> CONS(t,SHIFT(k+n, s1))
| (k, s, t)           -> CONS(t,SHIFT(k, s));;

(* Tests whether a substitution is equal to the identity *)
let rec is_subs_id = function
    ESID _     -> true
  | LIFT(_,s)  -> is_subs_id s
  | SHIFT(0,s) -> is_subs_id s
  | CONS(x,s)  -> Int.equal (Array.length x) 0 && is_subs_id s
  | _          -> false

(* Expands de Bruijn k in the explicit substitution subs
 * lams accumulates de shifts to perform when retrieving the i-th value
 * the rules used are the following:
 *
 *    [id]k       --> k
 *    [S.t]1      --> t
 *    [S.t]k      --> [S](k-1)  if k > 1
 *    [^n o S] k  --> [^n]([S]k)
 *    [(%n S)] k  --> k         if k <= n
 *    [(%n S)] k  --> [^n]([S](k-n))
 *
 * the result is (Inr (k+lams,p)) when the variable is just relocated
 * where p is None if the variable points inside subs and Some(k) if the
 * variable points k bindings beyond subs.
 *)
let rec exp_rel lams k subs =
  match subs with
    | CONS (def,_) when k <= Array.length def
                           -> Inl(lams,def.(Array.length def - k))
    | CONS (v,l)           -> exp_rel lams (k - Array.length v) l
    | LIFT (n,_) when k<=n -> Inr(lams+k,None)
    | LIFT (n,l)           -> exp_rel (n+lams) (k-n) l
    | SHIFT (n,s)          -> exp_rel (n+lams) k s
    | ESID n when k<=n     -> Inr(lams+k,None)
    | ESID n               -> Inr(lams+k,Some (k-n))

let expand_rel k subs = exp_rel 0 k subs

let rec subs_map f = function
| ESID _ as s -> s
| CONS (x, s) -> CONS (Array.map f x, subs_map f s)
| SHIFT (n, s) -> SHIFT (n, subs_map f s)
| LIFT (n, s) -> LIFT (n, subs_map f s)

let rec lift_subst mk_cl s1 s2 = match s1 with
| ELID -> subs_map (fun c -> mk_cl ELID c) s2
| ELSHFT(s, k) -> subs_shft(k, lift_subst mk_cl s s2)
| ELLFT (k, s) ->
  match s2 with
  | CONS(x,s') ->
      CONS(CArray.Fun1.map mk_cl s1 x, lift_subst mk_cl s1 s')
  | ESID n -> lift_subst mk_cl s (ESID (n + k))
  | SHIFT(k',s') ->
      if k<k'
      then subs_shft(k, lift_subst mk_cl s (subs_shft(k'-k, s')))
      else subs_shft(k', lift_subst mk_cl (el_liftn (k-k') s) s')
  | LIFT(k',s') ->
      if k<k'
      then subs_liftn k (lift_subst mk_cl s (subs_liftn (k'-k) s'))
      else subs_liftn k' (lift_subst mk_cl (el_liftn (k-k') s) s')

let rec comp mk_cl s1 s2 =
  match (s1, s2) with
    | _, ESID _ -> s1
    | ESID _, _ -> s2
    | SHIFT(k,s), _ -> subs_shft(k, comp mk_cl s s2)
    | _, CONS(x,s') ->
        CONS(Array.Fun1.map (fun s t -> mk_cl(s,t)) s1 x, comp mk_cl s1 s')
    | CONS(x,s), SHIFT(k,s') ->
        let lg = Array.length x in
        if k == lg then comp mk_cl s s'
        else if k > lg then comp mk_cl s (SHIFT(k-lg, s'))
        else comp mk_cl (CONS(Array.sub x 0 (lg-k), s)) s'
    | CONS(x,s), LIFT(k,s') ->
        let lg = Array.length x in
        if k == lg then CONS(x, comp mk_cl s s')
        else if k > lg then CONS(x, comp mk_cl s (LIFT(k-lg, s')))
        else
          CONS(Array.sub x (lg-k) k,
               comp mk_cl (CONS(Array.sub x 0 (lg-k),s)) s')
    | LIFT(k,s), SHIFT(k',s') ->
        if k<k'
        then subs_shft(k, comp mk_cl s (subs_shft(k'-k, s')))
        else subs_shft(k', comp mk_cl (subs_liftn (k-k') s) s')
    | LIFT(k,s), LIFT(k',s') ->
        if k<k'
        then subs_liftn k (comp mk_cl s (subs_liftn (k'-k) s'))
        else subs_liftn k' (comp mk_cl (subs_liftn (k-k') s) s')
