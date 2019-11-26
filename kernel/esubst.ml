(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
  | ENIL            (* empty substitution *)
  | CONS of 'a array * 'a subs
                           (* CONS([|t1..tn|],S)  =
                              (S.t1...tn)    parallel substitution
                              beware of the order *)
  | RELS of int * int * 'a subs (* RELS(n, k, S) = S.Rel(n+1) ... Rel(n+k+1) *)
  | SHIFT of int * 'a subs (* SHIFT(n,S) = (^n o S) terms in S are relocated *)
                           (*                        with n vars *)
(* In term of typing rules:

- · ⊢ ENIL : ·
- If Γ, Ξ, Σ ⊢ σ : Δ then Γ, Ξ, Σ ⊢ RELS (n, k, σ) : Δ, Ξ provided |Σ|=n and |Ξ|=k
- If Γ ⊢ σ : Δ and Γ ⊢ u : A then Γ ⊢ CONS (u, σ) : Δ, A
- If Γ ⊢ σ : Δ then Γ, Ξ ⊢ SHIFT (n, σ) : Δ provided |Ξ|=n.
*)

(* operations of subs: collapses constructors when possible.
 * Needn't be recursive if we always use these functions
 *)

let subs_id i = if Int.equal i 0 then ENIL else RELS(0, i, ENIL)

let subs_cons(x,s) = if Int.equal (Array.length x) 0 then s else CONS(x,s)

let rec subs_shft n s = match s with
  | SHIFT (k, s) -> SHIFT (k + n, s)
  | RELS (m, k, s) -> RELS (m + n, k, subs_shft n s)
  | ENIL | CONS _ -> SHIFT (n, s)

let subs_rels n k s = match s with
| RELS (m, p, s') ->
  if Int.equal m (n + k) then RELS (n, p + k, s') else RELS (n, k, s)
| s -> RELS (n, k, s)

let subs_liftn n s =
  if Int.equal n 0 then s else subs_rels 0 n (subs_shft n s)

let subs_lift a = subs_liftn 1 a
let subs_shft (n, s) = subs_shft n s

(* Tests whether a substitution is equal to the identity *)
let rec is_subs_id = function
    ENIL     -> true
  | RELS(0,k,SHIFT(n, s))  -> Int.equal k n && is_subs_id s
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
    | CONS (def, s) ->
      let len = Array.length def in
      if k <= len then Inl (lams, def.(len - k))
      else exp_rel lams (k - len) s
    | RELS (n, len, s) ->
      if k <= len then Inr (lams+n+k, None)
      else exp_rel lams (k - len) s
    | SHIFT (n,s)          -> exp_rel (n+lams) k s
    | ENIL                 -> Inr (lams+k, Some k)

let expand_rel k subs = exp_rel 0 k subs

let rec subs_map f = function
| ENIL -> ENIL
| CONS (x, s) -> CONS (Array.map f x, subs_map f s)
| RELS (n, k, s) -> RELS (n, k, subs_map f s)
| SHIFT (n, s) -> SHIFT (n, subs_map f s)

let rec reloc_range n k accu e = match e with
| ELID -> subs_rels n k accu
| ELSHFT (e, p) -> reloc_range (n + p) k accu e
| ELLFT (p, e') ->
  if n < p then subs_rels n (p - n) (reloc_range p (n + k - p) accu e)
  else reloc_range (n + p) k accu e'

let rec lift_subst mk_cl s1 s2 = match s1 with
| ELID -> subs_map (fun c -> mk_cl ELID c) s2
| ELSHFT(s, k) -> subs_shft(k, lift_subst mk_cl s s2)
| ELLFT (k, s) ->
  match s2 with
  | ENIL -> ENIL
  | CONS(x,s') ->
      CONS(CArray.Fun1.map mk_cl s1 x, lift_subst mk_cl s1 s')
  | SHIFT(k',s') ->
      if k<k'
      then subs_shft(k, lift_subst mk_cl s (subs_shft(k'-k, s')))
      else subs_shft(k', lift_subst mk_cl (el_liftn (k-k') s) s')
  | RELS (m, p, s') ->
    let s' = lift_subst mk_cl s1 s' in
    reloc_range m p s' s1
