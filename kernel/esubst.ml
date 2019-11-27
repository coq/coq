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

(* Variant of skewed lists enriched w.r.t. a monoid. See the Range module.

  In addition to the indexed data, every node contains a monoid element, in our
  case, integers. It corresponds to the number of partial lifts to apply when
  reaching this subtree. The total lift is obtained by summing all the partial
  lifts encountered in the tree traversal. For efficiency, we also cache the
  sum of partial lifts of the whole subtree as the last argument of the [Node]
  constructor. *)

type mon = int
let mul n m = n + m
let one = 0

type 'a or_var = Arg of 'a | Var of int

type 'a tree =
| Leaf of mon * 'a or_var
| Node of mon * 'a or_var * 'a tree * 'a tree * mon

type 'a subs = Nil of mon | Cons of int * 'a tree * 'a subs

let eval = function
| Leaf (w, _) -> w
| Node (w1, _, _, _, w2) -> mul w1 w2

let leaf x = Leaf (one, x)
let node x t1 t2 = Node (one, x, t1, t2, mul (eval t1) (eval t2))

let rec tree_get h w t i = match t with
| Leaf (w', x) ->
  let w = mul w w' in
  if i = 0 then w, Inl x else assert false
| Node (w', x, t1, t2, _) ->
  let w = mul w w' in
  if i = 0 then w, Inl x
  else
    let h = h / 2 in
    if i <= h then tree_get h w t1 (i - 1)
    else tree_get h (mul w (eval t1)) t2 (i - h - 1)

let rec get w l i = match l with
| Nil w' -> mul w w', Inr i
| Cons (h, t, rem) ->
  if i < h then tree_get h w t i else get (mul (eval t) w) rem (i - h)

let get l i = get one l i

let tree_write w = function
| Leaf (w', x) -> Leaf (mul w w', x)
| Node (w', x, t1, t2, wt) -> Node (mul w w', x, t1, t2, wt)

let write w l = match l with
| Nil w' -> Nil (mul w w')
| Cons (h, t, rem) -> Cons (h, tree_write w t, rem)

let empty = Nil one

let cons x l = match l with
| Cons (h1, t1, Cons (h2, t2, rem)) ->
  if Int.equal h1 h2 then Cons (1 + h1 + h2, node x t1 t2, rem)
  else Cons (1, leaf x, l)
| _ -> Cons (1, leaf x, l)

let expand_rel n s =
  let k, v = get s (n - 1) in
  match v with
  | Inl (Arg v) -> Inl (k, v)
  | Inl (Var i) -> Inr (k + i, None)
  | Inr i -> Inr (k + i + 1, Some (i + 1))

let is_subs_id = function
| Nil w -> Int.equal w 0
| Cons (_, _, _) -> false

let subs_cons (v, s) =
  Array.fold_left (fun accu x -> cons (Arg x) accu) s v

let rec push_vars i s =
  if Int.equal i 0 then s
  else push_vars (pred i) (cons (Var i) s)

let subs_liftn n s =
  if Int.equal n 0 then s
  else
    let s = write n s in
    push_vars n s

let subs_lift s =
  cons (Var 1) (write 1 s)

let subs_id n =
  if Int.equal n 0 then empty
  else push_vars n empty

let subs_shft (n, s) = write n s
