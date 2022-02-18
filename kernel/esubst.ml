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

(* Terminology comes from substitution calculi (see e.g. Hardin et al.).
   That is, what is called a lift in Coq is made of what is called in
   substitution calculi a shift (the shift to add) and of what is
   called a lift (the threshold above which to apply the shift), which
   can be iterated as represented in the type [lift] *)
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
  case, integers. It corresponds to the number of partial shifts to apply when
  reaching this subtree. The total shift is obtained by summing all the partial
  shifts encountered in the tree traversal. For efficiency, we also cache the
  sum of partial shifts of the whole subtree as the last argument of the [Node]
  constructor.

  A more intuitive but inefficient representation of this data structure would
  be a list of terms interspeded with shifts, as in

  type 'a subst = NIL | CONS of 'a or_var * 'a subst | SHIFT of 'a subst

  On this inefficient representation, the typing rules would be:

  · ⊢ NIL : ·
  Γ ⊢ σ : Δ and Γ ⊢ t : A{σ} implies Γ ⊢ CONS (t, σ) : Δ, A
  Γ ⊢ σ : Δ implies Γ, A ⊢ SHIFT σ : Δ

  The efficient representation is isomorphic to this naive variant, except that
  shifts are grouped together, and we use skewed lists instead of lists.

*)

type shf = int
let cmp n m = n + m
let idn = 0

type 'a or_var = Arg of 'a | Var of int

type 'a tree =
| Leaf of shf * 'a or_var
| Node of shf * 'a or_var * 'a tree * 'a tree * shf
(*
  Invariants:
  - All trees are complete.
  - Define get_shift inductively as [get_shift (Leaf (w, _)) := w] and
    [get_shift (Node (w, _, t1, t2, _)) := w + t1 + t2] then for every tree
    of the form Node (_, _, t1, t2, sub), we must have
    sub = get_shift t1 + get_shift t2.

  In the naive semantics:

  Leaf (w, x) := SHIFT^w (CONS (x, NIL))
  Node (w, x, t1, t2, _) := SHIFT^w (CONS (x, t1 @ t2))

*)

type 'a subs = Nil of shf * int | Cons of int * 'a tree * 'a subs
(*
  In the naive semantics mentioned above, we have the following.

  Nil (w, n) stands for SHIFT^w (ID n) where ID n is a compact form of identity
  substitution, defined inductively as

  ID 0 := NIL
  ID (S n) := CONS (Var 1, SHIFT (ID n))

  Cons (h, t, s) stands for (t @ s) and h is the total number of values in the
  tree t. In particular, it is always of the form 2^n - 1 for some n.
*)

(* Returns the number of shifts contained in the whole tree. *)
let eval = function
| Leaf (w, _) -> w
| Node (w1, _, _, _, w2) -> cmp w1 w2

let leaf x = Leaf (idn, x)
let node x t1 t2 = Node (idn, x, t1, t2, cmp (eval t1) (eval t2))

let rec tree_get h w t i = match t with
| Leaf (w', x) ->
  let w = cmp w w' in
  if i = 0 then w, Inl x else assert false
| Node (w', x, t1, t2, _) ->
  let w = cmp w w' in
  if i = 0 then w, Inl x
  else
    let h = h / 2 in
    if i <= h then tree_get h w t1 (i - 1)
    else tree_get h (cmp w (eval t1)) t2 (i - h - 1)

let rec get w l i = match l with
| Nil (w', n) ->
  let w = cmp w w' in
  if i < n then w, Inl (Var (i + 1))
  else n + w, Inr (i - n) (* FIXME: double check *)
| Cons (h, t, rem) ->
  if i < h then tree_get h w t i else get (cmp (eval t) w) rem (i - h)

let get l i = get idn l i

let tree_write w = function
| Leaf (w', x) -> Leaf (cmp w w', x)
| Node (w', x, t1, t2, wt) -> Node (cmp w w', x, t1, t2, wt)

let write w l = match l with
| Nil (w', n) -> Nil (cmp w w', n)
| Cons (h, t, rem) -> Cons (h, tree_write w t, rem)

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
| Nil (w, _) -> Int.equal w 0
| Cons (_, _, _) -> false

let subs_cons v s = cons (Arg v) s

let rec push_vars i s =
  if Int.equal i 0 then s
  else push_vars (pred i) (cons (Var i) s)

let subs_liftn n s =
  if Int.equal n 0 then s
  else match s with
  | Nil (0, m) -> Nil (0, m + n) (* Preserve identity substitutions *)
  | Nil _ | Cons _ ->
    let s = write n s in
    push_vars n s

let subs_lift s = match s with
| Nil (0, m) -> Nil (0, m + 1) (* Preserve identity substitutions *)
| Nil _ | Cons _ ->
  cons (Var 1) (write 1 s)

let subs_id n = Nil (0, n)

let subs_shft (n, s) = write n s

(* pop is the n-ary tailrec variant of a function whose typing rules would be
   given as follows. Assume Γ ⊢ e : Δ, A, then
   - Γ := Ξ, A, Ω for some Ξ and Ω with |Ω| := fst (pop e)
   - Ξ ⊢ snd (pop e) : Δ
*)
let rec pop n i e =
  if Int.equal n 0 then i, e
  else match e with
  | ELID -> i, e
  | ELLFT (k, e) ->
    if k <= n then pop (n - k) i e
    else i, ELLFT (k - n, e)
  | ELSHFT (e, k) -> pop n (i + k) e

let apply mk e = function
| Var i -> Var (reloc_rel i e)
| Arg v -> Arg (mk e v)

let rec tree_map mk e = function
| Leaf (w, x) ->
  let (n, e) = pop w 0 e in
  Leaf (w + n, apply mk e x), e
| Node (w, x, t1, t2, _) ->
  let (n, e) = pop w 0 e in
  let x = apply mk e x in
  let t1, e = tree_map mk e t1 in
  let t2, e = tree_map mk e t2 in
  Node (w + n, x, t1, t2, cmp (eval t1) (eval t2)), e

let rec lift_id e n = match e with
| ELID -> Nil (0, n)
| ELSHFT (e, k) -> write k (lift_id e n)
| ELLFT (k, e) ->
  if k <= n then subs_liftn k (lift_id e (n - k))
  else assert false

let rec lift_subst mk e s = match s with
| Nil (w, m) ->
  let (n, e) = pop w 0 e in
  write (w + n) (lift_id e m)
| Cons (h, t, rem) ->
  let t, e = tree_map mk e t in
  let rem = lift_subst mk e rem in
  Cons (h, t, rem)

module Internal =
struct

type 'a or_rel = REL of int | VAL of int * 'a

let to_rel shift = function
| Var i -> REL (i + shift)
| Arg v -> VAL (shift, v)

let rec get_tree_subst shift accu = function
| Leaf (w, x) ->
  to_rel (shift + w) x :: accu
| Node (w, x, l, r, _) ->
  let accu = get_tree_subst (shift + w + eval l) accu r in
  let accu = get_tree_subst (shift + w) accu l in
  to_rel (shift + w) x :: accu

let rec get_subst shift accu = function
| Nil (w, n) ->
  List.init n (fun i -> REL (w + i + shift + 1))
| Cons (_, t, s) ->
  let accu = get_subst (shift + eval t) accu s in
  get_tree_subst shift accu t

let rec get_shift accu = function
| Nil (w, n) -> accu + w + n
| Cons (_, t, s) -> get_shift (eval t + accu) s

let repr (s : 'a subs) =
  let shift = get_shift 0 s in
  let subs = get_subst 0 [] s in
  subs, shift

end
