(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Explicit substitutions *)

(** {6 Explicit substitutions } *)
(** Explicit substitutions of type ['a]. 
    - ESID(n)             = %n END   bounded identity
    - CONS([|t1..tn|],S)  = (S.t1...tn)    parallel substitution
        (beware of the order: indice 1 is substituted by tn)
    - SHIFT(n,S)          = (^n o S) terms in S are relocated with n vars
    - LIFT(n,S)           = (%n S) stands for ((^n o S).n...1)
         (corresponds to S crossing n binders) *)
type 'a subs =
  | ESID of int
  | CONS of 'a array * 'a subs
  | SHIFT of int * 'a subs
  | LIFT of int * 'a subs

(** Derived constructors granting basic invariants *)
val subs_cons: 'a array * 'a subs -> 'a subs
val subs_shft: int * 'a subs -> 'a subs
val subs_lift: 'a subs -> 'a subs
val subs_liftn: int -> 'a subs -> 'a subs

(** [subs_shift_cons(k,s,[|t1..tn|])] builds (^k s).t1..tn *)
val subs_shift_cons: int * 'a subs * 'a array -> 'a subs

(** [expand_rel k subs] expands de Bruijn [k] in the explicit substitution
    [subs]. The result is either (Inl(lams,v)) when the variable is
    substituted by value [v] under lams binders (i.e. v *has* to be
    shifted by lams), or (Inr (k',p)) when the variable k is just relocated
    as k'; p is None if the variable points inside subs and Some(k) if the
    variable points k bindings beyond subs (cf argument of ESID).
*)
val expand_rel: int -> 'a subs -> (int * 'a, int * int option) Util.union

(** Tests whether a substitution behaves like the identity *)
val is_subs_id: 'a subs -> bool

(** Composition of substitutions: [comp mk_clos s1 s2] computes a
    substitution equivalent to applying s2 then s1. Argument
    mk_clos is used when a closure has to be created, i.e. when
    s1 is applied on an element of s2.
*)
val comp : ('a subs * 'a -> 'a) -> 'a subs -> 'a subs -> 'a subs

(** {6 Compact representation } *)
(** Compact representation of explicit relocations
    - [ELSHFT(l,n)] == lift of [n], then apply [lift l].
    - [ELLFT(n,l)] == apply [l] to de Bruijn > [n] i.e under n binders. *)
type lift =
  | ELID
  | ELSHFT of lift * int
  | ELLFT of int * lift

val el_shft : int -> lift -> lift
val el_liftn : int -> lift -> lift
val el_lift : lift -> lift
val reloc_rel : int -> lift -> int
val is_lift_id : lift -> bool
