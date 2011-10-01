(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file centralizes the lemmas about [Z], classifying them
    according to the way they can be used in automatic search  *)

(** Lemmas which clearly leads to simplification during proof search are *)
(** declared as Hints. A definite status (Hint or not) for the other lemmas *)
(** remains to be given *)

(** Structure of the file *)
(** - simplification lemmas (only those are declared as Hints) *)
(** - reversible lemmas relating operators *)
(** - useful Bottom-up lemmas              *)
(** - irreversible lemmas with meta-variables *)
(** - unclear or too specific lemmas       *)
(** - lemmas to be used as rewrite rules   *)

(** Lemmas involving positive and compare are not taken into account *)

Require Import BinInt.
Require Import Zorder.
Require Import Zmin.
Require Import Zabs.
Require Import Zcompare.
Require Import Znat.
Require Import auxiliary.
Require Import Zmisc.
Require Import Wf_Z.

(************************************************************************)
(** *                 Simplification lemmas                             *)

(** No subgoal or smaller subgoals                                     *)

Hint Resolve
  (** ** Reversible simplification lemmas (no loss of information)      *)
  (** Should clearly be declared as hints                               *)

  (** Lemmas ending by eq *)
  Zsucc_eq_compat (* :(n,m:Z)`n = m`->`(Zs n) = (Zs m)` *)

  (** Lemmas ending by Zgt *)
  Zsucc_gt_compat (* :(n,m:Z)`m > n`->`(Zs m) > (Zs n)` *)
  Zgt_succ (* :(n:Z)`(Zs n) > n` *)
  Zorder.Zgt_pos_0 (* :(p:positive)`(POS p) > 0` *)
  Zplus_gt_compat_l (* :(n,m,p:Z)`n > m`->`p+n > p+m` *)
  Zplus_gt_compat_r (* :(n,m,p:Z)`n > m`->`n+p > m+p` *)

  (** Lemmas ending by Zlt *)
  Zlt_succ (* :(n:Z)`n < (Zs n)` *)
  Zsucc_lt_compat (* :(n,m:Z)`n < m`->`(Zs n) < (Zs m)` *)
  Zlt_pred (* :(n:Z)`(Zpred n) < n` *)
  Zplus_lt_compat_l (* :(n,m,p:Z)`n < m`->`p+n < p+m` *)
  Zplus_lt_compat_r (* :(n,m,p:Z)`n < m`->`n+p < m+p` *)

  (** Lemmas ending by Zle *)
  Zle_0_nat (* :(n:nat)`0 <= (inject_nat n)` *)
  Zorder.Zle_0_pos (* :(p:positive)`0 <= (POS p)` *)
  Zle_refl (* :(n:Z)`n <= n` *)
  Zle_succ (* :(n:Z)`n <= (Zs n)` *)
  Zsucc_le_compat (* :(n,m:Z)`m <= n`->`(Zs m) <= (Zs n)` *)
  Zle_pred (* :(n:Z)`(Zpred n) <= n` *)
  Zle_min_l (* :(n,m:Z)`(Zmin n m) <= n` *)
  Zle_min_r (* :(n,m:Z)`(Zmin n m) <= m` *)
  Zplus_le_compat_l (* :(n,m,p:Z)`n <= m`->`p+n <= p+m` *)
  Zplus_le_compat_r (* :(a,b,c:Z)`a <= b`->`a+c <= b+c` *)
  Zabs_pos (* :(x:Z)`0 <= |x|` *)

  (** ** Irreversible simplification lemmas *)
  (** Probably to be declared as hints, when no other simplification is possible *)

  (** Lemmas ending by eq *)
  BinInt.Z_eq_mult (* :(x,y:Z)`y = 0`->`y*x = 0` *)
  Zplus_eq_compat (* :(n,m,p,q:Z)`n = m`->`p = q`->`n+p = m+q` *)

  (** Lemmas ending by Zge *)
  Zorder.Zmult_ge_compat_r (* :(a,b,c:Z)`a >= b`->`c >= 0`->`a*c >= b*c` *)
  Zorder.Zmult_ge_compat_l (* :(a,b,c:Z)`a >= b`->`c >= 0`->`c*a >= c*b` *)
  Zorder.Zmult_ge_compat (* :
      (a,b,c,d:Z)`a >= c`->`b >= d`->`c >= 0`->`d >= 0`->`a*b >= c*d` *)

  (** Lemmas ending by Zlt *)
  Zorder.Zmult_gt_0_compat (* :(a,b:Z)`a > 0`->`b > 0`->`a*b > 0` *)
  Zlt_lt_succ (* :(n,m:Z)`n < m`->`n < (Zs m)` *)

  (** Lemmas ending by Zle *)
  Zorder.Zmult_le_0_compat (* :(x,y:Z)`0 <= x`->`0 <= y`->`0 <= x*y` *)
  Zorder.Zmult_le_compat_r (* :(a,b,c:Z)`a <= b`->`0 <= c`->`a*c <= b*c` *)
  Zorder.Zmult_le_compat_l (* :(a,b,c:Z)`a <= b`->`0 <= c`->`c*a <= c*b` *)
  Zplus_le_0_compat (* :(x,y:Z)`0 <= x`->`0 <= y`->`0 <= x+y` *)
  Zle_le_succ (* :(x,y:Z)`x <= y`->`x <= (Zs y)` *)
  Zplus_le_compat (* :(n,m,p,q:Z)`n <= m`->`p <= q`->`n+p <= m+q` *)

  : zarith.
