(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(**********************************************************************)
(** The integer logarithms with base 2. 

    There are three logarithms,
    depending on the rounding of the real 2-based logarithm:
    - [Log_inf]: [y = (Log_inf x) iff 2^y <= x < 2^(y+1)]
      i.e. [Log_inf x] is the biggest integer that is smaller than [Log x]
    - [Log_sup]: [y = (Log_sup x) iff 2^(y-1) < x <= 2^y]
      i.e. [Log_inf x] is the smallest integer that is bigger than [Log x]
    - [Log_nearest]: [y= (Log_nearest x) iff 2^(y-1/2) < x <= 2^(y+1/2)]
      i.e. [Log_nearest x] is the integer nearest from [Log x] *)

Require ZArith_base.
Require Omega.
Require Zcomplements.
Require Zpower.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

Section Log_pos. (* Log of positive integers *)

(** First we build [log_inf] and [log_sup] *)

Fixpoint log_inf [p:positive] : Z :=  
  Cases p of
    xH => `0`	 				(* 1 *)
  | (xO q) => (Zs (log_inf q))		(* 2n *)
  | (xI q) => (Zs (log_inf q))		(* 2n+1 *)
  end.
Fixpoint log_sup [p:positive] : Z :=
  Cases p of
    xH => `0`					(* 1 *)
  | (xO n) => (Zs (log_sup n)) 		(* 2n *)
  | (xI n) => (Zs (Zs (log_inf n)))		(* 2n+1 *)
  end.

Hints Unfold log_inf log_sup.

(** Then we give the specifications of [log_inf] and [log_sup] 
    and prove their validity *)

(*i Hints Resolve ZERO_le_S : zarith. i*)
Hints Resolve Zle_trans : zarith.

Theorem log_inf_correct : (x:positive) ` 0 <= (log_inf x)` /\
  ` (two_p (log_inf x)) <= (POS x) < (two_p (Zs (log_inf x)))`.
Induction x; Intros; Simpl;
[ Elim H; Intros Hp HR; Clear H; Split;
  [ Auto with zarith
  | Conditional (Apply Zle_le_S; Trivial) Rewrite two_p_S with x:=(Zs (log_inf p));
    Conditional Trivial Rewrite two_p_S;
    Conditional Trivial Rewrite two_p_S in HR;
    Rewrite (POS_xI p); Omega ]
| Elim H; Intros Hp HR; Clear H; Split;
  [ Auto with zarith
  | Conditional (Apply Zle_le_S; Trivial) Rewrite two_p_S with x:=(Zs (log_inf p));
    Conditional Trivial Rewrite two_p_S;
    Conditional Trivial Rewrite two_p_S in HR;
    Rewrite (POS_xO p); Omega ]
| Unfold two_power_pos; Unfold shift_pos; Simpl; Omega 
].
Qed.

Definition log_inf_correct1 :=
	[p:positive](proj1 ? ? (log_inf_correct p)).
Definition log_inf_correct2 := 
	[p:positive](proj2 ? ? (log_inf_correct p)).

Opaque log_inf_correct1 log_inf_correct2.

Hints Resolve log_inf_correct1 log_inf_correct2 : zarith.

Lemma log_sup_correct1 : (p:positive)` 0 <= (log_sup p)`.
Induction p; Intros; Simpl; Auto with zarith.
Qed.

(** For every [p], either [p] is a power of two and [(log_inf p)=(log_sup p)]
    either [(log_sup p)=(log_inf p)+1] *)

Theorem log_sup_log_inf : (p:positive)
  IF (POS p)=(two_p (log_inf p)) 
  then (POS p)=(two_p (log_sup p))
  else ` (log_sup p)=(Zs (log_inf p))`.

Induction p; Intros;
[ Elim H; Right; Simpl;
  Rewrite (two_p_S (log_inf p0) (log_inf_correct1 p0));
  Rewrite POS_xI; Unfold Zs; Omega
| Elim H; Clear H; Intro Hif;
  [ Left; Simpl;
    Rewrite (two_p_S (log_inf p0) (log_inf_correct1 p0));
    Rewrite (two_p_S (log_sup p0) (log_sup_correct1 p0));
    Rewrite <- (proj1 ? ? Hif); Rewrite <- (proj2 ? ? Hif);
    Auto
  | Right; Simpl;
    Rewrite (two_p_S (log_inf p0) (log_inf_correct1 p0));
    Rewrite POS_xO; Unfold Zs; Omega ]
| Left; Auto ].
Qed.

Theorem log_sup_correct2 : (x:positive)
  ` (two_p (Zpred (log_sup x))) < (POS x) <= (two_p (log_sup x))`.

Intro.
Elim (log_sup_log_inf x).
(* x is a power of two and [log_sup = log_inf] *)
Intros (E1,E2); Rewrite E2.
Split ; [ Apply two_p_pred; Apply log_sup_correct1 | Apply Zle_n ].
Intros (E1,E2); Rewrite E2.
Rewrite <- (Zpred_Sn (log_inf x)).
Generalize (log_inf_correct2 x); Omega.
Qed.

Lemma log_inf_le_log_sup : 
	(p:positive) `(log_inf p) <= (log_sup p)`.
Induction p; Simpl; Intros; Omega.
Qed.

Lemma log_sup_le_Slog_inf : 
	(p:positive) `(log_sup p) <= (Zs (log_inf p))`.
Induction p; Simpl; Intros; Omega.
Qed.

(** Now it's possible to specify and build the [Log] rounded to the nearest *)

Fixpoint log_near[x:positive] : Z :=
  Cases x of 
    xH => `0`
  | (xO xH) => `1`
  | (xI xH) => `2`
  | (xO y)  => (Zs (log_near y))
  | (xI y)  => (Zs (log_near y))
  end.    

Theorem log_near_correct1 : (p:positive)` 0 <= (log_near p)`.
Induction p; Simpl; Intros; 
[Elim p0; Auto with zarith | Elim p0; Auto with zarith | Trivial with zarith ].
Intros; Apply Zle_le_S.
Generalize H0; Elim p1; Intros; Simpl;
    [ Assumption | Assumption | Apply ZERO_le_POS ].
Intros; Apply Zle_le_S.
Generalize H0; Elim p1; Intros; Simpl;
    [ Assumption | Assumption | Apply ZERO_le_POS ].
Qed.

Theorem log_near_correct2: (p:positive)
  (log_near p)=(log_inf p)
\/(log_near p)=(log_sup p).
Induction p.
Intros p0 [Einf|Esup].
Simpl. Rewrite Einf.
Case p0; [Left | Left | Right]; Reflexivity.
Simpl; Rewrite Esup.
Elim (log_sup_log_inf p0).
Generalize (log_inf_le_log_sup p0).
Generalize (log_sup_le_Slog_inf p0).
Case p0; Auto with zarith.
Intros; Omega.
Case p0; Intros; Auto with zarith.
Intros p0 [Einf|Esup].
Simpl.
Repeat Rewrite Einf.
Case p0; Intros; Auto with zarith.
Simpl.
Repeat Rewrite Esup.
Case p0; Intros; Auto with zarith.
Auto.
Qed.

(*i******************
Theorem log_near_correct: (p:positive)
  `| (two_p (log_near p)) - (POS p) | <= (POS p)-(two_p (log_inf p))`
  /\`| (two_p (log_near p)) - (POS p) | <= (two_p (log_sup p))-(POS p)`.
Intro.
Induction p.
Intros p0 [(Einf1,Einf2)|(Esup1,Esup2)].
Unfold log_near log_inf log_sup. Fold log_near log_inf log_sup.
Rewrite Einf1.
Repeat Rewrite two_p_S.
Case p0; [Left | Left | Right].

Split.
Simpl.
Rewrite E1; Case p0; Try Reflexivity.
Compute.
Unfold log_near; Fold log_near.
Unfold log_inf; Fold log_inf.
Repeat Rewrite E1.
Split.
**********************************i*)

End Log_pos.

Section divers.

(** Number of significative digits. *)

Definition N_digits :=
  [x:Z]Cases x of 
       	  (POS p) => (log_inf p)
        | (NEG p) => (log_inf p)
	|  ZERO   => `0`
       end.

Lemma ZERO_le_N_digits : (x:Z) ` 0 <= (N_digits x)`.
Induction x; Simpl;
[ Apply Zle_n
| Exact log_inf_correct1
| Exact log_inf_correct1].
Qed.

Lemma log_inf_shift_nat : 
  (n:nat)(log_inf (shift_nat n xH))=(inject_nat n).
Induction n; Intros;
[ Try Trivial
| Rewrite -> inj_S; Rewrite <- H; Reflexivity].
Qed.

Lemma log_sup_shift_nat : 
  (n:nat)(log_sup (shift_nat n xH))=(inject_nat n).
Induction n; Intros;
[ Try Trivial
| Rewrite -> inj_S; Rewrite <- H; Reflexivity].
Qed.

(** [Is_power p] means that p is a power of two *)
Fixpoint Is_power[p:positive] : Prop :=
  Cases p of
    xH => True
  | (xO q) => (Is_power q)
  | (xI q) => False
  end.

Lemma Is_power_correct :
  (p:positive) (Is_power p) <-> (Ex [y:nat](p=(shift_nat y xH))).

Split; 
[ Elim p; 
   [ Simpl; Tauto
   | Simpl; Intros; Generalize (H H0); Intro H1; Elim H1; Intros y0 Hy0;
     Exists (S y0); Rewrite Hy0; Reflexivity
   | Intro; Exists O; Reflexivity]
| Intros; Elim H; Intros; Rewrite -> H0; Elim x; Intros; Simpl; Trivial].
Qed.

Lemma Is_power_or : (p:positive) (Is_power p)\/~(Is_power p).
Induction p;
[ Intros; Right; Simpl; Tauto
| Intros; Elim H; 
   [ Intros; Left; Simpl; Exact H0
   | Intros; Right; Simpl; Exact H0]
| Left; Simpl; Trivial].
Qed.

End divers.







