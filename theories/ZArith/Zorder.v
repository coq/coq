(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*i $Id$ i*)

(** Binary Integers (Pierre Crégut (CNET, Lannion, France) *)

Require fast_integer.
Require Arith.
Require Decidable.
Require Zsyntax.

V7only [Import nat_scope.].
Open Local Scope Z_scope.

Set Implicit Arguments.
V7only [Unset Implicit Arguments.].

Implicit Variable Type x,y,z:Z.

(**********************************************************************)
(** Properties of the order relations on binary integers *)

(** Trichotomy *)

Theorem Ztrichotomy_inf : (m,n:Z) {`m<n`} + {m=n} + {`m>n`}.
Proof.
Unfold Zgt Zlt; Intros m n; Assert H:=(refl_equal ? (Zcompare m n)).
  LetTac x := (Zcompare m n) in 2 H Goal.
  NewDestruct x; 
    [Left; Right;Rewrite Zcompare_EGAL_eq with 1:=H 
    | Left; Left
    | Right ]; Reflexivity.
Qed.

Theorem Ztrichotomy : (m,n:Z) `m<n` \/ m=n \/ `m>n`.
Proof.
  Intros m n; NewDestruct (Ztrichotomy_inf m n) as [[Hlt|Heq]|Hgt];
    [Left | Right; Left |Right; Right]; Assumption.
Qed.

(**********************************************************************)
(** Decidability of equality and order on Z *)

Theorem dec_eq: (x,y:Z) (decidable (x=y)).
Proof.
Intros x y; Unfold decidable ; Elim (Zcompare_EGAL x y);
Intros H1 H2; Elim (Dcompare (Zcompare x y)); [
    Tauto
  | Intros H3; Right; Unfold not ; Intros H4;
    Elim H3; Rewrite (H2 H4); Intros H5; Discriminate H5].
Qed. 

Theorem dec_Zne: (x,y:Z) (decidable (Zne x y)).
Proof.
Intros x y; Unfold decidable Zne ; Elim (Zcompare_EGAL x y).
Intros H1 H2; Elim (Dcompare (Zcompare x y)); 
  [ Right; Rewrite H1; Auto
  | Left; Unfold not; Intro; Absurd (Zcompare x y)=EGAL; 
    [ Elim H; Intros HR; Rewrite HR; Discriminate 
    | Auto]].
Qed.

Theorem dec_Zle: (x,y:Z) (decidable `x<=y`).
Proof.
Intros x y; Unfold decidable Zle ; Elim (Zcompare x y); [
    Left; Discriminate
  | Left; Discriminate
  | Right; Unfold not ; Intros H; Apply H; Trivial with arith].
Qed.

Theorem dec_Zgt: (x,y:Z) (decidable `x>y`).
Proof.
Intros x y; Unfold decidable Zgt ; Elim (Zcompare x y);
  [ Right; Discriminate | Right; Discriminate | Auto with arith].
Qed.

Theorem dec_Zge: (x,y:Z) (decidable `x>=y`).
Proof.
Intros x y; Unfold decidable Zge ; Elim (Zcompare x y); [
  Left; Discriminate
| Right; Unfold not ; Intros H; Apply H; Trivial with arith
| Left; Discriminate]. 
Qed.

Theorem dec_Zlt: (x,y:Z) (decidable `x<y`).
Proof.
Intros x y; Unfold decidable Zlt ; Elim (Zcompare x y);
  [ Right; Discriminate | Auto with arith | Right; Discriminate].
Qed.

Theorem not_Zeq : (x,y:Z) ~ x=y -> `x<y` \/ `y<x`.
Proof.
Intros x y; Elim (Dcompare (Zcompare x y)); [
  Intros H1 H2; Absurd x=y; [ Assumption | Elim (Zcompare_EGAL x y); Auto with arith]
| Unfold Zlt ; Intros H; Elim H; Intros H1; 
    [Auto with arith | Right; Elim (Zcompare_ANTISYM x y); Auto with arith]].
Qed. 

(** Relating strict and large orders *)

Lemma Zgt_lt : (m,n:Z) `m>n` -> `n<m`.
Proof.
Unfold Zgt Zlt ;Intros m n H; Elim (Zcompare_ANTISYM m n); Auto with arith.
Qed.

Lemma Zlt_gt : (m,n:Z) `m<n` -> `n>m`.
Proof.
Unfold Zgt Zlt ;Intros m n H; Elim (Zcompare_ANTISYM n m); Auto with arith.
Qed.

Lemma Zge_le : (m,n:Z) `m>=n` -> `n<=m`.
Proof.
Intros m n; Change ~`m<n`-> ~`n>m`;
Unfold not; Intros H1 H2; Apply H1; Apply Zgt_lt; Assumption.
Qed.

Lemma Zle_ge : (m,n:Z) `m<=n` -> `n>=m`.
Proof.
Intros m n; Change ~`m>n`-> ~`n<m`;
Unfold not; Intros H1 H2; Apply H1; Apply Zlt_gt; Assumption.
Qed.

Lemma Zle_not_gt     : (n,m:Z)`n<=m` -> ~`n>m`.
Proof.
Trivial.
Qed.

Lemma Zgt_not_le     : (n,m:Z)`n>m` -> ~`n<=m`.
Proof.
Intros n m H1 H2; Apply H2; Assumption.
Qed.

Lemma Zle_not_lt : (n,m:Z)`n<=m` -> ~`m<n`.
Proof.
Intros n m H1 H2.
Assert H3:=(Zlt_gt ? ? H2).
Apply Zle_not_gt with n m; Assumption.
Qed.

Lemma Zlt_not_le : (n,m:Z)`n<m` -> ~`m<=n`.
Proof.
Intros n m H1 H2.
Apply Zle_not_lt with m n; Assumption.
Qed.

Theorem not_Zge : (x,y:Z) ~`x>=y` -> `x<y`.
Proof.
Unfold Zge Zlt ; Intros x y H; Apply dec_not_not;
  [ Exact (dec_Zlt x y) | Assumption].
Qed.
 
Theorem not_Zlt : (x,y:Z) ~`x<y` -> `x>=y`.
Proof.
Unfold Zlt Zge; Auto with arith.
Qed.

Lemma not_Zgt : (x,y:Z)~`x>y` -> `x<=y`.
Proof.
Trivial.
Qed.

Theorem not_Zle : (x,y:Z) ~`x<=y` -> `x>y`.
Proof.
Unfold Zle Zgt ; Intros x y H; Apply dec_not_not;
  [ Exact (dec_Zgt x y) | Assumption].
Qed.
 
(** Reflexivity *)

Lemma Zle_n : (n:Z) (Zle n n).
Proof.
Intros n; Unfold Zle; Rewrite (Zcompare_x_x n); Discriminate.
Qed. 

(** Antisymmetry *)

Lemma Zle_antisym : (n,m:Z)`n<=m`->`m<=n`->n=m.
Proof.
Intros n m H1 H2; NewDestruct (Ztrichotomy n m) as [Hlt|[Heq|Hgt]]. 
  Absurd `m>n`; [ Apply Zle_not_gt | Apply Zlt_gt]; Assumption.
  Assumption.
  Absurd `n>m`; [ Apply Zle_not_gt | Idtac]; Assumption.
Qed.

(** Asymmetry *)

Lemma Zgt_not_sym    : (n,m:Z)`n>m` -> ~`m>n`.
Proof.
Unfold Zgt ;Intros n m H; Elim (Zcompare_ANTISYM n m); Intros H1 H2;
Rewrite -> H1; [ Discriminate | Assumption ].
Qed.

Lemma Zlt_not_sym : (n,m:Z)`n<m` -> ~`m<n`.
Proof.
Intros n m H H1;
Assert H2:`m>n`. Apply Zlt_gt; Assumption.
Assert H3: `n>m`. Apply Zlt_gt; Assumption.
Apply Zgt_not_sym with m n; Assumption.
Qed.

(** Irreflexivity *)

Lemma Zgt_antirefl   : (n:Z)~`n>n`.
Proof.
Intros n H; Apply (Zgt_not_sym n n H H).
Qed.

Lemma Zlt_n_n : (n:Z)~`n<n`.
Proof.
Intros n H; Apply (Zlt_not_sym n n H H).
Qed.

(** Large = strict or equal *)

Lemma Zle_lt_or_eq : (n,m:Z)`n<=m`->(`n<m` \/ n=m).
Proof.
Intros n m H; NewDestruct (Ztrichotomy n m) as [Hlt|[Heq|Hgt]]; [
  Left; Assumption
| Right; Assumption
| Absurd `n>m`; [Apply Zle_not_gt|Idtac]; Assumption ].
Qed.

Lemma Zlt_le_weak : (n,m:Z)`n<m`->`n<=m`.
Proof.
Intros n m Hlt; Apply not_Zgt; Apply Zgt_not_sym; Apply Zlt_gt; Assumption.
Qed.

(** Dichotomy *)

Lemma Zle_or_lt : (n,m:Z)`n<=m`\/`m<n`.
Proof.
Intros n m; NewDestruct (Ztrichotomy n m) as [Hlt|[Heq|Hgt]]; [
  Left; Apply not_Zgt; Intro Hgt; Assert Hgt':=(Zlt_gt ? ? Hlt);
     Apply Zgt_not_sym with m n; Assumption
| Left; Rewrite Heq; Apply Zle_n
| Right; Apply Zgt_lt; Assumption ].
Qed.

(** Transitivity of strict orders *)

Lemma Zgt_trans      : (n,m,p:Z)`n>m`->`m>p`->`n>p`.
Proof.
Exact Zcompare_trans_SUPERIEUR.
Qed.

Lemma Zlt_trans : (n,m,p:Z)`n<m`->`m<p`->`n<p`.
Proof.
Intros n m p H1 H2; Apply Zgt_lt; Apply Zgt_trans with m:= m; 
Apply Zlt_gt; Assumption.
Qed.

(** Mixed transitivity *)

Lemma Zle_gt_trans : (n,m,p:Z)`m<=n`->`m>p`->`n>p`.
Proof.
Intros n m p H1 H2; NewDestruct (Zle_lt_or_eq m n H1) as [Hlt|Heq]; [
  Apply Zgt_trans with m; [Apply Zlt_gt; Assumption | Assumption ]
| Rewrite <- Heq; Assumption ].
Qed.

Lemma Zgt_le_trans : (n,m,p:Z)`n>m`->`p<=m`->`n>p`.
Proof.
Intros n m p H1 H2; NewDestruct (Zle_lt_or_eq p m H2) as [Hlt|Heq]; [
  Apply Zgt_trans with m; [Assumption|Apply Zlt_gt; Assumption]
| Rewrite Heq; Assumption ].
Qed.

Lemma Zlt_le_trans : (n,m,p:Z)`n<m`->`m<=p`->`n<p`.
Intros n m p H1 H2;Apply Zgt_lt;Apply Zle_gt_trans with m:=m;
  [ Assumption | Apply Zlt_gt;Assumption ].
Qed.

Lemma Zle_lt_trans : (n,m,p:Z)`n<=m`->`m<p`->`n<p`.
Proof.
Intros n m p H1 H2;Apply Zgt_lt;Apply Zgt_le_trans with m:=m; 
  [ Apply Zlt_gt;Assumption | Assumption ].
Qed.

(** Transitivity of large orders *)

Lemma Zle_trans : (n,m,p:Z)`n<=m`->`m<=p`->`n<=p`.
Proof.
Intros n m p H1 H2; Apply not_Zgt.
Intro Hgt; Apply Zle_not_gt with n m. Assumption.
Exact (Zgt_le_trans n p m Hgt H2).
Qed.

Lemma Zge_trans : (n, m, p : Z) `n>=m` -> `m>=p` -> `n>=p`.
Proof.
Intros n m p H1 H2.
Apply Zle_ge.
Apply Zle_trans with m; Apply Zge_le; Trivial.
Qed.

(** Compatibility of successor wrt to order *)

Lemma Zle_n_S : (n,m:Z) `m<=n` -> `(Zs m)<=(Zs n)`.
Proof.
Unfold Zle not ;Intros m n H1 H2; Apply H1; 
Rewrite <- (Zcompare_Zplus_compatible n m (POS xH));
Do 2 Rewrite (Zplus_sym (POS xH)); Exact H2.
Qed.

Lemma Zgt_n_S : (n,m:Z)`m>n` -> `(Zs m)>(Zs n)`.
Proof.
Unfold Zgt; Intros n m H; Rewrite Zcompare_n_S; Auto with arith.
Qed.

(** Simplification of successor wrt to order *)

Lemma Zgt_S_n        : (n,p:Z)`(Zs p)>(Zs n)`->`p>n`.
Proof.
Unfold Zs Zgt;Intros n p;Do 2 Rewrite -> [m:Z](Zplus_sym m (POS xH));
Rewrite -> (Zcompare_Zplus_compatible p n (POS xH));Trivial with arith.
Qed.

Lemma Zle_S_n     : (n,m:Z) `(Zs m)<=(Zs n)` -> `m<=n`.
Proof.
Unfold Zle not ;Intros m n H1 H2;Apply H1;
Unfold Zs ;Do 2 Rewrite <- (Zplus_sym (POS xH));
Rewrite -> (Zcompare_Zplus_compatible n m (POS xH));Assumption.
Qed.

(** Compatibility of addition wrt to order *)

Lemma Zgt_reg_l   : (n,m,p:Z)`n>m`->`p+n>p+m`.
Proof.
Unfold Zgt; Intros n m p H; Rewrite (Zcompare_Zplus_compatible n m p); 
Assumption.
Qed.

Lemma Zgt_reg_r : (n,m,p:Z)`n>m`->`n+p>m+p`.
Proof.
Intros n m p H; Rewrite (Zplus_sym n p); Rewrite (Zplus_sym m p); Apply Zgt_reg_l; Trivial.
Qed.

Lemma Zle_reg_l : (n,m,p:Z)`n<=m`->`p+n<=p+m`.
Proof.
Intros n m p; Unfold Zle not ;Intros H1 H2;Apply H1; 
Rewrite <- (Zcompare_Zplus_compatible n m p); Assumption.
Qed.

Lemma Zle_reg_r : (n,m,p:Z) `n<=m`->`n+p<=m+p`.
Proof.
Intros a b c;Do 2 Rewrite [n:Z](Zplus_sym n c); Exact (Zle_reg_l a b c).
Qed.

Lemma Zlt_reg_l : (n,m,p:Z)`n<m`->`p+n<p+m`.
Proof.
Unfold Zlt ;Intros n m p; Rewrite Zcompare_Zplus_compatible;Trivial with arith.
Qed.

Lemma Zlt_reg_r : (n,m,p:Z)`n<m`->`n+p<m+p`.
Proof.
Intros n m p H; Rewrite (Zplus_sym n p); Rewrite (Zplus_sym m p); Apply Zlt_reg_l; Trivial.
Qed.

Lemma Zlt_le_reg : (a,b,c,d:Z) `a<b`->`c<=d`->`a+c<b+d`.
Proof.
Intros a b c d H0 H1.
Apply Zlt_le_trans with (Zplus b c).
Apply  Zlt_reg_r; Trivial.
Apply  Zle_reg_l; Trivial.
Qed.

Lemma Zle_lt_reg : (a,b,c,d:Z) `a<=b`->`c<d`->`a+c<b+d`.
Proof.
Intros a b c d H0 H1.
Apply Zle_lt_trans with (Zplus b c).
Apply  Zle_reg_r; Trivial.
Apply  Zlt_reg_l; Trivial.
Qed.

Lemma Zle_plus_plus : (n,m,p,q:Z) `n<=m`->(Zle p q)->`n+p<=m+q`.
Proof.
Intros n m p q; Intros H1 H2;Apply Zle_trans with m:=(Zplus n q); [
  Apply Zle_reg_l;Assumption | Apply Zle_reg_r;Assumption ].
Qed.

V7only [Set Implicit Arguments.].

Lemma Zlt_Zplus : (x1,x2,y1,y2:Z)`x1 < x2` -> `y1 < y2` -> `x1 + y1 < x2 + y2`.
Intros; Apply Zle_lt_reg. Apply Zlt_le_weak; Assumption. Assumption.
Qed.

V7only [Unset Implicit Arguments.].

(** Compatibility of addition wrt to being positive *)

Theorem Zle_0_plus : (x,y:Z) `0<=x` -> `0<=y` -> `0<=x+y`.
Proof.
Intros x y H1 H2;Rewrite <- (Zero_left ZERO); Apply Zle_plus_plus; Assumption.
Qed.

(** Simplification of addition wrt to order *)

Lemma Zsimpl_gt_plus_l : (n,m,p:Z)`p+n>p+m`->`n>m`.
Proof.
Unfold Zgt; Intros n m p H; 
	Rewrite <- (Zcompare_Zplus_compatible n m p); Assumption.
Qed.

Lemma Zsimpl_gt_plus_r : (n,m,p:Z)`n+p>m+p`->`n>m`.
Proof.
Intros n m p H; Apply Zsimpl_gt_plus_l with p.
Rewrite (Zplus_sym p n); Rewrite (Zplus_sym p m); Trivial.
Qed.

Lemma Zsimpl_le_plus_l : (p,n,m:Z)`p+n<=p+m`->`n<=m`.
Proof.
Intros p n m; Unfold Zle not ;Intros H1 H2;Apply H1; 
Rewrite (Zcompare_Zplus_compatible n m p); Assumption.
Qed.
 
Lemma Zsimpl_le_plus_r : (p,n,m:Z)`n+p<=m+p`->`n<=m`.
Proof.
Intros p n m H; Apply Zsimpl_le_plus_l with p.
Rewrite (Zplus_sym p n); Rewrite (Zplus_sym p m); Trivial.
Qed.

Lemma Zsimpl_lt_plus_l : (n,m,p:Z)`p+n<p+m`->`n<m`.
Proof.
Unfold Zlt ;Intros n m p; 
	Rewrite Zcompare_Zplus_compatible;Trivial with arith.
Qed.
 
Lemma Zsimpl_lt_plus_r : (n,m,p:Z)`n+p<m+p`->`n<m`.
Proof.
Intros n m p H; Apply Zsimpl_lt_plus_l with p.
Rewrite (Zplus_sym p n); Rewrite (Zplus_sym p m); Trivial.
Qed.
 
(** Order, predecessor and successor *)

Lemma Zgt_Sn_n : (n:Z)`(Zs n)>n`.
Proof.
Exact Zcompare_Zs_SUPERIEUR.
Qed.

Lemma Zgt_le_S       : (n,p:Z)`p>n`->`(Zs n)<=p`.
Proof.
Unfold Zgt Zle; Intros n p H; Elim (Zcompare_et_un p n); Intros H1 H2;
Unfold not ;Intros H3; Unfold not in H1; Apply H1; [
  Assumption
| Elim (Zcompare_ANTISYM (Zplus n (POS xH)) p);Intros H4 H5;Apply H4;Exact H3].
Qed.

Lemma Zgt_S_le       : (n,p:Z)`(Zs p)>n`->`n<=p`.
Proof.
Intros n p H;Apply Zle_S_n; Apply Zgt_le_S; Assumption.
Qed.

V7only [ (* Relevance confirmed from Zextensions *) ].
Lemma Zlt_S_le: (n,p:Z)`n < (Zs p)`->`n <= p`.
Proof.
Intros; Apply Zgt_S_le; Apply Zlt_gt; Assumption.
Qed.

Lemma Zle_S_gt : (n,m:Z) `(Zs n)<=m` -> `m>n`.
Proof.
Intros n m H;Apply Zle_gt_trans with m:=(Zs n);
  [ Assumption | Apply Zgt_Sn_n ].
Qed.

Lemma Zle_gt_S       : (n,p:Z)`n<=p`->`(Zs p)>n`.
Proof.
Intros n p H; Apply Zgt_le_trans with p.
  Apply Zgt_Sn_n.
  Assumption.
Qed.

Lemma Zgt_pred : (n,p:Z)`p>(Zs n)`->`(Zpred p)>n`.
Proof.
Unfold Zgt Zs Zpred ;Intros n p H; 
Rewrite <- [x,y:Z](Zcompare_Zplus_compatible x y (POS xH));
Rewrite (Zplus_sym p); Rewrite Zplus_assoc; Rewrite [x:Z](Zplus_sym x n);
Simpl; Assumption.
Qed.

Lemma Zlt_ZERO_pred_le_ZERO : (n:Z) `0<n` -> `0<=(Zpred n)`.
Intros x H.
Rewrite (Zs_pred x) in H.
Apply Zgt_S_le.
Apply Zlt_gt.
Assumption.
Qed.

V7only [Set Implicit Arguments.].

Lemma Zgt0_le_pred : (y:Z) `y > 0` -> `0 <= (Zpred y)`.
Intros; Apply Zlt_ZERO_pred_le_ZERO; Apply Zgt_lt. Assumption.
Qed.

V7only [Unset Implicit Arguments.].

(** Special cases of ordered integers *)

V7only [ (* Relevance confirmed from Zdivides *) ].
Theorem Z_O_1: `0<1`.
Proof.
Red; Simpl; Auto; Intros; Red; Intros; Discriminate.
Qed.

V7only [ (* Relevance confirmed from Zdivides *) ].
Theorem Zle_NEG_POS: (p,q:positive) `(NEG p)<=(POS q)`.
Proof.
Intros p; Red; Simpl; Red; Intros H; Discriminate.
Qed.

Lemma Zle_n_Sn : (n:Z)`n<=(Zs n)`.
Proof.
Intros n; Apply Zgt_S_le;Apply Zgt_trans with m:=(Zs n) ;Apply Zgt_Sn_n.
Qed.

Lemma Zle_pred_n : (n:Z)`(Zpred n)<=n`.
Proof.
Intros n;Pattern 2 n ;Rewrite Zs_pred; Apply Zle_n_Sn.
Qed.

Lemma POS_gt_ZERO : (p:positive) `(POS p)>0`.
Unfold Zgt; Trivial.
Qed.

  (* weaker but useful (in [Zpower] for instance) *)
Lemma ZERO_le_POS : (p:positive) `0<=(POS p)`.
Intro; Unfold Zle; Discriminate.
Qed.

Lemma NEG_lt_ZERO : (p:positive)`(NEG p)<0`.
Unfold Zlt; Trivial.
Qed.

(** Weakening equality within order *)
 
Lemma Zlt_not_eq : (x,y:Z)`x<y` -> ~x=y.
Proof.
Unfold not; Intros x y H H0.
Rewrite H0 in H.
Apply (Zlt_n_n ? H).
Qed.

Lemma Zle_refl : (n,m:Z) n=m -> `n<=m`.
Proof.
Intros; Rewrite H; Apply Zle_n.
Qed.

(** Transitivity using successor *)

Lemma Zgt_trans_S  : (n,m,p:Z)`(Zs n)>m`->`m>p`->`n>p`.
Proof.
Intros n m p H1 H2;Apply Zle_gt_trans with m:=m;
  [ Apply Zgt_S_le; Assumption | Assumption ].
Qed.

Lemma Zgt_S        : (n,m:Z)`(Zs n)>m`->(`n>m`\/(m=n)).
Proof.
Intros n m H.
Assert Hle : `m<=n`.
  Apply Zgt_S_le; Assumption.
NewDestruct (Zle_lt_or_eq ? ? Hle) as [Hlt|Heq].
  Left; Apply Zlt_gt; Assumption.  
  Right; Assumption.
Qed.

Hints Resolve Zle_n Zle_n_Sn Zle_trans Zle_n_S : zarith.
Hints Immediate Zle_refl : zarith.

Lemma Zle_trans_S : (n,m:Z)`(Zs n)<=m`->`n<=m`.
Proof.
Intros n m H;Apply Zle_trans with m:=(Zs n); [ Apply Zle_n_Sn | Assumption ].
Qed.

Lemma Zle_Sn_n : (n:Z)~`(Zs n)<=n`.
Proof.
Intros n; Apply Zgt_not_le; Apply Zgt_Sn_n.
Qed.

Lemma Zlt_n_Sn : (n:Z)`n<(Zs n)`.
Proof.
Intro n; Apply Zgt_lt; Apply Zgt_Sn_n.
Qed.

Lemma Zlt_S : (n,m:Z)`n<m`->`n<(Zs m)`.
Intros n m H;Apply Zgt_lt; Apply Zgt_trans with m:=m; [
  Apply Zgt_Sn_n
| Apply Zlt_gt; Assumption ].
Qed.

Lemma Zlt_n_S : (n,m:Z)`n<m`->`(Zs n)<(Zs m)`.
Proof.
Intros n m H;Apply Zgt_lt;Apply Zgt_n_S;Apply Zlt_gt; Assumption.
Qed.

Lemma Zlt_S_n : (n,m:Z)`(Zs n)<(Zs m)`->`n<m`.
Proof.
Intros n m H;Apply Zgt_lt;Apply Zgt_S_n;Apply Zlt_gt; Assumption.
Qed.

Lemma Zlt_pred : (n,p:Z)`(Zs n)<p`->`n<(Zpred p)`.
Proof.
Intros n p H;Apply Zlt_S_n; Rewrite <- Zs_pred; Assumption.
Qed.

Lemma Zlt_pred_n_n : (n:Z)`(Zpred n)<n`.
Proof.
Intros n; Apply Zlt_S_n; Rewrite <- Zs_pred; Apply Zlt_n_Sn.
Qed.
 
Lemma Zlt_le_S : (n,p:Z)`n<p`->`(Zs n)<=p`.
Proof.
Intros n p H; Apply Zgt_le_S; Apply Zlt_gt; Assumption.
Qed.

Lemma Zlt_n_Sm_le : (n,m:Z)`n<(Zs m)`->`n<=m`.
Proof.
Intros n m H; Apply Zgt_S_le; Apply Zlt_gt; Assumption.
Qed.

Lemma Zle_lt_n_Sm : (n,m:Z)`n<=m`->`n<(Zs m)`.
Proof.
Intros n m H; Apply Zgt_lt; Apply Zle_gt_S; Assumption.
Qed.

Lemma Zle_le_S : (x,y:Z)`x<=y`->`x<=(Zs y)`.
Proof.
Intros.
Apply Zle_trans with y; Trivial with zarith.
Qed.

Hints Resolve Zle_le_S : zarith.

(** Compatibility of multiplication by a positive wrt to order *)

V7only [Set Implicit Arguments.].

Lemma Zle_Zmult_pos_right : (a,b,c : Z) `a<=b` -> `0<=c` -> `a*c<=b*c`.
Proof.
Intros; NewDestruct c.
  Do 2 Rewrite Zero_mult_right; Assumption.
  Rewrite (Zmult_sym a); Rewrite (Zmult_sym b).
    Unfold Zle; Rewrite Zcompare_Zmult_compatible; Assumption.
  Unfold Zle in H0; Contradiction H0; Reflexivity.
Qed.

Lemma Zle_Zmult_pos_left : (a,b,c : Z) `a<=b` -> `0<=c` -> `c*a<=c*b`.
Proof.
Intros a b c H1 H2; Rewrite (Zmult_sym c a);Rewrite (Zmult_sym c b).
Apply  Zle_Zmult_pos_right; Trivial.
Qed.

Lemma Zlt_Zmult_right : (x,y,z:Z)`z>0` -> `x < y` -> `x*z < y*z`.
Proof.
Intros; NewDestruct z.
  Contradiction (Zgt_antirefl `0`).
  Rewrite (Zmult_sym x); Rewrite (Zmult_sym y).
    Unfold Zlt; Rewrite Zcompare_Zmult_compatible; Assumption.
  Discriminate H.
Qed.

V7only [ (* Relevance confirmed from Zextensions *) ].
Lemma Zmult_lt_compat_r : (x,y,z:Z)`0<z` -> `x < y` -> `x*z < y*z`.
Proof.
Intros; Apply Zlt_Zmult_right; Try Apply Zlt_gt; Assumption.
Save.

Lemma Zle_Zmult_right : (x,y,z:Z)`z>0` -> `x <= y` -> `x*z <= y*z`.
Proof.
Intros x y z Hz Hxy.
Elim (Zle_lt_or_eq x y Hxy).
Intros; Apply Zlt_le_weak.
Apply Zlt_Zmult_right; Trivial.
Intros; Apply Zle_refl.
Rewrite H; Trivial.
Qed.

V7only [ (* Relevance confirmed from Zextensions *) ].
Lemma Zmult_lt_0_le_compat_r : (x,y,z:Z)`0 < z`->`x <= y`->`x*z <= y*z`.
Proof.
Intros; Apply Zle_Zmult_right; Try Apply Zlt_gt; Assumption.
Qed.

Lemma Zgt_Zmult_right : (x,y,z:Z)`z>0` -> `x > y` -> `x*z > y*z`.
Proof.
Intros; Apply Zlt_gt; Apply Zlt_Zmult_right; 
[ Assumption | Apply Zgt_lt ; Assumption ].
Qed.

Lemma Zlt_Zmult_left : (x,y,z:Z)`z>0` -> `x < y` -> `z*x < z*y`.
Proof.
Intros;
Rewrite (Zmult_sym z x); Rewrite (Zmult_sym z y);
Apply Zlt_Zmult_right; Assumption.
Qed.

V7only [ (* Relevance confirmed from Zextensions *) ].
Lemma Zmult_lt_compat_l : (x,y,z:Z)`0<z` -> `x < y` -> `z*x < z*y`.
Proof.
Intros;
Rewrite (Zmult_sym z x); Rewrite (Zmult_sym z y);
Apply Zlt_Zmult_right; Try Apply Zlt_gt; Assumption.
Save.

Lemma Zgt_Zmult_left : (x,y,z:Z)`z>0` -> `x > y` -> `z*x > z*y`.
Proof.
Intros;
Rewrite (Zmult_sym z x); Rewrite (Zmult_sym z y);
Apply Zgt_Zmult_right; Assumption.
Qed.

Lemma Zge_Zmult_pos_right : (a,b,c : Z) `a>=b` -> `c>=0` -> `a*c>=b*c`.
Proof.
Intros a b c H1 H2; Apply Zle_ge.
Apply Zle_Zmult_pos_right; Apply Zge_le; Trivial.
Qed.

Lemma Zge_Zmult_pos_left : (a,b,c : Z) 	`a>=b` -> `c>=0` -> `c*a>=c*b`.
Proof.
Intros a b c H1 H2; Apply Zle_ge.
Apply Zle_Zmult_pos_left; Apply Zge_le; Trivial.
Qed.

Lemma Zge_Zmult_pos_compat : 
  (a,b,c,d : Z) `a>=c` -> `b>=d` -> `c>=0` -> `d>=0` -> `a*b>=c*d`.
Proof.
Intros a b c d H0 H1 H2 H3.
Apply Zge_trans with (Zmult a d).
Apply Zge_Zmult_pos_left; Trivial.
Apply Zge_trans with c; Trivial. 
Apply Zge_Zmult_pos_right; Trivial.
Qed.

V7only [ (* Relevance confirmed from Zextensions *) ].
Lemma Zmult_le_compat: (a, b, c, d : Z)
 `a<=c` -> `b<=d` -> `0<=a` -> `0<=b` -> `a*b<=c*d`.
Proof.
Intros a b c d H0 H1 H2 H3.
Apply Zle_trans with (Zmult c b).
Apply Zle_Zmult_pos_right; Assumption.
Apply Zle_Zmult_pos_left.
Assumption.
Apply Zle_trans with a; Assumption.
Qed.

(** Simplification of multiplication by a positive wrt to being positive *)

Lemma Zlt_Zmult_right2 : (x,y,z:Z)`z>0`  -> `x*z < y*z` -> `x < y`.
Proof.
Intros; NewDestruct z.
  Contradiction (Zgt_antirefl `0`).
  Rewrite (Zmult_sym x) in H0; Rewrite (Zmult_sym y) in H0.
    Unfold Zlt in H0; Rewrite Zcompare_Zmult_compatible in H0; Assumption.
  Discriminate H.
Qed.

V7only [ (* Relevance confirmed from Zextensions *) ].
Lemma Zmult_lt_reg_r : (a, b, c : Z) `0<c` -> `a*c<b*c` -> `a<b`.
Proof.
Intros a b c H0 H1.
Apply Zlt_Zmult_right2 with c; Try Apply Zlt_gt; Assumption.
Qed.

Lemma Zle_mult_simpl : (a,b,c:Z)`c>0`->`a*c<=b*c`->`a<=b`.
Proof.
Intros x y z Hz Hxy.
Elim (Zle_lt_or_eq `x*z` `y*z` Hxy).
Intros; Apply Zlt_le_weak.
Apply Zlt_Zmult_right2 with z; Trivial.
Intros; Apply Zle_refl.
Apply Zmult_reg_right with z.
  Intro. Rewrite H0 in Hz. Contradiction (Zgt_antirefl `0`).
Assumption.
Qed.
V7only [Notation Zle_Zmult_right2 := Zle_mult_simpl.
(* Zle_Zmult_right2 :  (x,y,z:Z)`z>0` -> `x*z <= y*z` -> `x <= y`. *)
].

V7only [ (* Relevance confirmed from Zextensions *) ].
Lemma Zmult_lt_0_le_reg_r: (x,y,z:Z)`0 <z`->`x*z <= y*z`->`x <= y`.
Intros ; Apply Zle_mult_simpl with z.
Try Apply Zlt_gt; Assumption.
Assumption.
Qed.

V7only [Unset Implicit Arguments.].

Lemma Zge_mult_simpl : (a,b,c:Z) `c>0`->`a*c>=b*c`->`a>=b`.
Intros a b c H1 H2; Apply Zle_ge; Apply Zle_mult_simpl with c; Trivial.
Apply Zge_le; Trivial.
Qed.

Lemma Zgt_mult_simpl : (a,b,c:Z) `c>0`->`a*c>b*c`->`a>b`.
Intros a b c H1 H2; Apply Zlt_gt; Apply Zlt_Zmult_right2 with c; Trivial.
Apply Zgt_lt; Trivial.
Qed.


(** Compatibility of multiplication by a positive wrt to being positive *)

Theorem Zle_ZERO_mult : (x,y:Z) `0<=x` -> `0<=y` -> `0<=x*y`.
Proof.
Intros x y; Case x.
Intros; Rewrite Zero_mult_left; Trivial.
Intros p H1; Unfold Zle.
  Pattern 2 ZERO ; Rewrite <- (Zero_mult_right (POS p)).
  Rewrite  Zcompare_Zmult_compatible; Trivial.
Intros p H1 H2; Absurd (Zgt ZERO (NEG p)); Trivial.
Unfold Zgt; Simpl; Auto with zarith.
Qed.

Lemma Zgt_ZERO_mult: (a,b:Z) `a>0`->`b>0`->`a*b>0`.
Proof.
Intros x y; Case x.
Intros H; Discriminate H.
Intros p H1; Unfold Zgt; 
Pattern 2 ZERO ; Rewrite <- (Zero_mult_right (POS p)).
  Rewrite  Zcompare_Zmult_compatible; Trivial.
Intros p H; Discriminate H.
Qed.

V7only [ (* Relevance confirmed from Zextensions *) ].
Lemma Zmult_lt_O_compat : (a, b : Z) `0<a` -> `0<b` -> `0<a*b`.
Intros a b apos bpos.
Apply Zgt_lt.
Apply Zgt_ZERO_mult; Try Apply Zlt_gt; Assumption.
Qed.

Theorem Zle_mult: (x,y:Z) `x>0` -> `0<=y` -> `0<=(Zmult y x)`.
Proof.
Intros x y H1 H2; Apply Zle_ZERO_mult; Trivial.
Apply Zlt_le_weak; Apply Zgt_lt; Trivial.
Qed.

(** Simplification of multiplication by a positive wrt to being positive *)

Theorem Zmult_le: (x,y:Z) `x>0` -> `0<=(Zmult y x)` -> `0<=y`.
Proof.
Intros x y; Case x; [
  Simpl; Unfold Zgt ; Simpl; Intros H; Discriminate H
| Intros p H1; Unfold Zle; Rewrite -> Zmult_sym;
  Pattern 1 ZERO ; Rewrite <- (Zero_mult_right (POS p));
  Rewrite  Zcompare_Zmult_compatible; Auto with arith
| Intros p; Unfold Zgt ; Simpl; Intros H; Discriminate H].
Qed.

Theorem Zmult_lt: (x,y:Z) `x>0` -> `0<y*x` -> `0<y`.
Proof.
Intros x y; Case x; [
  Simpl; Unfold Zgt ; Simpl; Intros H; Discriminate H
| Intros p H1; Unfold Zlt; Rewrite -> Zmult_sym;
  Pattern 1 ZERO ; Rewrite <- (Zero_mult_right (POS p));
  Rewrite  Zcompare_Zmult_compatible; Auto with arith
| Intros p; Unfold Zgt ; Simpl; Intros H; Discriminate H].
Qed.

V7only [ (* Relevance confirmed from Zextensions *) ].
Lemma Zmult_lt_0_reg_r : (x,y:Z)`0 < x`->`0 < y*x`->`0 < y`.
Proof.
Intros ; EApply Zmult_lt with x ; Try Apply Zlt_gt; Assumption.
Qed.

Theorem Zmult_gt: (x,y:Z) `x>0` -> `x*y>0` -> `y>0`.
Proof.
Intros x y; Case x.
 Intros H; Discriminate H.
 Intros p H1; Unfold Zgt.
 Pattern 1 ZERO ; Rewrite <- (Zero_mult_right (POS p)).
 Rewrite  Zcompare_Zmult_compatible; Trivial.
Intros p H; Discriminate H.
Qed.

(** Simplification of square wrt order *)

Lemma Zgt_square_simpl: (x, y : Z) `x>=0` -> `y>=0` -> `x*x>y*y` -> (Zgt x y).
Proof.
Intros x y H0 H1 H2.
Case (dec_Zlt y x).
Intro; Apply Zlt_gt; Trivial.
Intros H3; Cut (Zge y x).
Intros H.
Elim Zgt_not_le with 1 := H2.
Apply Zge_le.
Apply Zge_Zmult_pos_compat; Auto.
Apply not_Zlt; Trivial.
Qed.

Lemma Zlt_square_simpl: (x,y:Z) `0<=x` -> `0<=y` -> `y*y<x*x` -> `y<x`.
Proof.
Intros x y H0 H1 H2.
Apply Zgt_lt.
Apply Zgt_square_simpl; Try Apply Zle_ge; Try Apply Zlt_gt; Assumption.
Qed.

(** Equivalence between inequalities (used in contrib/graph) *)

Lemma Zle_plus_swap : (x,y,z:Z) `x+z<=y` <-> `x<=y-z`.
Proof.
    Intros. Split. Intro. Rewrite <- (Zero_right x). Rewrite <- (Zplus_inverse_r z).
    Rewrite Zplus_assoc_l. Exact (Zle_reg_r ? ? ? H).
    Intro. Rewrite <- (Zero_right y). Rewrite <- (Zplus_inverse_l z). Rewrite Zplus_assoc_l.
    Apply Zle_reg_r. Assumption.
Qed.

Lemma Zge_iff_le : (x,y:Z) `x>=y` <-> `y<=x`.
Proof.
    Intros. Split. Intro. Apply Zge_le. Assumption.
    Intro. Apply Zle_ge. Assumption.
Qed.

Lemma Zlt_plus_swap : (x,y,z:Z) `x+z<y` <-> `x<y-z`.
Proof.
    Intros. Split. Intro. Unfold Zminus. Rewrite Zplus_sym. Rewrite <- (Zero_left x).
    Rewrite <- (Zplus_inverse_l z). Rewrite Zplus_assoc_r. Apply Zlt_reg_l. Rewrite Zplus_sym.
    Assumption.
    Intro. Rewrite Zplus_sym. Rewrite <- (Zero_left y). Rewrite <- (Zplus_inverse_r z).
    Rewrite Zplus_assoc_r. Apply Zlt_reg_l. Rewrite Zplus_sym. Assumption.
Qed.

Lemma Zgt_iff_lt : (x,y:Z) `x>y` <-> `y<x`.
Proof.
    Intros. Split. Intro. Apply Zgt_lt. Assumption.
    Intro. Apply Zlt_gt. Assumption.
Qed.

Lemma Zeq_plus_swap : (x,y,z:Z)`x+z=y` <-> `x=y-z`.
Proof.
Intros. Split. Intro. Apply Zplus_minus. Symmetry. Rewrite Zplus_sym. 
  Assumption.
Intro. Rewrite H. Unfold Zminus. Rewrite Zplus_assoc_r. 
  Rewrite Zplus_inverse_l. Apply Zero_right.
Qed.

Lemma Zlt_minus : (n,m:Z)`0<m`->`n-m<n`.
Proof.
Intros n m H; Apply Zsimpl_lt_plus_l with p:=m; Rewrite Zle_plus_minus;
Pattern 1 n ;Rewrite <- (Zero_right n); Rewrite (Zplus_sym m n);
Apply Zlt_reg_l; Assumption.
Qed.

Lemma Zlt_O_minus_lt : (n,m:Z)`0<n-m`->`m<n`.
Proof.
Intros n m H; Apply Zsimpl_lt_plus_l with p:=(Zopp m); Rewrite Zplus_inverse_l;
Rewrite Zplus_sym;Exact H.
Qed.

(** Reverting [x ?= y] to trichotomy *)

Lemma rename : (A:Set)(P:A->Prop)(x:A) ((y:A)(x=y)->(P y)) -> (P x).
Proof.
Auto with arith. 
Qed.

Theorem Zcompare_elim :
  (c1,c2,c3:Prop)(x,y:Z)
    ((x=y) -> c1) ->(`x<y` -> c2) ->(`x>y`-> c3)
     -> Cases (Zcompare x y) of EGAL => c1 | INFERIEUR => c2 | SUPERIEUR => c3 end.
Proof.
Intros.
Apply rename with x:=(Zcompare x y); Intro r; Elim r;
[ Intro; Apply H; Apply (Zcompare_EGAL_eq x y); Assumption
| Unfold Zlt in H0; Assumption
| Unfold Zgt in H1; Assumption ].
Qed.

Lemma Zcompare_eq_case : 
  (c1,c2,c3:Prop)(x,y:Z) c1 -> x=y ->
  Cases (Zcompare x y) of EGAL => c1 | INFERIEUR => c2 | SUPERIEUR => c3 end.
Proof.
Intros.
Rewrite H0; Rewrite (Zcompare_x_x).
Assumption.
Qed.

(** Decompose an egality between two [?=] relations into 3 implications *)

Theorem Zcompare_egal_dec :
   (x1,y1,x2,y2:Z)
    (`x1<y1`->`x2<y2`)
     ->((Zcompare x1 y1)=EGAL -> (Zcompare x2 y2)=EGAL)
        ->(`x1>y1`->`x2>y2`)->(Zcompare x1 y1)=(Zcompare x2 y2).
Proof.
Intros x1 y1 x2 y2.
Unfold Zgt; Unfold Zlt;
Case (Zcompare x1 y1); Case (Zcompare x2 y2); Auto with arith; Symmetry; Auto with arith.
Qed.

(** Relating [x ?= y] to [Zle], [Zlt], [Zge] or [Zgt] *)

Lemma Zle_Zcompare :
  (x,y:Z)`x<=y` ->
  Cases (Zcompare x y) of EGAL => True | INFERIEUR => True | SUPERIEUR => False end.
Proof.
Intros x y; Unfold Zle; Elim (Zcompare x y); Auto with arith.
Qed.

Lemma Zlt_Zcompare :
  (x,y:Z)`x<y`  ->
  Cases (Zcompare x y) of EGAL => False | INFERIEUR => True | SUPERIEUR => False end.
Proof.
Intros x y; Unfold Zlt; Elim (Zcompare x y); Intros; Discriminate Orelse Trivial with arith.
Qed.

Lemma Zge_Zcompare :
  (x,y:Z)`x>=y`->
  Cases (Zcompare x y) of EGAL => True | INFERIEUR => False | SUPERIEUR => True end.
Proof.
Intros x y; Unfold Zge; Elim (Zcompare x y); Auto with arith. 
Qed.

Lemma Zgt_Zcompare :
  (x,y:Z)`x>y` ->
  Cases (Zcompare x y) of EGAL => False | INFERIEUR => False | SUPERIEUR => True end.
Proof.
Intros x y; Unfold Zgt; Elim (Zcompare x y); Intros; Discriminate Orelse Trivial with arith.
Qed.
