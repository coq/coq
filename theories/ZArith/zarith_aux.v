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

V7only [Import nat_scope.].
Open Local Scope Z_scope.

(**********************************************************************)
(** Properties of the order relations on binary integers *)

(** Trichotomy *)

Theorem Ztrichotomy_inf : (m,n:Z) {Zlt m n} + {m=n} + {Zgt m n}.
Proof.
Unfold Zgt Zlt; Intros m n; Assert H:=(refl_equal ? (Zcompare m n)).
  LetTac x := (Zcompare m n) in 2 H Goal.
  NewDestruct x; 
    [Left; Right;Rewrite Zcompare_EGAL_eq with 1:=H 
    | Left; Left
    | Right ]; Reflexivity.
Qed.

Theorem Ztrichotomy : (m,n:Z) (Zlt m n) \/ m=n \/ (Zgt m n).
Proof.
  Intros m n; NewDestruct (Ztrichotomy_inf m n) as [[Hlt|Heq]|Hgt];
    [Left | Right; Left |Right; Right]; Assumption.
Qed.

(** Relating strict and large orders *)

Lemma Zgt_lt : (m,n:Z) (Zgt m n) -> (Zlt n m).
Proof.
Unfold Zgt Zlt ;Intros m n H; Elim (Zcompare_ANTISYM m n); Auto with arith.
Qed.

Lemma Zlt_gt : (m,n:Z) (Zlt m n) -> (Zgt n m).
Proof.
Unfold Zgt Zlt ;Intros m n H; Elim (Zcompare_ANTISYM n m); Auto with arith.
Qed.

Lemma Zge_le : (m,n:Z) (Zge m n) -> (Zle n m).
Proof.
Intros m n; Change ~(Zlt m n)-> ~(Zgt n m);
Unfold not; Intros H1 H2; Apply H1; Apply Zgt_lt; Assumption.
Qed.

Lemma Zle_ge : (m,n:Z) (Zle m n) -> (Zge n m).
Proof.
Intros m n; Change ~(Zgt m n)-> ~(Zlt n m);
Unfold not; Intros H1 H2; Apply H1; Apply Zlt_gt; Assumption.
Qed.

Lemma Zle_not_gt     : (n,m:Z)(Zle n m) -> ~(Zgt n m).
Proof.
Trivial.
Qed.

Lemma Znot_gt_le     : (n,m:Z)~(Zgt n m) -> (Zle n m).
Proof.
Trivial.
Qed.

Lemma Zgt_not_le     : (n,m:Z)(Zgt n m) -> ~(Zle n m).
Proof.
Intros n m H1 H2; Apply H2; Assumption.
Qed.

Lemma Zle_not_lt : (n,m:Z)(Zle n m) -> ~(Zlt m n).
Proof.
Intros n m H1 H2.
Assert H3:=(Zlt_gt ? ? H2).
Apply Zle_not_gt with n m; Assumption.
Qed.

Lemma Zlt_not_le : (n,m:Z)(Zlt n m) -> ~(Zle m n).
Proof.
Intros n m H1 H2.
Apply Zle_not_lt with m n; Assumption.
Qed.

(** Reflexivity *)

Lemma Zle_n : (n:Z) (Zle n n).
Proof.
Intros n; Unfold Zle; Rewrite (Zcompare_x_x n); Discriminate.
Qed. 

(** Antisymmetry *)

Lemma Zle_antisym : (n,m:Z)(Zle n m)->(Zle m n)->n=m.
Proof.
Intros n m H1 H2; NewDestruct (Ztrichotomy n m) as [Hlt|[Heq|Hgt]]. 
  Absurd (Zgt m n); [ Apply Zle_not_gt | Apply Zlt_gt]; Assumption.
  Assumption.
  Absurd (Zgt n m); [ Apply Zle_not_gt | Idtac]; Assumption.
Qed.

(** Asymmetry *)

Lemma Zgt_not_sym    : (n,m:Z)(Zgt n m) -> ~(Zgt m n).
Proof.
Unfold Zgt ;Intros n m H; Elim (Zcompare_ANTISYM n m); Intros H1 H2;
Rewrite -> H1; [ Discriminate | Assumption ].
Qed.

Lemma Zlt_not_sym : (n,m:Z)(Zlt n m) -> ~(Zlt m n).
Proof.
Intros n m H H1;
Assert H2:(Zgt m n). Apply Zlt_gt; Assumption.
Assert H3: (Zgt n m). Apply Zlt_gt; Assumption.
Apply Zgt_not_sym with m n; Assumption.
Qed.

(** Irreflexivity *)

Lemma Zgt_antirefl   : (n:Z)~(Zgt n n).
Proof.
Intros n H; Apply (Zgt_not_sym n n H H).
Qed.

Lemma Zlt_n_n : (n:Z)~(Zlt n n).
Proof.
Intros n H; Apply (Zlt_not_sym n n H H).
Qed.

(** Large = strict or equal *)

Lemma Zle_lt_or_eq : (n,m:Z)(Zle n m)->((Zlt n m) \/ n=m).
Proof.
Intros n m H; NewDestruct (Ztrichotomy n m) as [Hlt|[Heq|Hgt]]; [
  Left; Assumption
| Right; Assumption
| Absurd (Zgt n m); [Apply Zle_not_gt|Idtac]; Assumption ].
Qed.

Lemma Zlt_le_weak : (n,m:Z)(Zlt n m)->(Zle n m).
Proof.
Intros n m Hlt; Apply Znot_gt_le; Apply Zgt_not_sym; Apply Zlt_gt; Assumption.
Qed.

(** Dichotomy *)

Lemma Zle_or_lt : (n,m:Z)(Zle n m)\/(Zlt m n).
Proof.
Intros n m; NewDestruct (Ztrichotomy n m) as [Hlt|[Heq|Hgt]]; [
  Left; Apply Znot_gt_le; Intro Hgt; Assert Hgt':=(Zlt_gt ? ? Hlt);
     Apply Zgt_not_sym with m n; Assumption
| Left; Rewrite Heq; Apply Zle_n
| Right; Apply Zgt_lt; Assumption ].
Qed.

(** Transitivity of strict orders *)

Lemma Zgt_trans      : (n,m,p:Z)(Zgt n m)->(Zgt m p)->(Zgt n p).
Proof.
Exact Zcompare_trans_SUPERIEUR.
Qed.

Lemma Zlt_trans : (n,m,p:Z)(Zlt n m)->(Zlt m p)->(Zlt n p).
Proof.
Intros n m p H1 H2; Apply Zgt_lt; Apply Zgt_trans with m:= m; 
Apply Zlt_gt; Assumption.
Qed.

(** Mixed transitivity *)

Lemma Zle_gt_trans : (n,m,p:Z)(Zle m n)->(Zgt m p)->(Zgt n p).
Proof.
Intros n m p H1 H2; NewDestruct (Zle_lt_or_eq m n H1) as [Hlt|Heq]; [
  Apply Zgt_trans with m; [Apply Zlt_gt; Assumption | Assumption ]
| Rewrite <- Heq; Assumption ].
Qed.

Lemma Zgt_le_trans : (n,m,p:Z)(Zgt n m)->(Zle p m)->(Zgt n p).
Proof.
Intros n m p H1 H2; NewDestruct (Zle_lt_or_eq p m H2) as [Hlt|Heq]; [
  Apply Zgt_trans with m; [Assumption|Apply Zlt_gt; Assumption]
| Rewrite Heq; Assumption ].
Qed.

Lemma Zlt_le_trans : (n,m,p:Z)(Zlt n m)->(Zle m p)->(Zlt n p).
Intros n m p H1 H2;Apply Zgt_lt;Apply Zle_gt_trans with m:=m;
  [ Assumption | Apply Zlt_gt;Assumption ].
Qed.

Lemma Zle_lt_trans : (n,m,p:Z)(Zle n m)->(Zlt m p)->(Zlt n p).
Proof.
Intros n m p H1 H2;Apply Zgt_lt;Apply Zgt_le_trans with m:=m; 
  [ Apply Zlt_gt;Assumption | Assumption ].
Qed.

(** Transitivity of large orders *)

Lemma Zle_trans : (n,m,p:Z)(Zle n m)->(Zle m p)->(Zle n p).
Proof.
Intros n m p H1 H2; Apply Znot_gt_le.
Intro Hgt; Apply Zle_not_gt with n m. Assumption.
Exact (Zgt_le_trans n p m Hgt H2).
Qed.

Lemma Zge_trans : (n, m, p : Z) (Zge n m) -> (Zge m p) -> (Zge n p).
Proof.
Intros n m p H1 H2.
Apply Zle_ge.
Apply Zle_trans with m; Apply Zge_le; Trivial.
Qed.

(** Compatibility of operations wrt to order *)

Lemma Zgt_S_n        : (n,p:Z)(Zgt (Zs p) (Zs n))->(Zgt p n).
Proof.
Unfold Zs Zgt;Intros n p;Do 2 Rewrite -> [m:Z](Zplus_sym m (POS xH));
Rewrite -> (Zcompare_Zplus_compatible p n (POS xH));Trivial with arith.
Qed.

Lemma Zle_S_n     : (n,m:Z) (Zle (Zs m) (Zs n)) -> (Zle m n).
Proof.
Unfold Zle not ;Intros m n H1 H2;Apply H1;
Unfold Zs ;Do 2 Rewrite <- (Zplus_sym (POS xH));
Rewrite -> (Zcompare_Zplus_compatible n m (POS xH));Assumption.
Qed.

Lemma Zle_n_S : (n,m:Z) (Zle m n) -> (Zle (Zs m) (Zs n)).
Proof.
Unfold Zle not ;Intros m n H1 H2; Apply H1; 
Rewrite <- (Zcompare_Zplus_compatible n m (POS xH));
Do 2 Rewrite (Zplus_sym (POS xH)); Exact H2.
Qed.

Lemma Zgt_n_S : (n,m:Z)(Zgt m n) -> (Zgt (Zs m) (Zs n)).
Proof.
Unfold Zgt; Intros n m H; Rewrite Zcompare_n_S; Auto with arith.
Qed.

Lemma Zsimpl_gt_plus_l 
	: (n,m,p:Z)(Zgt (Zplus p n) (Zplus p m))->(Zgt n m).
Proof.
Unfold Zgt; Intros n m p H; 
	Rewrite <- (Zcompare_Zplus_compatible n m p); Assumption.
Qed.

Lemma Zsimpl_gt_plus_r
	: (n,m,p:Z)(Zgt (Zplus n p) (Zplus m p))->(Zgt n m).
Proof.
Intros n m p H; Apply Zsimpl_gt_plus_l with p.
Rewrite (Zplus_sym p n); Rewrite (Zplus_sym p m); Trivial.
Qed.

Lemma Zgt_reg_l      
	: (n,m,p:Z)(Zgt n m)->(Zgt (Zplus p n) (Zplus p m)).
Proof.
Unfold Zgt; Intros n m p H; Rewrite (Zcompare_Zplus_compatible n m p); 
Assumption.
Qed.

Lemma Zgt_reg_r : (n,m,p:Z)(Zgt n m)->(Zgt (Zplus n p) (Zplus m p)).
Proof.
Intros n m p H; Rewrite (Zplus_sym n p); Rewrite (Zplus_sym m p); Apply Zgt_reg_l; Trivial.
Qed.

(** Order, predecessor and successor *)

Lemma Zgt_Sn_n : (n:Z)(Zgt (Zs n) n).
Proof.
Exact Zcompare_Zs_SUPERIEUR.
Qed.

Lemma Zgt_le_S       : (n,p:Z)(Zgt p n)->(Zle (Zs n) p).
Proof.
Unfold Zgt Zle; Intros n p H; Elim (Zcompare_et_un p n); Intros H1 H2;
Unfold not ;Intros H3; Unfold not in H1; Apply H1; [
  Assumption
| Elim (Zcompare_ANTISYM (Zplus n (POS xH)) p);Intros H4 H5;Apply H4;Exact H3].
Qed.

Lemma Zgt_S_le       : (n,p:Z)(Zgt (Zs p) n)->(Zle n p).
Proof.
Intros n p H;Apply Zle_S_n; Apply Zgt_le_S; Assumption.
Qed.

Lemma Zle_S_gt : (n,m:Z) (Zle (Zs n) m) -> (Zgt m n).
Proof.
Intros n m H;Apply Zle_gt_trans with m:=(Zs n);
  [ Assumption | Apply Zgt_Sn_n ].
Qed.

Lemma Zle_gt_S       : (n,p:Z)(Zle n p)->(Zgt (Zs p) n).
Proof.
Intros n p H; Apply Zgt_le_trans with p.
  Apply Zgt_Sn_n.
  Assumption.
Qed.

Lemma Zgt_pred       
	: (n,p:Z)(Zgt p (Zs n))->(Zgt (Zpred p) n).
Proof.
Unfold Zgt Zs Zpred ;Intros n p H; 
Rewrite <- [x,y:Z](Zcompare_Zplus_compatible x y (POS xH));
Rewrite (Zplus_sym p); Rewrite Zplus_assoc; Rewrite [x:Z](Zplus_sym x n);
Simpl; Assumption.
Qed.

Lemma Zlt_ZERO_pred_le_ZERO : (n:Z) (Zlt ZERO n) -> (Zle ZERO (Zpred n)).
Intros x H.
Rewrite (Zs_pred x) in H.
Apply Zgt_S_le.
Apply Zlt_gt.
Assumption.
Qed.

(** Special cases of ordered integers *)

Lemma Zle_n_Sn : (n:Z)(Zle n (Zs n)).
Proof.
Intros n; Apply Zgt_S_le;Apply Zgt_trans with m:=(Zs n) ;Apply Zgt_Sn_n.
Qed.

Lemma Zle_pred_n : (n:Z)(Zle (Zpred n) n).
Proof.
Intros n;Pattern 2 n ;Rewrite Zs_pred; Apply Zle_n_Sn.
Qed.

Lemma POS_gt_ZERO : (p:positive) (Zgt (POS p) ZERO).
Unfold Zgt; Trivial.
Qed.

  (* weaker but useful (in [Zpower] for instance) *)
Lemma ZERO_le_POS : (p:positive) (Zle ZERO (POS p)).
Intro; Unfold Zle; Discriminate.
Qed.

Lemma NEG_lt_ZERO : (p:positive)(Zlt (NEG p) ZERO).
Unfold Zlt; Trivial.
Qed.

(** Weakening equality within order *)
 
Lemma Zlt_not_eq : (x,y:Z)(Zlt x y) -> ~x=y.
Proof.
Unfold not; Intros x y H H0.
Rewrite H0 in H.
Apply (Zlt_n_n ? H).
Qed.

Lemma Zle_refl : (n,m:Z) n=m -> (Zle n m).
Proof.
Intros; Rewrite H; Apply Zle_n.
Qed.

(** Transitivity using successor *)

Lemma Zgt_trans_S  : (n,m,p:Z)(Zgt (Zs n) m)->(Zgt m p)->(Zgt n p).
Proof.
Intros n m p H1 H2;Apply Zle_gt_trans with m:=m;
  [ Apply Zgt_S_le; Assumption | Assumption ].
Qed.

Lemma Zgt_S        : (n,m:Z)(Zgt (Zs n) m)->((Zgt n m)\/(m=n)).
Proof.
Intros n m H.
Assert Hle : (Zle m n).
  Apply Zgt_S_le; Assumption.
NewDestruct (Zle_lt_or_eq ? ? Hle) as [Hlt|Heq].
  Left; Apply Zlt_gt; Assumption.  
  Right; Assumption.
Qed.

Hints Resolve Zle_n Zle_n_Sn Zle_trans Zle_n_S : zarith.
Hints Immediate Zle_refl : zarith.

Lemma Zle_trans_S : (n,m:Z)(Zle (Zs n) m)->(Zle n m).
Proof.
Intros n m H;Apply Zle_trans with m:=(Zs n); [ Apply Zle_n_Sn | Assumption ].
Qed.

Lemma Zle_Sn_n : (n:Z)~(Zle (Zs n) n).
Proof.
Intros n; Apply Zgt_not_le; Apply Zgt_Sn_n.
Qed.

Lemma Zlt_n_Sn : (n:Z)(Zlt n (Zs n)).
Proof.
Intro n; Apply Zgt_lt; Apply Zgt_Sn_n.
Qed.

Lemma Zlt_S : (n,m:Z)(Zlt n m)->(Zlt n (Zs m)).
Intros n m H;Apply Zgt_lt; Apply Zgt_trans with m:=m; [
  Apply Zgt_Sn_n
| Apply Zlt_gt; Assumption ].
Qed.

Lemma Zlt_n_S : (n,m:Z)(Zlt n m)->(Zlt (Zs n) (Zs m)).
Proof.
Intros n m H;Apply Zgt_lt;Apply Zgt_n_S;Apply Zlt_gt; Assumption.
Qed.

Lemma Zlt_S_n : (n,m:Z)(Zlt (Zs n) (Zs m))->(Zlt n m).
Proof.
Intros n m H;Apply Zgt_lt;Apply Zgt_S_n;Apply Zlt_gt; Assumption.
Qed.

Lemma Zlt_pred : (n,p:Z)(Zlt (Zs n) p)->(Zlt n (Zpred p)).
Proof.
Intros n p H;Apply Zlt_S_n; Rewrite <- Zs_pred; Assumption.
Qed.

Lemma Zlt_pred_n_n : (n:Z)(Zlt (Zpred n) n).
Proof.
Intros n; Apply Zlt_S_n; Rewrite <- Zs_pred; Apply Zlt_n_Sn.
Qed.
 
Lemma Zlt_le_S : (n,p:Z)(Zlt n p)->(Zle (Zs n) p).
Proof.
Intros n p H; Apply Zgt_le_S; Apply Zlt_gt; Assumption.
Qed.

Lemma Zlt_n_Sm_le : (n,m:Z)(Zlt n (Zs m))->(Zle n m).
Proof.
Intros n m H; Apply Zgt_S_le; Apply Zlt_gt; Assumption.
Qed.

Lemma Zle_lt_n_Sm : (n,m:Z)(Zle n m)->(Zlt n (Zs m)).
Proof.
Intros n m H; Apply Zgt_lt; Apply Zle_gt_S; Assumption.
Qed.

Lemma Zle_le_S : (x,y:Z)(Zle x y)->(Zle x (Zs y)).
Proof.
Intros.
Apply Zle_trans with y; Trivial with zarith.
Qed.

Hints Resolve Zle_le_S : zarith.

(** Simplification and compatibility *)

Lemma Zsimpl_le_plus_l : (p,n,m:Z)(Zle (Zplus p n) (Zplus p m))->(Zle n m).
Proof.
Intros p n m; Unfold Zle not ;Intros H1 H2;Apply H1; 
Rewrite (Zcompare_Zplus_compatible n m p); Assumption.
Qed.
 
Lemma Zsimpl_le_plus_r : (p,n,m:Z)(Zle (Zplus n p) (Zplus m p))->(Zle n m).
Proof.
Intros p n m H; Apply Zsimpl_le_plus_l with p.
Rewrite (Zplus_sym p n); Rewrite (Zplus_sym p m); Trivial.
Qed.

Lemma Zle_reg_l : (n,m,p:Z)(Zle n m)->(Zle (Zplus p n) (Zplus p m)).
Proof.
Intros n m p; Unfold Zle not ;Intros H1 H2;Apply H1; 
Rewrite <- (Zcompare_Zplus_compatible n m p); Assumption.
Qed.

Lemma Zle_reg_r : (n,m,p:Z) (Zle n m)->(Zle (Zplus n p) (Zplus m p)).
Proof.
Intros a b c;Do 2 Rewrite [n:Z](Zplus_sym n c); Exact (Zle_reg_l a b c).
Qed.

Lemma Zle_plus_plus : 
 (n,m,p,q:Z) (Zle n m)->(Zle p q)->(Zle (Zplus n p) (Zplus m q)).
Proof.
Intros n m p q; Intros H1 H2;Apply Zle_trans with m:=(Zplus n q); [
  Apply Zle_reg_l;Assumption | Apply Zle_reg_r;Assumption ].
Qed.

Lemma Zsimpl_lt_plus_l 
	: (n,m,p:Z)(Zlt (Zplus p n) (Zplus p m))->(Zlt n m).
Proof.
Unfold Zlt ;Intros n m p; 
	Rewrite Zcompare_Zplus_compatible;Trivial with arith.
Qed.
 
Lemma Zsimpl_lt_plus_r
	: (n,m,p:Z)(Zlt (Zplus n p) (Zplus m p))->(Zlt n m).
Proof.
Intros n m p H; Apply Zsimpl_lt_plus_l with p.
Rewrite (Zplus_sym p n); Rewrite (Zplus_sym p m); Trivial.
Qed.
 
Lemma Zlt_reg_l : (n,m,p:Z)(Zlt n m)->(Zlt (Zplus p n) (Zplus p m)).
Proof.
Unfold Zlt ;Intros n m p; Rewrite Zcompare_Zplus_compatible;Trivial with arith.
Qed.

Lemma Zlt_reg_r : (n,m,p:Z)(Zlt n m)->(Zlt (Zplus n p) (Zplus m p)).
Proof.
Intros n m p H; Rewrite (Zplus_sym n p); Rewrite (Zplus_sym m p); Apply Zlt_reg_l; Trivial.
Qed.

Lemma Zlt_le_reg :
 (a,b,c,d:Z) (Zlt a b)->(Zle c d)->(Zlt (Zplus a c) (Zplus b d)).
Proof.
Intros a b c d H0 H1.
Apply Zlt_le_trans with (Zplus b c).
Apply  Zlt_reg_r; Trivial.
Apply  Zle_reg_l; Trivial.
Qed.

Lemma Zle_lt_reg :
 (a,b,c,d:Z) (Zle a b)->(Zlt c d)->(Zlt (Zplus a c) (Zplus b d)).
Proof.
Intros a b c d H0 H1.
Apply Zle_lt_trans with (Zplus b c).
Apply  Zle_reg_r; Trivial.
Apply  Zlt_reg_l; Trivial.
Qed.

(** Equivalence between inequalities (used in contrib/graph) *)

Lemma Zle_plus_swap : (x,y,z:Z) (Zle (Zplus x z) y) <-> (Zle x (Zminus y z)).
Proof.
    Intros. Split. Intro. Rewrite <- (Zero_right x). Rewrite <- (Zplus_inverse_r z).
    Rewrite Zplus_assoc_l. Exact (Zle_reg_r ? ? ? H).
    Intro. Rewrite <- (Zero_right y). Rewrite <- (Zplus_inverse_l z). Rewrite Zplus_assoc_l.
    Apply Zle_reg_r. Assumption.
Qed.

Lemma Zge_iff_le : (x,y:Z) (Zge x y) <-> (Zle y x).
Proof.
    Intros. Split. Intro. Apply Zge_le. Assumption.
    Intro. Apply Zle_ge. Assumption.
Qed.

Lemma Zlt_plus_swap : (x,y,z:Z) (Zlt (Zplus x z) y) <-> (Zlt x (Zminus y z)).
Proof.
    Intros. Split. Intro. Unfold Zminus. Rewrite Zplus_sym. Rewrite <- (Zero_left x).
    Rewrite <- (Zplus_inverse_l z). Rewrite Zplus_assoc_r. Apply Zlt_reg_l. Rewrite Zplus_sym.
    Assumption.
    Intro. Rewrite Zplus_sym. Rewrite <- (Zero_left y). Rewrite <- (Zplus_inverse_r z).
    Rewrite Zplus_assoc_r. Apply Zlt_reg_l. Rewrite Zplus_sym. Assumption.
Qed.

Lemma Zgt_iff_lt : (x,y:Z) (Zgt x y) <-> (Zlt y x).
Proof.
    Intros. Split. Intro. Apply Zgt_lt. Assumption.
    Intro. Apply Zlt_gt. Assumption.
Qed.

Lemma Zeq_plus_swap : (x,y,z:Z) (Zplus x z)=y <-> x=(Zminus y z).
Proof.
    Intros. Split. Intro. Rewrite <- H. Unfold Zminus. Rewrite Zplus_assoc_r.
    Rewrite Zplus_inverse_r. Apply sym_eq. Apply Zero_right.
    Intro. Rewrite H. Unfold Zminus. Rewrite Zplus_assoc_r. Rewrite Zplus_inverse_l.
    Apply Zero_right.
Qed.

(** Reverting [x ?= y] to trichotomy *)

Lemma rename : (A:Set)(P:A->Prop)(x:A) ((y:A)(x=y)->(P y)) -> (P x).
Auto with arith. 
Qed.

Theorem Zcompare_elim :
  (c1,c2,c3:Prop)(x,y:Z)
    ((x=y) -> c1) ->((Zlt x y) -> c2) ->((Zgt x y)-> c3)
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
Intros.
Rewrite H0; Rewrite (Zcompare_x_x).
Assumption.
Qed.

(** Decompose an egality between two [?=] relations into 3 implications *)

Theorem Zcompare_egal_dec :
   (x1,y1,x2,y2:Z)
    ((Zlt x1 y1)->(Zlt x2 y2))
     ->((Zcompare x1 y1)=EGAL -> (Zcompare x2 y2)=EGAL)
        ->((Zgt x1 y1)->(Zgt x2 y2))->(Zcompare x1 y1)=(Zcompare x2 y2).
Intros x1 y1 x2 y2.
Unfold Zgt; Unfold Zlt;
Case (Zcompare x1 y1); Case (Zcompare x2 y2); Auto with arith; Symmetry; Auto with arith.
Qed.

(** Relating [x ?= y] to [Zle], [Zlt], [Zge] or [Zgt] *)

Lemma Zle_Zcompare :
  (x,y:Z)(Zle x y) ->
  Cases (Zcompare x y) of EGAL => True | INFERIEUR => True | SUPERIEUR => False end.
Intros x y; Unfold Zle; Elim (Zcompare x y); Auto with arith.
Qed.

Lemma Zlt_Zcompare :
  (x,y:Z)(Zlt x y)  ->
  Cases (Zcompare x y) of EGAL => False | INFERIEUR => True | SUPERIEUR => False end.
Intros x y; Unfold Zlt; Elim (Zcompare x y); Intros; Discriminate Orelse Trivial with arith.
Qed.

Lemma Zge_Zcompare :
  (x,y:Z)(Zge x y)->
  Cases (Zcompare x y) of EGAL => True | INFERIEUR => False | SUPERIEUR => True end.
Intros x y; Unfold Zge; Elim (Zcompare x y); Auto with arith. 
Qed.

Lemma Zgt_Zcompare :
  (x,y:Z)(Zgt x y) ->
  Cases (Zcompare x y) of EGAL => False | INFERIEUR => False | SUPERIEUR => True end.
Intros x y; Unfold Zgt; Elim (Zcompare x y); Intros; Discriminate Orelse Trivial with arith.
Qed.

(**********************************************************************)
(** Minimum on binary integer numbers *)

Definition Zmin := [n,m:Z]
 <Z>Cases (Zcompare n m) of
      EGAL      => n
    | INFERIEUR => n
    | SUPERIEUR => m
    end.

(** Properties of minimum on binary integer numbers *)

Lemma Zmin_SS : (n,m:Z)((Zs (Zmin n m))=(Zmin (Zs n) (Zs m))).
Proof.
Intros n m;Unfold Zmin; Rewrite (Zcompare_n_S n m);
(ElimCompare 'n 'm);Intros E;Rewrite E;Auto with arith.
Qed.

Lemma Zle_min_l : (n,m:Z)(Zle (Zmin n m) n).
Proof.
Intros n m;Unfold Zmin ; (ElimCompare 'n 'm);Intros E;Rewrite -> E;
  [ Apply Zle_n | Apply Zle_n | Apply Zlt_le_weak; Apply Zgt_lt;Exact E ].
Qed.

Lemma Zle_min_r : (n,m:Z)(Zle (Zmin n m) m).
Proof.
Intros n m;Unfold Zmin ; (ElimCompare 'n 'm);Intros E;Rewrite -> E;[
  Unfold Zle ;Rewrite -> E;Discriminate
| Unfold Zle ;Rewrite -> E;Discriminate
| Apply Zle_n ].
Qed.

Lemma Zmin_case : (n,m:Z)(P:Z->Set)(P n)->(P m)->(P (Zmin n m)).
Proof.
Intros n m P H1 H2; Unfold Zmin; Case (Zcompare n m);Auto with arith.
Qed.

Lemma Zmin_or : (n,m:Z)(Zmin n m)=n \/ (Zmin n m)=m.
Proof.
Unfold Zmin; Intros; Elim (Zcompare n m); Auto.
Qed.

Lemma Zmin_n_n : (n:Z) (Zmin n n)=n.
Proof.
Unfold Zmin; Intros; Elim (Zcompare n n); Auto.
Qed.

Lemma Zmin_plus :
 (x,y,n:Z)(Zmin (Zplus x n) (Zplus y n))=(Zplus (Zmin x y) n).
Proof.
Intros; Unfold Zmin.
Rewrite (Zplus_sym x n);
Rewrite (Zplus_sym y n);
Rewrite (Zcompare_Zplus_compatible x y n).
Case (Zcompare x y); Apply Zplus_sym.
Qed.

(**********************************************************************)
(* Absolute value on integers *)

Definition absolu [x:Z] : nat :=
  Cases x of
     ZERO   => O
  | (POS p) => (convert p)
  | (NEG p) => (convert p)
  end.

Definition Zabs [z:Z] : Z :=
  Cases z of 
     ZERO   => ZERO
  | (POS p) => (POS p)
  | (NEG p) => (POS p)
  end.

(** Properties of absolute value *)

Lemma Zabs_eq : (x:Z) (Zle ZERO x) -> (Zabs x)=x.
NewDestruct x; Auto with arith.
Compute; Intros; Absurd SUPERIEUR=SUPERIEUR; Trivial with arith.
Qed.

Lemma Zabs_non_eq : (x:Z) (Zle x ZERO) -> (Zabs x)=(Zopp x).
Proof.
NewDestruct x; Auto with arith.
Compute; Intros; Absurd SUPERIEUR=SUPERIEUR; Trivial with arith.
Qed.

Definition Zabs_dec : (x:Z){x=(Zabs x)}+{x=(Zopp (Zabs x))}.
Proof.
NewDestruct x;Auto with arith.
Defined.

Lemma Zabs_pos : (x:Z)(Zle ZERO (Zabs x)).
NewDestruct x;Auto with arith; Compute; Intros H;Inversion H.
Qed.

Lemma Zsgn_Zabs: (x:Z)(Zmult x (Zsgn x))=(Zabs x).
Proof.
NewDestruct x; Rewrite Zmult_sym; Auto with arith.
Qed.

Lemma Zabs_Zsgn: (x:Z)(Zmult (Zabs x) (Zsgn x))=x.
Proof.
NewDestruct x; Rewrite Zmult_sym; Auto with arith.
Qed.

(** absolute value in nat is compatible with order *)

Lemma absolu_lt : (x,y:Z) (Zle ZERO x)/\(Zlt x  y) -> (lt (absolu x) (absolu y)).
Proof.
Intros x y. Case x; Simpl. Case y; Simpl.

Intro. Absurd (Zlt ZERO ZERO). Compute. Intro H0. Discriminate H0. Intuition.
Intros. Elim (ZL4 p). Intros. Rewrite H0. Auto with arith.
Intros. Elim (ZL4 p). Intros. Rewrite H0. Auto with arith.

Case y; Simpl.
Intros. Absurd (Zlt (POS p) ZERO). Compute. Intro H0. Discriminate H0. Intuition.
Intros. Change (gt (convert p) (convert p0)).
Apply compare_convert_SUPERIEUR.
Elim H; Auto with arith. Intro. Exact (ZC2 p0 p).

Intros. Absurd (Zlt (POS p0) (NEG p)).
Compute. Intro H0. Discriminate H0. Intuition.

Intros. Absurd (Zle ZERO (NEG p)). Compute. Auto with arith. Intuition.
Qed.

Lemma Zlt_minus : (n,m:Z)(Zlt ZERO m)->(Zlt (Zminus n m) n).
Proof.
Intros n m H; Apply Zsimpl_lt_plus_l with p:=m; Rewrite Zle_plus_minus;
Pattern 1 n ;Rewrite <- (Zero_right n); Rewrite (Zplus_sym m n);
Apply Zlt_reg_l; Assumption.
Qed.

Lemma Zlt_O_minus_lt : (n,m:Z)(Zlt ZERO (Zminus n m))->(Zlt m n).
Proof.
Intros n m H; Apply Zsimpl_lt_plus_l with p:=(Zopp m); Rewrite Zplus_inverse_l;
Rewrite Zplus_sym;Exact H.
Qed.

(** Just for compatibility with previous versions. 
    Use [Zmult_plus_distr_r] and [Zmult_plus_distr_l] rather than
    their synomymous *)

Definition Zmult_Zplus_distr := Zmult_plus_distr_r.
Definition Zmult_plus_distr := Zmult_plus_distr_l.
