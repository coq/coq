(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*i $Id$ i*)

(** Binary Integers (Pierre Crégut (CNET, Lannion, France) *)

Require Arith.
Require Export fast_integer.

Meta Definition ElimCompare com1 com2:=
  Elim (Dcompare (Zcompare com1 com2)); [
         Idtac 
       | Intro hidden_auxiliary; Elim hidden_auxiliary; 
         Clear hidden_auxiliary ] .

(** Order relations *)
Definition Zlt := [x,y:Z](Zcompare x y) = INFERIEUR.
Definition Zgt := [x,y:Z](Zcompare x y) = SUPERIEUR.
Definition Zle := [x,y:Z]~(Zcompare x y) = SUPERIEUR.
Definition Zge := [x,y:Z]~(Zcompare x y) = INFERIEUR.

(** Sign function *)
Definition Zsgn [z:Z] : Z :=
  Cases z of 
     ZERO   => ZERO
  | (POS p) => (POS xH)
  | (NEG p) => (NEG xH)
  end.

(** Absolu function *)
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

(** Properties of absolu function *)

Lemma Zabs_eq : (x:Z) (Zle ZERO x) -> (Zabs x)=x.
NewDestruct x; Auto with arith.
Compute; Intros; Absurd SUPERIEUR=SUPERIEUR; Trivial with arith.
Save.

Lemma Zabs_non_eq : (x:Z) (Zle x ZERO) -> (Zabs x)=(Zopp x).
Proof.
NewDestruct x; Auto with arith.
Compute; Intros; Absurd SUPERIEUR=SUPERIEUR; Trivial with arith.
Save.

Lemma Zabs_dec : (x:Z){x=(Zabs x)}+{x=(Zopp (Zabs x))}.
Proof.
NewDestruct x;Auto with arith.
Save.

Lemma Zabs_pos : (x:Z)(Zle ZERO (Zabs x)).
NewDestruct x;Auto with arith; Compute; Intros H;Inversion H.
Save.

Lemma Zsgn_Zabs: (x:Z)(Zmult x (Zsgn x))=(Zabs x).
Proof.
Destruct x;Intros;Rewrite Zmult_sym;Auto with arith.
Save.

Lemma Zabs_Zsgn: (x:Z)(Zabs x)=(Zmult (Zsgn x) x).
Proof.
Destruct x;Intros;Auto with arith.
Qed.

(** From [nat] to [Z] *)
Definition inject_nat := 
  [x:nat]Cases x of
           O => ZERO
         | (S y) => (POS (anti_convert y))
         end.

(** Successor and Predecessor functions on [Z] *)
Definition Zs := [x:Z](Zplus x (POS xH)).
Definition Zpred := [x:Z](Zplus x (NEG xH)).

(* Properties of the order relation *)
Theorem Zgt_Sn_n : (n:Z)(Zgt (Zs n) n).

Intros n; Unfold Zgt Zs; Pattern 2 n; Rewrite <- (Zero_right n); 
Rewrite Zcompare_Zplus_compatible;Auto with arith.
Save.

(** Properties of the order *)
Theorem Zle_gt_trans : (n,m,p:Z)(Zle m n)->(Zgt m p)->(Zgt n p).

Unfold Zle Zgt; Intros n m p H1 H2; (ElimCompare 'm 'n); [
  Intro E; Elim (Zcompare_EGAL m n); Intros H3 H4;Rewrite <- (H3 E); Assumption
| Intro H3; Apply Zcompare_trans_SUPERIEUR with y:=m;[
    Elim (Zcompare_ANTISYM n m); Intros H4 H5;Apply H5; Assumption
  | Assumption ]
| Intro H3; Absurd (Zcompare m n)=SUPERIEUR;Assumption ].
Save.

Theorem Zgt_le_trans : (n,m,p:Z)(Zgt n m)->(Zle p m)->(Zgt n p).

Unfold Zle Zgt ;Intros n m p H1 H2; (ElimCompare 'p 'm); [
  Intros E;Elim (Zcompare_EGAL p m);Intros H3 H4; Rewrite (H3 E); Assumption
| Intro H3; Apply Zcompare_trans_SUPERIEUR with y:=m; [
    Assumption
  | Elim (Zcompare_ANTISYM m p); Auto with arith ]
| Intro H3; Absurd (Zcompare p m)=SUPERIEUR;Assumption ].
Save.

Theorem Zle_S_gt : (n,m:Z) (Zle (Zs n) m) -> (Zgt m n).

Intros n m H;Apply Zle_gt_trans with m:=(Zs n);[ Assumption | Apply Zgt_Sn_n ].
Save.

Theorem Zcompare_n_S : (n,m:Z)(Zcompare (Zs n) (Zs m)) = (Zcompare n m).
Intros n m;Unfold Zs ;Do 2 Rewrite -> [t:Z](Zplus_sym t (POS xH));
Rewrite -> Zcompare_Zplus_compatible;Auto with arith.
Save.
 
Theorem Zgt_n_S : (n,m:Z)(Zgt m n) -> (Zgt (Zs m) (Zs n)).

Unfold Zgt; Intros n m H; Rewrite Zcompare_n_S; Auto with arith.
Save.

Lemma Zle_not_gt     : (n,m:Z)(Zle n m) -> ~(Zgt n m).

Unfold Zle Zgt; Auto with arith.
Save.

Lemma Zgt_antirefl   : (n:Z)~(Zgt n n).

Unfold Zgt ;Intros n; Elim (Zcompare_EGAL n n); Intros H1 H2;
Rewrite H2; [ Discriminate | Trivial with arith ].
Save.

Lemma Zgt_not_sym    : (n,m:Z)(Zgt n m) -> ~(Zgt m n).

Unfold Zgt ;Intros n m H; Elim (Zcompare_ANTISYM n m); Intros H1 H2;
Rewrite -> H1; [ Discriminate | Assumption ].
Save.

Lemma Zgt_not_le     : (n,m:Z)(Zgt n m) -> ~(Zle n m).

Unfold Zgt Zle not; Auto with arith.
Save.

Lemma Zgt_trans      : (n,m,p:Z)(Zgt n m)->(Zgt m p)->(Zgt n p).

Unfold Zgt; Exact Zcompare_trans_SUPERIEUR.
Save.

Lemma Zle_gt_S       : (n,p:Z)(Zle n p)->(Zgt (Zs p) n).

Unfold Zle Zgt ;Intros n p H; (ElimCompare 'n 'p); [
  Intros H1;Elim (Zcompare_EGAL n p);Intros H2 H3; Rewrite <- H2; [
    Exact (Zgt_Sn_n n)
  | Assumption ]
 
| Intros H1;Apply Zcompare_trans_SUPERIEUR with y:=p; [
    Exact (Zgt_Sn_n p)
  | Elim (Zcompare_ANTISYM p n); Auto with arith ]
| Intros H1;Absurd (Zcompare n p)=SUPERIEUR;Assumption ].
Save.

Lemma Zgt_pred       
	: (n,p:Z)(Zgt p (Zs n))->(Zgt (Zpred p) n).

Unfold Zgt Zs Zpred ;Intros n p H; 
Rewrite <- [x,y:Z](Zcompare_Zplus_compatible x y (POS xH));
Rewrite (Zplus_sym p); Rewrite Zplus_assoc; Rewrite [x:Z](Zplus_sym x n);
Simpl; Assumption.
Save.

Lemma Zsimpl_gt_plus_l 
	: (n,m,p:Z)(Zgt (Zplus p n) (Zplus p m))->(Zgt n m).

Unfold Zgt; Intros n m p H; 
	Rewrite <- (Zcompare_Zplus_compatible n m p); Assumption.
Save.

Lemma Zsimpl_gt_plus_r
	: (n,m,p:Z)(Zgt (Zplus n p) (Zplus m p))->(Zgt n m).

Intros n m p H; Apply Zsimpl_gt_plus_l with p.
Rewrite (Zplus_sym p n); Rewrite (Zplus_sym p m); Trivial.

Save.

Lemma Zgt_reg_l      
	: (n,m,p:Z)(Zgt n m)->(Zgt (Zplus p n) (Zplus p m)).

Unfold Zgt; Intros n m p H; Rewrite (Zcompare_Zplus_compatible n m p); 
Assumption.
Save.

Lemma Zgt_reg_r : (n,m,p:Z)(Zgt n m)->(Zgt (Zplus n p) (Zplus m p)).
Intros n m p H; Rewrite (Zplus_sym n p); Rewrite (Zplus_sym m p); Apply Zgt_reg_l; Trivial.
Save.

Theorem Zcompare_et_un: 
  (x,y:Z) (Zcompare x y)=SUPERIEUR <-> 
    ~(Zcompare x (Zplus y (POS xH)))=INFERIEUR.

Intros x y; Split; [
  Intro H; (ElimCompare 'x '(Zplus y (POS xH)));[
    Intro H1; Rewrite H1; Discriminate
  | Intros H1; Elim SUPERIEUR_POS with 1:=H; Intros h H2; 
    Absurd (gt (convert h) O) /\ (lt (convert h) (S O)); [
      Unfold not ;Intros H3;Elim H3;Intros H4 H5; Absurd (gt (convert h) O); [
        Unfold gt ;Apply le_not_lt; Apply le_S_n; Exact H5
      | Assumption]
    | Split; [
        Elim (ZL4 h); Intros i H3;Rewrite H3; Apply gt_Sn_O
      | Change (lt (convert h) (convert xH)); 
        Apply compare_convert_INFERIEUR;
        Change (Zcompare (POS h) (POS xH))=INFERIEUR;
        Rewrite <- H2; Rewrite <- [m,n:Z](Zcompare_Zplus_compatible m n y);
        Rewrite (Zplus_sym x);Rewrite Zplus_assoc; Rewrite Zplus_inverse_r;
        Simpl; Exact H1 ]]
  | Intros H1;Rewrite -> H1;Discriminate ]
| Intros H; (ElimCompare 'x '(Zplus y (POS xH))); [
    Intros H1;Elim (Zcompare_EGAL x (Zplus y (POS xH))); Intros H2 H3;
    Rewrite  (H2 H1); Exact (Zgt_Sn_n y)
  | Intros H1;Absurd (Zcompare x (Zplus y (POS xH)))=INFERIEUR;Assumption
  | Intros H1; Apply Zcompare_trans_SUPERIEUR with y:=(Zs y); 
      [ Exact H1 | Exact (Zgt_Sn_n y) ]]].
Save.

Lemma Zgt_S_n        : (n,p:Z)(Zgt (Zs p) (Zs n))->(Zgt p n).

Unfold Zs Zgt;Intros n p;Do 2 Rewrite -> [m:Z](Zplus_sym m (POS xH));
Rewrite -> (Zcompare_Zplus_compatible p n (POS xH));Trivial with arith.
Save.

Lemma Zle_S_n     : (n,m:Z) (Zle (Zs m) (Zs n)) -> (Zle m n).

Unfold Zle not ;Intros m n H1 H2;Apply H1;
Unfold Zs ;Do 2 Rewrite <- (Zplus_sym (POS xH));
Rewrite -> (Zcompare_Zplus_compatible n m (POS xH));Assumption.
Save.

Lemma Zgt_le_S       : (n,p:Z)(Zgt p n)->(Zle (Zs n) p).

Unfold Zgt Zle; Intros n p H; Elim (Zcompare_et_un p n); Intros H1 H2;
Unfold not ;Intros H3; Unfold not in H1; Apply H1; [
  Assumption
| Elim (Zcompare_ANTISYM (Zplus n (POS xH)) p);Intros H4 H5;Apply H4;Exact H3].
Save.

Lemma Zgt_S_le       : (n,p:Z)(Zgt (Zs p) n)->(Zle n p).

Intros n p H;Apply Zle_S_n; Apply Zgt_le_S; Assumption.
Save.

Theorem Zgt_S        : (n,m:Z)(Zgt (Zs n) m)->((Zgt n m)\/(<Z>m=n)).

Intros n m H; Unfold Zgt; (ElimCompare 'n 'm); [
  Elim (Zcompare_EGAL n m); Intros H1 H2 H3;Rewrite -> H1;Auto with arith
| Intros H1;Absurd (Zcompare m n)=SUPERIEUR; 
    [ Exact (Zgt_S_le m n H) | Elim (Zcompare_ANTISYM m n); Auto with arith ]
| Auto with arith ].
Save.

Theorem Zgt_trans_S  : (n,m,p:Z)(Zgt (Zs n) m)->(Zgt m p)->(Zgt n p).

Intros n m p H1 H2;Apply Zle_gt_trans with m:=m;
  [ Apply Zgt_S_le; Assumption | Assumption ].
Save.

Theorem Zeq_S : (n,m:Z) n=m -> (Zs n)=(Zs m).
Intros n m H; Rewrite H; Auto with arith.
Save.

Theorem Zpred_Sn : (m:Z) m=(Zpred (Zs m)).
Intros m; Unfold Zpred Zs; Rewrite <- Zplus_assoc; Simpl; 
Rewrite Zplus_sym; Auto with arith.
Save.

Theorem Zeq_add_S : (n,m:Z) (Zs n)=(Zs m) -> n=m.
Intros n m H.
Change (Zplus (Zplus (NEG xH) (POS xH)) n)=
       (Zplus (Zplus (NEG xH) (POS xH)) m);
Do 2 Rewrite <- Zplus_assoc; Do 2 Rewrite (Zplus_sym (POS xH));
Unfold Zs in H;Rewrite H; Trivial with arith.
Save.
 
Theorem Znot_eq_S : (n,m:Z) ~(n=m) -> ~((Zs n)=(Zs m)).

Unfold not ;Intros n m H1 H2;Apply H1;Apply Zeq_add_S; Assumption.
Save.
 
Lemma Zsimpl_plus_l : (n,m,p:Z)(Zplus n m)=(Zplus n p)->m=p.
Intros n m p H; Cut (Zplus (Zopp n) (Zplus n m))=(Zplus (Zopp n) (Zplus n p));[
  Do 2 Rewrite -> Zplus_assoc; Rewrite -> (Zplus_sym (Zopp n) n);
  Rewrite -> Zplus_inverse_r;Simpl; Trivial with arith
| Rewrite -> H; Trivial with arith ].
Save.

Theorem Zn_Sn : (n:Z) ~(n=(Zs n)).
Intros n;Cut ~ZERO=(POS xH);[
  Unfold not ;Intros H1 H2;Apply H1;Apply (Zsimpl_plus_l n);Rewrite Zero_right;
  Exact H2
| Discriminate ].
Save.

Lemma Zplus_n_O : (n:Z) n=(Zplus n ZERO).
Intro; Rewrite Zero_right; Trivial with arith.
Save.

Lemma Zplus_unit_left : (n,m:Z) (Zplus n ZERO)=m -> n=m.
Intro; Rewrite Zero_right; Trivial with arith.
Save.

Lemma Zplus_unit_right : (n,m:Z) n=(Zplus m ZERO) -> n=m.
Intros n m; Rewrite (Zero_right m); Trivial with arith.
Save.

Lemma Zplus_n_Sm : (n,m:Z) (Zs (Zplus n m))=(Zplus n (Zs m)).

Intros n m; Unfold Zs; Rewrite Zplus_assoc; Trivial with arith.
Save.

Lemma Zmult_n_O : (n:Z) ZERO=(Zmult n ZERO).

Intro;Rewrite Zmult_sym;Simpl; Trivial with arith.
Save.

Lemma Zmult_n_Sm : (n,m:Z) (Zplus (Zmult n m) n)=(Zmult n (Zs m)).

Intros n m;Unfold Zs; Rewrite Zmult_plus_distr_r;
Rewrite (Zmult_sym n (POS xH));Rewrite Zmult_one; Trivial with arith.
Save.

Theorem Zle_n : (n:Z) (Zle n n).
Intros n;Elim (Zcompare_EGAL n n);Unfold Zle ;Intros H1 H2;Rewrite H2;
  [ Discriminate | Trivial with arith ].
Save. 

Theorem Zle_refl : (n,m:Z) n=m -> (Zle n m).
Intros; Rewrite H; Apply Zle_n.
Save.

Theorem Zle_trans : (n,m,p:Z)(Zle n m)->(Zle m p)->(Zle n p).

Intros n m p;Unfold 1 3 Zle; Unfold not; Intros H1 H2 H3;Apply H1;
Exact (Zgt_le_trans n p m H3 H2).
Save.

Theorem Zle_n_Sn : (n:Z)(Zle n (Zs n)).

Intros n; Apply Zgt_S_le;Apply Zgt_trans with m:=(Zs n) ;Apply Zgt_Sn_n.
Save.

Lemma Zle_n_S : (n,m:Z) (Zle m n) -> (Zle (Zs m) (Zs n)).

Unfold Zle not ;Intros m n H1 H2; Apply H1; 
Rewrite <- (Zcompare_Zplus_compatible n m (POS xH));
Do 2 Rewrite (Zplus_sym (POS xH)); Exact H2.
Save.

Hints Resolve Zle_n Zle_n_Sn Zle_trans Zle_n_S : zarith.
Hints Immediate Zle_refl : zarith.

Lemma Zs_pred : (n:Z) n=(Zs (Zpred n)).

Intros n; Unfold Zs Zpred ;Rewrite <- Zplus_assoc; Simpl; Rewrite Zero_right;
Trivial with arith.
Save. 

Hints Immediate Zs_pred : zarith.
 
Theorem Zle_pred_n : (n:Z)(Zle (Zpred n) n).

Intros n;Pattern 2 n ;Rewrite Zs_pred; Apply Zle_n_Sn.
Save.
 
Theorem Zle_trans_S : (n,m:Z)(Zle (Zs n) m)->(Zle n m).

Intros n m H;Apply Zle_trans with m:=(Zs n); [ Apply Zle_n_Sn | Assumption ].
Save.

Theorem Zle_Sn_n : (n:Z)~(Zle (Zs n) n).

Intros n; Apply Zgt_not_le; Apply Zgt_Sn_n.
Save.

Theorem Zle_antisym : (n,m:Z)(Zle n m)->(Zle m n)->(n=m).

Unfold Zle ;Intros n m H1 H2; (ElimCompare 'n 'm); [
  Elim (Zcompare_EGAL n m);Auto with arith
| Intros H3;Absurd (Zcompare m n)=SUPERIEUR; [
    Assumption
  | Elim (Zcompare_ANTISYM m n);Auto with arith ]
| Intros H3;Absurd (Zcompare n m)=SUPERIEUR;Assumption ].
Save.

Theorem Zgt_lt : (m,n:Z) (Zgt m n) -> (Zlt n m).
Unfold Zgt Zlt ;Intros m n H; Elim (Zcompare_ANTISYM m n); Auto with arith.
Save.

Theorem Zlt_gt : (m,n:Z) (Zlt m n) -> (Zgt n m).
Unfold Zgt Zlt ;Intros m n H; Elim (Zcompare_ANTISYM n m); Auto with arith.
Save.

Theorem Zge_le : (m,n:Z) (Zge m n) -> (Zle n m).
Intros m n; Change ~(Zlt m n)-> ~(Zgt n m);
Unfold not; Intros H1 H2; Apply H1; Apply Zgt_lt; Assumption.
Save.

Theorem Zle_ge : (m,n:Z) (Zle m n) -> (Zge n m).
Intros m n; Change ~(Zgt m n)-> ~(Zlt n m);
Unfold not; Intros H1 H2; Apply H1; Apply Zlt_gt; Assumption.
Save.

Theorem Zge_trans : (n, m, p : Z) (Zge n m) -> (Zge m p) -> (Zge n p).
Intros n m p H1 H2.
Apply Zle_ge.
Apply Zle_trans with m; Apply Zge_le; Trivial.
Save.

Theorem Zlt_n_Sn : (n:Z)(Zlt n (Zs n)).
Intro n; Apply Zgt_lt; Apply Zgt_Sn_n.
Save.
Theorem Zlt_S : (n,m:Z)(Zlt n m)->(Zlt n (Zs m)).
Intros n m H;Apply Zgt_lt; Apply Zgt_trans with m:=m; [
  Apply Zgt_Sn_n
| Apply Zlt_gt; Assumption ].
Save.

Theorem Zlt_n_S : (n,m:Z)(Zlt n m)->(Zlt (Zs n) (Zs m)).
Intros n m H;Apply Zgt_lt;Apply Zgt_n_S;Apply Zlt_gt; Assumption.
Save.

Theorem Zlt_S_n : (n,m:Z)(Zlt (Zs n) (Zs m))->(Zlt n m).

Intros n m H;Apply Zgt_lt;Apply Zgt_S_n;Apply Zlt_gt; Assumption.
Save.

Theorem Zlt_n_n : (n:Z)~(Zlt n n).

Intros n;Elim (Zcompare_EGAL n n); Unfold Zlt ;Intros H1 H2;
Rewrite H2; [ Discriminate | Trivial with arith ].
Save.

Lemma Zlt_pred : (n,p:Z)(Zlt (Zs n) p)->(Zlt n (Zpred p)).

Intros n p H;Apply Zlt_S_n; Rewrite <- Zs_pred; Assumption.
Save.

Lemma Zlt_pred_n_n : (n:Z)(Zlt (Zpred n) n).

Intros n; Apply Zlt_S_n; Rewrite <- Zs_pred; Apply Zlt_n_Sn.
Save.
 
Theorem Zlt_le_S : (n,p:Z)(Zlt n p)->(Zle (Zs n) p).
Intros n p H; Apply Zgt_le_S; Apply Zlt_gt; Assumption.
Save.

Theorem Zlt_n_Sm_le : (n,m:Z)(Zlt n (Zs m))->(Zle n m).
Intros n m H; Apply Zgt_S_le; Apply Zlt_gt; Assumption.
Save.

Theorem Zle_lt_n_Sm : (n,m:Z)(Zle n m)->(Zlt n (Zs m)).
Intros n m H; Apply Zgt_lt; Apply Zle_gt_S; Assumption.
Save.

Theorem Zlt_le_weak : (n,m:Z)(Zlt n m)->(Zle n m).
Unfold Zlt Zle ;Intros n m H;Rewrite H;Discriminate.
Save.

Theorem Zlt_trans : (n,m,p:Z)(Zlt n m)->(Zlt m p)->(Zlt n p).
Intros n m p H1 H2; Apply Zgt_lt; Apply Zgt_trans with m:= m; 
Apply Zlt_gt; Assumption.
Save.
Theorem Zlt_le_trans : (n,m,p:Z)(Zlt n m)->(Zle m p)->(Zlt n p).
Intros n m p H1 H2;Apply Zgt_lt;Apply Zle_gt_trans with m:=m;
  [ Assumption | Apply Zlt_gt;Assumption ].
Save.

Theorem Zle_lt_trans : (n,m,p:Z)(Zle n m)->(Zlt m p)->(Zlt n p).

Intros n m p H1 H2;Apply Zgt_lt;Apply Zgt_le_trans with m:=m; 
  [ Apply Zlt_gt;Assumption | Assumption ].
Save.
 
Theorem Zle_lt_or_eq : (n,m:Z)(Zle n m)->((Zlt n m) \/ n=m).

Unfold Zle Zlt ;Intros n m H; (ElimCompare 'n 'm); [
  Elim (Zcompare_EGAL n m);Auto with arith
| Auto with arith
| Intros H';Absurd (Zcompare n m)=SUPERIEUR;Assumption ].
Save.

Theorem Zle_or_lt : (n,m:Z)((Zle n m)\/(Zlt m n)).

Unfold Zle Zlt ;Intros n m; (ElimCompare 'n 'm); [
  Intros E;Rewrite -> E;Left;Discriminate
| Intros E;Rewrite -> E;Left;Discriminate
| Elim (Zcompare_ANTISYM n m); Auto with arith ].
Save.

Theorem Zle_not_lt : (n,m:Z)(Zle n m) -> ~(Zlt m n).

Unfold Zle Zlt; Unfold not ;Intros n m H1 H2;Apply H1; 
Elim (Zcompare_ANTISYM n m);Auto with arith.
Save.

Theorem Zlt_not_le : (n,m:Z)(Zlt n m) -> ~(Zle m n).
Unfold Zlt Zle not ;Intros n m H1 H2; Apply H2; Elim (Zcompare_ANTISYM m n);
Auto with arith.
Save.

Theorem Zlt_not_sym : (n,m:Z)(Zlt n m) -> ~(Zlt m n).
Intros n m H;Apply Zle_not_lt; Apply Zlt_le_weak; Assumption.
Save.

Theorem Zle_le_S : (x,y:Z)(Zle x y)->(Zle x (Zs y)).
Intros.
Apply Zle_trans with y; Trivial with zarith.
Save.

Hints Resolve Zle_le_S : zarith.

Definition Zmin := [n,m:Z]
 <Z>Cases (Zcompare n m) of
      EGAL      => n
    | INFERIEUR => n
    | SUPERIEUR => m
    end.

Lemma Zmin_SS : (n,m:Z)((Zs (Zmin n m))=(Zmin (Zs n) (Zs m))).

Intros n m;Unfold Zmin; Rewrite (Zcompare_n_S n m);
(ElimCompare 'n 'm);Intros E;Rewrite E;Auto with arith.
Save.

Lemma Zle_min_l : (n,m:Z)(Zle (Zmin n m) n).

Intros n m;Unfold Zmin ; (ElimCompare 'n 'm);Intros E;Rewrite -> E;
  [ Apply Zle_n | Apply Zle_n | Apply Zlt_le_weak; Apply Zgt_lt;Exact E ].
Save.

Lemma Zle_min_r : (n,m:Z)(Zle (Zmin n m) m).

Intros n m;Unfold Zmin ; (ElimCompare 'n 'm);Intros E;Rewrite -> E;[
  Unfold Zle ;Rewrite -> E;Discriminate
| Unfold Zle ;Rewrite -> E;Discriminate
| Apply Zle_n ].
Save.

Lemma Zmin_case : (n,m:Z)(P:Z->Set)(P n)->(P m)->(P (Zmin n m)).
Intros n m P H1 H2; Unfold Zmin; Case (Zcompare n m);Auto with arith.
Save.

Lemma Zmin_or : (n,m:Z)(Zmin n m)=n \/ (Zmin n m)=m.
Unfold Zmin; Intros; Elim (Zcompare n m); Auto.
Save.

Lemma Zmin_n_n : (n:Z) (Zmin n n)=n.
Unfold Zmin; Intros; Elim (Zcompare n n); Auto.
Save.

Lemma Zplus_assoc_l : (n,m,p:Z)((Zplus n (Zplus m p))=(Zplus (Zplus n m) p)).

Exact Zplus_assoc.
Save.

Lemma Zplus_assoc_r : (n,m,p:Z)(Zplus (Zplus n m) p) =(Zplus n (Zplus m p)).

Intros; Symmetry; Apply Zplus_assoc.
Save.

Lemma Zplus_permute : (n,m,p:Z) (Zplus n (Zplus m p))=(Zplus m (Zplus n p)).

Intros n m p;
Rewrite Zplus_sym;Rewrite <- Zplus_assoc; Rewrite (Zplus_sym p n); Trivial with arith.
Save.

Lemma Zsimpl_le_plus_l : (p,n,m:Z)(Zle (Zplus p n) (Zplus p m))->(Zle n m).

Intros p n m; Unfold Zle not ;Intros H1 H2;Apply H1; 
Rewrite (Zcompare_Zplus_compatible n m p); Assumption.
Save.
 
Lemma Zsimpl_le_plus_r : (p,n,m:Z)(Zle (Zplus n p) (Zplus m p))->(Zle n m).

Intros p n m H; Apply Zsimpl_le_plus_l with p.
Rewrite (Zplus_sym p n); Rewrite (Zplus_sym p m); Trivial.
Save.

Lemma Zle_reg_l : (n,m,p:Z)(Zle n m)->(Zle (Zplus p n) (Zplus p m)).

Intros n m p; Unfold Zle not ;Intros H1 H2;Apply H1; 
Rewrite <- (Zcompare_Zplus_compatible n m p); Assumption.
Save.

Lemma Zle_reg_r : (a,b,c:Z) (Zle a b)->(Zle (Zplus a c) (Zplus b c)).

Intros a b c;Do 2 Rewrite [n:Z](Zplus_sym n c); Exact (Zle_reg_l a b c).
Save.

Lemma Zle_plus_plus : 
 (n,m,p,q:Z) (Zle n m)->(Zle p q)->(Zle (Zplus n p) (Zplus m q)).

Intros n m p q; Intros H1 H2;Apply Zle_trans with m:=(Zplus n q); [
  Apply Zle_reg_l;Assumption | Apply Zle_reg_r;Assumption ].
Save.

Lemma Zplus_Snm_nSm : (n,m:Z)(Zplus (Zs n) m)=(Zplus n (Zs m)).

Unfold Zs ;Intros n m; Rewrite <- Zplus_assoc; Rewrite (Zplus_sym (POS xH));
Trivial with arith.
Save.

Lemma Zsimpl_lt_plus_l 
	: (n,m,p:Z)(Zlt (Zplus p n) (Zplus p m))->(Zlt n m).

Unfold Zlt ;Intros n m p; 
	Rewrite Zcompare_Zplus_compatible;Trivial with arith.
Save.
 
Lemma Zsimpl_lt_plus_r
	: (n,m,p:Z)(Zlt (Zplus n p) (Zplus m p))->(Zlt n m).

Intros n m p H; Apply Zsimpl_lt_plus_l with p.
Rewrite (Zplus_sym p n); Rewrite (Zplus_sym p m); Trivial.
Save.
 
Lemma Zlt_reg_l : (n,m,p:Z)(Zlt n m)->(Zlt (Zplus p n) (Zplus p m)).
Unfold Zlt ;Intros n m p; Rewrite Zcompare_Zplus_compatible;Trivial with arith.
Save.

Lemma Zlt_reg_r : (n,m,p:Z)(Zlt n m)->(Zlt (Zplus n p) (Zplus m p)).
Intros n m p H; Rewrite (Zplus_sym n p); Rewrite (Zplus_sym m p); Apply Zlt_reg_l; Trivial.
Save.

Lemma Zlt_le_reg :
 (a,b,c,d:Z) (Zlt a b)->(Zle c d)->(Zlt (Zplus a c) (Zplus b d)).
Intros a b c d H0 H1.
Apply Zlt_le_trans with (Zplus b c).
Apply  Zlt_reg_r; Trivial.
Apply  Zle_reg_l; Trivial.
Save.


Lemma Zle_lt_reg :
 (a,b,c,d:Z) (Zle a b)->(Zlt c d)->(Zlt (Zplus a c) (Zplus b d)).
Intros a b c d H0 H1.
Apply Zle_lt_trans with (Zplus b c).
Apply  Zle_reg_r; Trivial.
Apply  Zlt_reg_l; Trivial.
Save.


Definition Zminus := [m,n:Z](Zplus m (Zopp n)).

Lemma Zminus_plus_simpl : 
  (n,m,p:Z)((Zminus n m)=(Zminus (Zplus p n) (Zplus p m))).

Intros n m p;Unfold Zminus; Rewrite Zopp_Zplus; Rewrite Zplus_assoc;
Rewrite (Zplus_sym p); Rewrite <- (Zplus_assoc n p); Rewrite Zplus_inverse_r;
Rewrite Zero_right; Trivial with arith.
Save.

Lemma Zminus_n_O : (n:Z)(n=(Zminus n ZERO)).

Intro; Unfold Zminus; Simpl;Rewrite Zero_right; Trivial with arith.
Save.

Lemma Zminus_n_n : (n:Z)(ZERO=(Zminus n n)).
Intro; Unfold Zminus; Rewrite Zplus_inverse_r; Trivial with arith.
Save.

Lemma Zplus_minus : (n,m,p:Z)(n=(Zplus m p))->(p=(Zminus n m)).

Intros n m p H;Unfold Zminus;Apply (Zsimpl_plus_l m); 
Rewrite (Zplus_sym m (Zplus n (Zopp m))); Rewrite <- Zplus_assoc;
Rewrite Zplus_inverse_l; Rewrite Zero_right; Rewrite H; Trivial with arith.
Save.
 
Lemma Zminus_plus : (n,m:Z)(Zminus (Zplus n m) n)=m.
Intros n m;Unfold Zminus ;Rewrite -> (Zplus_sym n m);Rewrite <- Zplus_assoc;
Rewrite -> Zplus_inverse_r; Apply Zero_right.
Save.

Lemma Zle_plus_minus : (n,m:Z) (Zplus n (Zminus m n))=m.

Unfold Zminus; Intros n m; Rewrite Zplus_permute; Rewrite Zplus_inverse_r;
Apply Zero_right.
Save.

Lemma Zminus_Sn_m : (n,m:Z)((Zs (Zminus n m))=(Zminus (Zs n) m)).

Intros n m;Unfold Zminus Zs; Rewrite (Zplus_sym n (Zopp m));
Rewrite <- Zplus_assoc;Apply Zplus_sym.
Save.

Lemma Zlt_minus : (n,m:Z)(Zlt ZERO m)->(Zlt (Zminus n m) n).

Intros n m H; Apply Zsimpl_lt_plus_l with p:=m; Rewrite Zle_plus_minus;
Pattern 1 n ;Rewrite <- (Zero_right n); Rewrite (Zplus_sym m n);
Apply Zlt_reg_l; Assumption.
Save.

Lemma Zlt_O_minus_lt : (n,m:Z)(Zlt ZERO (Zminus n m))->(Zlt m n).

Intros n m H; Apply Zsimpl_lt_plus_l with p:=(Zopp m); Rewrite Zplus_inverse_l;
Rewrite Zplus_sym;Exact H.
Save.

Lemma Zmult_plus_distr_l : 
  (n,m,p:Z)((Zmult (Zplus n m) p)=(Zplus (Zmult n p) (Zmult m p))).

Intros n m p;Rewrite Zmult_sym;Rewrite Zmult_plus_distr_r; 
Do 2 Rewrite -> (Zmult_sym p); Trivial with arith.
Save.

Lemma Zmult_minus_distr :
  (n,m,p:Z)((Zmult (Zminus n m) p)=(Zminus (Zmult n p) (Zmult m p))).
Intros n m p;Unfold Zminus; Rewrite Zmult_plus_distr_l; Rewrite Zopp_Zmult;
Trivial with arith.
Save.
 
Lemma Zmult_assoc_r : (n,m,p:Z)((Zmult (Zmult n m) p) = (Zmult n (Zmult m p))).
Intros n m p; Rewrite Zmult_assoc; Trivial with arith.
Save.

Lemma Zmult_assoc_l : (n,m,p:Z)(Zmult n (Zmult m p)) = (Zmult (Zmult n m) p).
Intros n m p; Rewrite Zmult_assoc; Trivial with arith.
Save.

Theorem Zmult_permute : (n,m,p:Z)(Zmult n (Zmult m p)) = (Zmult m (Zmult n p)).
Intros; Rewrite -> (Zmult_assoc m n p); Rewrite -> (Zmult_sym m n).
Apply Zmult_assoc.
Save.

Lemma Zmult_1_n : (n:Z)(Zmult (POS xH) n)=n.
Exact Zmult_one.
Save.

Lemma Zmult_n_1 : (n:Z)(Zmult n (POS xH))=n.
Intro; Rewrite Zmult_sym; Apply Zmult_one.
Save.

Lemma Zmult_Sm_n : (n,m:Z) (Zplus (Zmult n m) m)=(Zmult (Zs n) m).
Intros n m; Unfold Zs; Rewrite Zmult_plus_distr_l; Rewrite Zmult_1_n;
Trivial with arith.
Save.


(** Just for compatibility with previous versions. 
    Use [Zmult_plus_distr_r] and [Zmult_plus_distr_l] rather than
    their synomymous *)

Definition Zmult_Zplus_distr := Zmult_plus_distr_r.
Definition Zmult_plus_distr := Zmult_plus_distr_l.
