(**************************************************************************)
(*                                                                        *)
(* Binary Integers                                                        *)
(*                                                                        *)
(* Pierre Crégut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

(* $Id$ *)

Require Export Arith.
Require fast_integer.
Require zarith_aux.
Require Peano_dec.
Require Export Compare_dec.

Definition neq := [x,y:nat] ~(x=y).
Definition Zne := [x,y:Z] ~(x=y).
Theorem add_un_Zs : (x:positive) (POS (add_un x)) = (Zs (POS x)).
Intro; Rewrite -> ZL12; Unfold Zs; Simpl; Trivial with arith.
Save.

Theorem pred_of_minus : (x:nat)(pred x)=(minus x (S O)).
Induction x; Auto with arith.
Save.

Theorem inj_S : (y:nat) (inject_nat (S y)) = (Zs (inject_nat y)).
Induction y; [
  Unfold Zs ; Simpl; Trivial with arith
| Intros n; Intros H;
  Change (POS (add_un (anti_convert n)))=(Zs (inject_nat (S n)));
  Rewrite add_un_Zs; Trivial with arith].
Save.
 
Theorem Zplus_S_n: (x,y:Z) (Zplus (Zs x) y) = (Zs (Zplus x y)).
Intros x y; Unfold Zs; Rewrite (Zplus_sym (Zplus x y)); Rewrite Zplus_assoc;
Rewrite (Zplus_sym (POS xH)); Trivial with arith.
Save.

Theorem inj_plus : 
  (x,y:nat) (inject_nat (plus x y)) = (Zplus (inject_nat x) (inject_nat y)).

Induction x; Induction y; [
  Simpl; Trivial with arith
| Simpl; Trivial with arith
| Simpl; Rewrite <- plus_n_O; Trivial with arith
| Intros m H1; Change (inject_nat (S (plus n (S m))))=
                        (Zplus (inject_nat (S n)) (inject_nat (S m)));
  Rewrite inj_S; Rewrite H; Do 2 Rewrite inj_S; Rewrite Zplus_S_n; Trivial with arith].
Save.
 
Theorem inj_mult : 
  (x,y:nat) (inject_nat (mult x y)) = (Zmult (inject_nat x) (inject_nat y)).

Induction x; [
  Simpl; Trivial with arith
| Intros n H y; Rewrite -> inj_S; Rewrite <- Zmult_Sm_n;
    Rewrite <- H;Rewrite <- inj_plus; Simpl; Rewrite plus_sym; Trivial with arith].
Save.

Theorem inj_neq:
  (x,y:nat) (neq x y) -> (Zne (inject_nat x) (inject_nat y)).

Unfold neq Zne not ; Intros x y H1 H2; Apply H1; Generalize H2; 
Case x; Case y; Intros; [
  Auto with arith
| Discriminate H0
| Discriminate H0
| Simpl in H0; Injection H0; Do 2 Rewrite <- bij1; Intros E; Rewrite E; Auto with arith].
Save. 
Theorem inj_le:
  (x,y:nat) (le x y) -> (Zle (inject_nat x) (inject_nat y)).

Intros x y; Intros H; Elim H; [
  Unfold Zle ; Elim (Zcompare_EGAL (inject_nat x) (inject_nat x));
  Intros H1 H2; Rewrite H2; [ Discriminate | Trivial with arith]
| Intros m H1 H2; Apply Zle_trans with (inject_nat m); 
    [Assumption | Rewrite inj_S; Apply Zle_n_Sn]].
Save.

Theorem inj_lt: (x,y:nat) (lt x y) -> (Zlt (inject_nat x) (inject_nat y)).
Intros x y H; Apply Zgt_lt; Apply Zle_S_gt; Rewrite <- inj_S; Apply inj_le;
Exact H.
Save.

Theorem inj_gt: (x,y:nat) (gt x y) -> (Zgt (inject_nat x) (inject_nat y)).
Intros x y H; Apply Zlt_gt; Apply inj_lt; Exact H.
Save.

Theorem inj_ge: (x,y:nat) (ge x y) -> (Zge (inject_nat x) (inject_nat y)).
Intros x y H; Apply Zle_ge; Apply inj_le; Apply H.
Save.

Theorem inj_eq: (x,y:nat) x=y -> (inject_nat x) = (inject_nat y).
Intros x y H; Rewrite H; Trivial with arith.
Save.

Theorem intro_Z : 
  (x:nat) (EX y:Z | (inject_nat x)=y /\ 
      	  (Zle ZERO (Zplus (Zmult y (POS xH)) ZERO))).
Intros x; Exists (inject_nat x); Split; [
  Trivial with arith
| Rewrite Zmult_sym; Rewrite Zmult_one; Rewrite Zero_right; 
  Unfold Zle ; Elim x; Intros;Simpl; Discriminate ].
Save.
Theorem inj_minus1 :
  (x,y:nat) (le y x) -> 
    (inject_nat (minus x y)) = (Zminus (inject_nat x) (inject_nat y)).
Intros x y H; Apply (Zsimpl_plus_l (inject_nat y)); Unfold Zminus ;
Rewrite Zplus_permute; Rewrite Zplus_inverse_r; Rewrite <- inj_plus;
Rewrite <- (le_plus_minus y x H);Rewrite Zero_right; Trivial with arith.
Save.
 
Theorem inj_minus_aux: (x,y:nat) ~(le y x) -> (minus x y) = O.
Intros y x; Pattern y x ; Apply nat_double_ind; [
  Simpl; Trivial with arith
| Intros n H; Absurd (le O (S n)); [ Assumption | Apply le_O_n]
| Simpl; Intros n m H1 H2; Apply H1;
  Unfold not ; Intros H3; Apply H2; Apply le_n_S; Assumption].
Save.

Theorem inj_minus2: (x,y:nat) (gt y x) -> (inject_nat (minus x y)) = ZERO.
Intros x y H; Rewrite inj_minus_aux; [ Trivial with arith | Apply gt_not_le; Assumption].
Save.

Definition decidable := [P:Prop] P \/ ~P.

Theorem dec_not_not : (P:Prop)(decidable P) -> (~P -> False) -> P.
Unfold decidable; Tauto. Save.

Theorem dec_True: (decidable True).
Unfold decidable; Auto with arith.Save.
Theorem dec_False: (decidable False).
Unfold decidable not; Auto with arith.Save.
Theorem dec_or: (A,B:Prop)(decidable A) -> (decidable B) -> (decidable (A\/B)).
Unfold decidable; Tauto. Save.
Theorem dec_and: (A,B:Prop)(decidable A) -> (decidable B) ->(decidable (A/\B)).
Unfold decidable; Tauto. Save.
Theorem dec_not: (A:Prop)(decidable A) -> (decidable ~A).
Unfold decidable; Tauto. Save.
Theorem dec_imp: (A,B:Prop)(decidable A) -> (decidable B) ->(decidable (A->B)).
Unfold decidable; Tauto. Save.

Theorem dec_eq: (x,y:Z) (decidable (x=y)).
Intros x y; Unfold decidable ; Elim (Zcompare_EGAL x y);
Intros H1 H2; Elim (Dcompare (Zcompare x y)); [
    Tauto
  | Intros H3; Right; Unfold not ; Intros H4;
    Elim H3; Rewrite (H2 H4); Intros H5; Discriminate H5].
Save. 

Theorem dec_Zne: (x,y:Z) (decidable (Zne x y)).
Intros x y; Unfold decidable Zne ; Elim (Zcompare_EGAL x y).
Intros H1 H2; Elim (Dcompare (Zcompare x y)); 
  [ Right; Rewrite H1; Auto
  | Left; Unfold not; Intro; Absurd (Zcompare x y)=EGAL; 
    [ Elim H; Intros HR; Rewrite HR; Discriminate 
    | Auto]].
Save.

Theorem dec_Zle: (x,y:Z) (decidable (Zle x y)).
Intros x y; Unfold decidable Zle ; Elim (Zcompare x y); [
    Left; Discriminate
  | Left; Discriminate
  | Right; Unfold not ; Intros H; Apply H; Trivial with arith].
Save.

Theorem dec_Zgt: (x,y:Z) (decidable (Zgt x y)).
Intros x y; Unfold decidable Zgt ; Elim (Zcompare x y);
  [ Right; Discriminate | Right; Discriminate | Auto with arith].
Save.

Theorem dec_Zge: (x,y:Z) (decidable (Zge x y)).
Intros x y; Unfold decidable Zge ; Elim (Zcompare x y); [
  Left; Discriminate
| Right; Unfold not ; Intros H; Apply H; Trivial with arith
| Left; Discriminate]. 
Save.

Theorem dec_Zlt: (x,y:Z) (decidable (Zlt x y)).
Intros x y; Unfold decidable Zlt ; Elim (Zcompare x y);
  [ Right; Discriminate | Auto with arith | Right; Discriminate].
Save.
Theorem dec_eq_nat:(x,y:nat)(decidable (x=y)).
Intros x y; Unfold decidable; Elim (eq_nat_dec x y); Auto with arith.
Save.

Theorem dec_le:(x,y:nat)(decidable (le x y)).
Intros x y; Unfold decidable ; Elim (le_gt_dec x y); [
  Auto with arith
| Intro; Right; Apply gt_not_le; Assumption].
Save.

Theorem dec_lt:(x,y:nat)(decidable (lt x y)).
Intros x y; Unfold lt; Apply dec_le.
Save.

Theorem dec_gt:(x,y:nat)(decidable (gt x y)).
Intros x y; Unfold gt; Apply dec_lt.
Save.

Theorem dec_ge:(x,y:nat)(decidable (ge x y)).
Intros x y; Unfold ge; Apply dec_le.
Save.

Theorem not_not : (P:Prop)(decidable P) -> (~(~P)) -> P.
Unfold decidable; Tauto. Save.

Theorem not_or : (A,B:Prop) ~(A\/B) -> ~A /\ ~B.
Tauto. Save.

Theorem not_and : (A,B:Prop) (decidable A) -> ~(A/\B) -> ~A \/ ~B.
Tauto. Save.

Theorem not_imp : (A,B:Prop) (decidable A) -> ~(A -> B) -> A /\ ~B.
Unfold decidable;Tauto.
Save.

Theorem imp_simp : (A,B:Prop) (decidable A) -> (A -> B) -> ~A \/ B.
Unfold decidable; Tauto.
Save.

Theorem not_Zge : (x,y:Z) ~(Zge x y) -> (Zlt x y).
Unfold Zge Zlt ; Intros x y H; Apply dec_not_not;
  [ Exact (dec_Zlt x y) | Assumption].
Save.
 
Theorem not_Zlt : (x,y:Z) ~(Zlt x y) -> (Zge x y).
Unfold Zlt Zge; Auto with arith.
Save.

Theorem not_Zle : (x,y:Z) ~(Zle x y) -> (Zgt x y).
Unfold Zle Zgt ; Intros x y H; Apply dec_not_not;
  [ Exact (dec_Zgt x y) | Assumption].
 Save.
 
Theorem not_Zgt : (x,y:Z) ~(Zgt x y) -> (Zle x y).
Unfold Zgt Zle; Auto with arith.
Save.

Theorem not_Zeq : (x,y:Z) ~ x=y -> (Zlt x y) \/ (Zlt y x).

Intros x y; Elim (Dcompare (Zcompare x y)); [
  Intros H1 H2; Absurd x=y; [ Assumption | Elim (Zcompare_EGAL x y); Auto with arith]
| Unfold Zlt ; Intros H; Elim H; Intros H1; 
    [Auto with arith | Right; Elim (Zcompare_ANTISYM x y); Auto with arith]].
Save. 

Theorem not_le : (x,y:nat) ~(le x y) -> (gt x y).
Intros x y H; Elim (le_gt_dec x y);
  [ Intros H1; Absurd (le x y); Assumption | Trivial with arith ].
Save.

Theorem not_ge : (x,y:nat) ~(ge x y) -> (lt x y).
Intros x y H; Exact (not_le y x H).
Save.

Theorem not_gt : (x,y:nat) ~(gt x y) -> (le x y).
Intros x y H; Elim (le_gt_dec x y);
  [ Trivial with arith | Intros H1; Absurd (gt x y); Assumption].
Save.

Theorem not_lt : (x,y:nat) ~(lt x y) -> (ge x y).
Intros x y H; Exact (not_gt y x H). 
Save.

Theorem not_eq : (x,y:nat) ~ x=y -> (lt x y) \/ (lt y x).
Intros x y H; Elim (lt_eq_lt_dec x y); [
  Intros H1; Elim H1; [ Auto with arith | Intros H2; Absurd x=y; Assumption]
| Auto with arith].
Save.

Theorem eq_ind_r : (A:Set)(x:A)(P:A->Prop)(P x)->(y:A)y=x -> (P y).
Intros A x P H y H0; Elim (sym_eq A y x H0); Assumption.
Save.

Theorem eqT_ind_r : (A:Type)(x:A)(P:A->Prop)(P x)->(y:A)y==x -> (P y).
Intros A x P H y H0; Elim (sym_eqT A y x H0); Assumption.
Save.
Lemma new_var: (x:Z) (EX y:Z |(x=y)).

Intros x; Exists x; Trivial with arith. 
Save.
Theorem Zne_left : (x,y:Z) (Zne x y) -> (Zne (Zplus x (Zopp y)) ZERO).
Intros x y; Unfold Zne; Unfold not; Intros H1 H2; Apply H1;
Apply Zsimpl_plus_l with (Zopp y); Rewrite Zplus_inverse_l; Rewrite Zplus_sym;
Trivial with arith.
Save.

Theorem Zegal_left : (x,y:Z) (x=y) -> (Zplus x (Zopp y)) = ZERO.
Intros x y H;Apply (Zsimpl_plus_l y);Rewrite -> Zplus_permute;
Rewrite -> Zplus_inverse_r;Do 2 Rewrite -> Zero_right;Assumption.
Save.

Theorem Zle_left : (x,y:Z) (Zle x y) -> (Zle ZERO (Zplus y (Zopp x))).
Intros x y H; Apply (Zsimpl_le_plus_l x); Rewrite Zplus_permute;
Rewrite Zplus_inverse_r; Do 2 Rewrite Zero_right; Assumption.
Save.

Theorem Zlt_left :
  (x,y:Z) (Zlt x y) -> (Zle ZERO (Zplus (Zplus y (NEG xH)) (Zopp x))).
Intros x y H; Apply Zle_left; Apply Zle_S_n; 
Change (Zle (Zs x) (Zs (Zpred y))); Rewrite <- Zs_pred; Apply Zlt_le_S;
Assumption.
Save.

Theorem Zge_left : (x,y:Z) (Zge x y) -> (Zle ZERO (Zplus x (Zopp y))).
Intros x y H; Apply Zle_left; Apply Zge_le; Assumption.
Save.

Theorem Zgt_left :
  (x,y:Z) (Zgt x y) -> (Zle ZERO (Zplus (Zplus x (NEG xH)) (Zopp y))).
Intros x y H; Apply Zlt_left; Apply Zgt_lt; Assumption.
Save.
Theorem Zopp_one : (x:Z)(Zopp x)=(Zmult x (NEG xH)).
Induction x; Intros; Rewrite Zmult_sym; Auto with arith.
Save.

Theorem Zopp_Zmult_r : (x,y:Z)(Zopp (Zmult x y)) = (Zmult x (Zopp y)).
Intros x y; Rewrite Zmult_sym; Rewrite <- Zopp_Zmult; Apply Zmult_sym.
Save.

Theorem Zmult_Zopp_left :  (x,y:Z)(Zmult (Zopp x) y) = (Zmult x (Zopp y)).
Intros; Rewrite Zopp_Zmult; Rewrite Zopp_Zmult_r; Trivial with arith.
Save.

Theorem Zred_factor0 : (x:Z) x = (Zmult x (POS xH)).
Intro x; Rewrite (Zmult_n_1 x); Trivial with arith.
Save.

Theorem Zred_factor1 : (x:Z) (Zplus x x) = (Zmult x (POS (xO xH))).
Intros x; Pattern 1 2 x ; Rewrite <- (Zmult_n_1 x);
Rewrite <- Zmult_plus_distr_r; Auto with arith.
Save.

Theorem Zred_factor2 :
  (x,y:Z) (Zplus x (Zmult x y)) = (Zmult x (Zplus (POS xH) y)).

Intros x y; Pattern 1 x ; Rewrite <- (Zmult_n_1 x);
Rewrite <- Zmult_plus_distr_r; Trivial with arith.
Save.

Theorem Zred_factor3 :
  (x,y:Z) (Zplus (Zmult x y) x) = (Zmult x (Zplus (POS xH) y)).

Intros x y; Pattern 2 x ; Rewrite <- (Zmult_n_1 x);
Rewrite <- Zmult_plus_distr_r; Rewrite Zplus_sym; Trivial with arith.
Save.
Theorem Zred_factor4 :
  (x,y,z:Z) (Zplus (Zmult x y) (Zmult x z)) = (Zmult x (Zplus y z)).
Intros x y z; Symmetry; Apply Zmult_plus_distr_r.
Save.

Theorem Zred_factor5 : (x,y:Z) (Zplus (Zmult x ZERO) y) = y.

Intros x y; Rewrite <- Zmult_n_O;Auto with arith.
Save.

Theorem Zred_factor6 : (x:Z) x = (Zplus x ZERO).

Intro; Rewrite Zero_right; Trivial with arith.
Save.

Theorem Zcompare_Zplus_compatible2 :
  (r:relation)(x,y,z,t:Z)
    (Zcompare x y) = r -> (Zcompare z t) = r ->
    (Zcompare (Zplus x z) (Zplus y t)) = r.

Intros r x y z t; Case r; [
  Intros H1 H2; Elim (Zcompare_EGAL x y); Elim (Zcompare_EGAL z t);
  Intros H3 H4 H5 H6; Rewrite H3; [ 
    Rewrite H5; [ Elim (Zcompare_EGAL (Zplus y t) (Zplus y t)); Auto with arith | Auto with arith ]
  | Auto with arith ]
| Intros H1 H2; Elim (Zcompare_ANTISYM (Zplus y t) (Zplus x z));
  Intros H3 H4; Apply H3;
  Apply Zcompare_trans_SUPERIEUR with y:=(Zplus y z) ; [
    Rewrite Zcompare_Zplus_compatible;
    Elim (Zcompare_ANTISYM t z); Auto with arith
  | Do 2 Rewrite <- (Zplus_sym z); 
    Rewrite Zcompare_Zplus_compatible;
    Elim (Zcompare_ANTISYM y x); Auto with arith]
| Intros H1 H2;
  Apply Zcompare_trans_SUPERIEUR with y:=(Zplus x t) ; [
    Rewrite Zcompare_Zplus_compatible; Assumption
  | Do 2 Rewrite <- (Zplus_sym t);
    Rewrite Zcompare_Zplus_compatible; Assumption]].
Save.

Lemma add_x_x : (x:positive) (add x x) = (xO x).
Intros p; Apply convert_intro; Simpl; Rewrite convert_add;
Unfold 3 convert ; Simpl; Rewrite ZL6; Trivial with arith.
Save.

Theorem Zcompare_Zmult_compatible : 
   (x:positive)(y,z:Z)
      (Zcompare (Zmult (POS x) y) (Zmult (POS x) z)) = (Zcompare y z).

Induction x; [
  Intros p H y z;
  Cut (POS (xI p))=(Zplus (Zplus (POS p) (POS p)) (POS xH)); [
    Intros E; Rewrite E; Do 4 Rewrite Zmult_plus_distr_l; 
    Do 2 Rewrite Zmult_one;
    Apply Zcompare_Zplus_compatible2; [
      Apply Zcompare_Zplus_compatible2; Apply H
    | Trivial with arith]
  | Simpl; Rewrite (add_x_x p); Trivial with arith]
| Intros p H y z; Cut (POS (xO p))=(Zplus (POS p) (POS p)); [
    Intros E; Rewrite E; Do 2 Rewrite Zmult_plus_distr_l;
      Apply Zcompare_Zplus_compatible2; Apply H
    | Simpl; Rewrite (add_x_x p); Trivial with arith]
  | Intros y z; Do 2 Rewrite Zmult_one; Trivial with arith].
Save.

Theorem Zmult_eq:
  (x,y:Z) ~(x=ZERO) -> (Zmult y x) = ZERO -> y = ZERO.

Intros x y; Case x; [
  Intro; Absurd ZERO=ZERO; Auto with arith
| Intros p H1 H2; Elim (Zcompare_EGAL y ZERO);
  Intros H3 H4; Apply H3; Rewrite <- (Zcompare_Zmult_compatible p);
  Rewrite -> Zero_mult_right; Rewrite -> Zmult_sym;
  Elim (Zcompare_EGAL (Zmult y (POS p)) ZERO); Auto with arith
| Intros p H1 H2; Apply Zopp_intro; Simpl;
  Elim (Zcompare_EGAL (Zopp y) ZERO); Intros H3 H4; Apply H3;
  Rewrite <- (Zcompare_Zmult_compatible p);
  Rewrite -> Zero_mult_right; Rewrite -> Zmult_sym;
  Rewrite -> Zmult_Zopp_left; Simpl;
  Elim (Zcompare_EGAL (Zmult y (NEG p)) ZERO); Auto with arith].
Save.

Theorem Z_eq_mult:
  (x,y:Z)  y = ZERO -> (Zmult y x) = ZERO.
Intros x y H; Rewrite H; Auto with arith.
Save.
Theorem Zmult_le:
  (x,y:Z) (Zgt x ZERO) -> (Zle ZERO (Zmult y x)) -> (Zle ZERO y).

Intros x y; Case x; [
  Simpl; Unfold Zgt ; Simpl; Intros H; Discriminate H
| Intros p H1; Unfold Zle; Rewrite -> Zmult_sym;
  Pattern 1 ZERO ; Rewrite <- (Zero_mult_right (POS p));
  Rewrite  Zcompare_Zmult_compatible; Auto with arith
| Intros p; Unfold Zgt ; Simpl; Intros H; Discriminate H].
Save.

Theorem Zle_mult:
  (x,y:Z) (Zgt x ZERO) -> (Zle ZERO y) -> (Zle ZERO (Zmult y x)).

Intros x y; Case x; [
  Simpl; Unfold Zgt ; Simpl; Intros H; Discriminate H
| Intros p H1; Unfold Zle; Rewrite -> Zmult_sym;
  Pattern 2 ZERO ; Rewrite <- (Zero_mult_right (POS p));
  Rewrite  Zcompare_Zmult_compatible; Auto with arith
| Intros p; Unfold Zgt ; Simpl; Intros H; Discriminate H].
Save.
 
 
Theorem Zmult_lt:
  (x,y:Z) (Zgt x ZERO) -> (Zlt ZERO (Zmult y x)) -> (Zlt ZERO y).

Intros x y; Case x; [
  Simpl; Unfold Zgt ; Simpl; Intros H; Discriminate H
| Intros p H1; Unfold Zlt; Rewrite -> Zmult_sym;
  Pattern 1 ZERO ; Rewrite <- (Zero_mult_right (POS p));
  Rewrite  Zcompare_Zmult_compatible; Auto with arith
| Intros p; Unfold Zgt ; Simpl; Intros H; Discriminate H].
Save.

Theorem Zle_mult_approx:
  (x,y,z:Z) (Zgt x ZERO) -> (Zgt z ZERO) -> (Zle ZERO y) -> 
    (Zle ZERO (Zplus (Zmult y x) z)).

Intros x y z H1 H2 H3; Apply Zle_trans with m:=(Zmult y x) ; [
  Apply Zle_mult; Assumption
| Pattern 1 (Zmult y x) ; Rewrite <- Zero_right; Apply Zle_reg_l;
  Apply Zlt_le_weak; Apply Zgt_lt; Assumption].

Save.

Theorem Zmult_le_approx:
  (x,y,z:Z) (Zgt x ZERO) -> (Zgt x z) -> 
    (Zle ZERO (Zplus (Zmult y x) z)) -> (Zle ZERO y).

Intros x y z H1 H2 H3; Apply Zlt_n_Sm_le; Apply (Zmult_lt x); [
  Assumption
  | Apply Zle_lt_trans with 1:=H3 ; Rewrite <- Zmult_Sm_n;
    Apply Zlt_reg_l; Apply Zgt_lt; Assumption].

Save.

Theorem OMEGA1 : (x,y:Z) (x=y) -> (Zle ZERO x) -> (Zle ZERO y).
Intros x y H; Rewrite H; Auto with arith.
Save.

Theorem OMEGA2 : (x,y:Z) (Zle ZERO x) -> (Zle ZERO y) -> (Zle ZERO (Zplus x y)).
Intros x y H1 H2;Rewrite <- (Zero_left ZERO); Apply Zle_plus_plus; Assumption.
Save. 

Theorem OMEGA3 : (x,y,k:Z)(Zgt k ZERO)-> (x=(Zmult y k)) -> (x=ZERO) -> (y=ZERO).

Intros x y k H1 H2 H3; Apply (Zmult_eq k); [
  Unfold not ; Intros H4; Absurd (Zgt k ZERO); [
    Rewrite H4; Unfold Zgt ; Simpl; Discriminate | Assumption]
  | Rewrite <- H2; Assumption].
Save.

Theorem OMEGA4 :
  (x,y,z:Z)(Zgt x ZERO) -> (Zgt y x) -> ~(Zplus (Zmult z y) x) = ZERO.

Unfold not ; Intros x y z H1 H2 H3; Cut (Zgt y ZERO); [
  Intros H4; Cut (Zle ZERO (Zplus (Zmult z y) x)); [
    Intros H5; Generalize (Zmult_le_approx y z x H4 H2 H5) ; Intros H6;
    Absurd (Zgt (Zplus (Zmult z y) x) ZERO); [
      Rewrite -> H3; Unfold Zgt ; Simpl; Discriminate
    | Apply Zle_gt_trans with x ; [
        Pattern 1 x ; Rewrite <- (Zero_left x); Apply Zle_reg_r;
        Rewrite -> Zmult_sym; Generalize H4 ; Unfold Zgt;
        Case y; [
          Simpl; Intros H7; Discriminate H7
        | Intros p H7; Rewrite <- (Zero_mult_right (POS p));
          Unfold Zle ; Rewrite -> Zcompare_Zmult_compatible; Exact H6
        | Simpl; Intros p H7; Discriminate H7]
      | Assumption]]
    | Rewrite -> H3; Unfold Zle ; Simpl; Discriminate]
  | Apply Zgt_trans with x ; [ Assumption | Assumption]].
Save.

Theorem OMEGA5: (x,y,z:Z)(x=ZERO) -> (y=ZERO) -> (Zplus x (Zmult y z)) = ZERO.

Intros x y z H1 H2; Rewrite H1; Rewrite H2; Simpl; Trivial with arith.
Save.
Theorem OMEGA6:
  (x,y,z:Z)(Zle ZERO x) -> (y=ZERO) -> (Zle ZERO (Zplus x (Zmult y z))).

Intros x y z H1 H2; Rewrite H2; Simpl; Rewrite Zero_right; Assumption.
Save.

Theorem OMEGA7:
  (x,y,z,t:Z)(Zgt z ZERO) -> (Zgt t ZERO) -> (Zle ZERO x) -> (Zle ZERO y) -> 
    (Zle ZERO (Zplus (Zmult x z) (Zmult y t))).

Intros x y z t H1 H2 H3 H4; Rewrite <- (Zero_left ZERO);
Apply Zle_plus_plus; Apply Zle_mult; Assumption.
Save.

Theorem OMEGA8: (x,y:Z) (Zle ZERO x) -> (Zle ZERO y) -> x = (Zopp y) -> x = ZERO.

Intros x y H1 H2 H3; Elim (Zle_lt_or_eq ZERO x H1); [
  Intros H4; Absurd (Zlt ZERO x); [
    Change (Zge ZERO x); Apply Zle_ge; Apply (Zsimpl_le_plus_l y);
    Rewrite -> H3; Rewrite Zplus_inverse_r; Rewrite Zero_right; Assumption
  | Assumption]
| Intros H4; Rewrite -> H4; Trivial with arith].
Save.

Theorem OMEGA9:(x,y,z,t:Z) y=ZERO -> x = z -> 
  (Zplus y (Zmult (Zplus (Zopp x) z) t)) = ZERO.

Intros x y z t H1 H2; Rewrite H2; Rewrite Zplus_inverse_l; 
Rewrite Zero_mult_left;  Rewrite Zero_right; Assumption.
Save.
Theorem OMEGA10:(v,c1,c2,l1,l2,k1,k2:Z)
  (Zplus (Zmult (Zplus (Zmult v c1) l1) k1) (Zmult (Zplus (Zmult v c2) l2) k2))
  = (Zplus (Zmult v (Zplus (Zmult c1 k1) (Zmult c2 k2)))
           (Zplus (Zmult l1 k1) (Zmult l2 k2))).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; 
Rewrite (Zplus_permute (Zmult l1 k1) (Zmult (Zmult v c2) k2)); Trivial with arith.
Save.

Theorem OMEGA11:(v1,c1,l1,l2,k1:Z)
  (Zplus (Zmult (Zplus (Zmult v1 c1) l1) k1) l2)
  = (Zplus (Zmult v1 (Zmult c1 k1)) (Zplus (Zmult l1 k1) l2)).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; Trivial with arith.
Save.

Theorem OMEGA12:(v2,c2,l1,l2,k2:Z)
  (Zplus l1 (Zmult (Zplus (Zmult v2 c2) l2) k2))
  = (Zplus (Zmult v2 (Zmult c2 k2)) (Zplus l1 (Zmult l2 k2))).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; Rewrite Zplus_permute;
Trivial with arith.
Save.

Theorem OMEGA13:(v,l1,l2:Z)(x:positive)
  (Zplus (Zplus (Zmult v (POS x)) l1) (Zplus (Zmult v (NEG x)) l2))
  = (Zplus l1 l2).

Intros; Rewrite  Zplus_assoc; Rewrite (Zplus_sym (Zmult v (POS x)) l1);
Rewrite (Zplus_assoc_r l1); Rewrite <- Zmult_plus_distr_r;
Rewrite <- Zopp_NEG; Rewrite (Zplus_sym (Zopp (NEG x)) (NEG x));
Rewrite Zplus_inverse_r; Rewrite  Zero_mult_right; Rewrite Zero_right; Trivial with arith.
Save.
 
Theorem OMEGA14:(v,l1,l2:Z)(x:positive)
  (Zplus (Zplus (Zmult v (NEG x)) l1) (Zplus (Zmult v (POS x)) l2))
  = (Zplus l1 l2).

Intros; Rewrite  Zplus_assoc; Rewrite (Zplus_sym (Zmult v (NEG x)) l1);
Rewrite (Zplus_assoc_r l1); Rewrite <- Zmult_plus_distr_r;
Rewrite <- Zopp_NEG; Rewrite  Zplus_inverse_r; Rewrite  Zero_mult_right;
Rewrite Zero_right; Trivial with arith.
Save.
Theorem OMEGA15:(v,c1,c2,l1,l2,k2:Z)
  (Zplus (Zplus (Zmult v c1) l1) (Zmult (Zplus (Zmult v c2) l2) k2))
  = (Zplus (Zmult v (Zplus c1  (Zmult c2 k2)))
           (Zplus l1 (Zmult l2 k2))).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; 
Rewrite (Zplus_permute l1 (Zmult (Zmult v c2) k2)); Trivial with arith.
Save.

Theorem OMEGA16:
  (v,c,l,k:Z)
   (Zmult (Zplus (Zmult v c) l) k) = (Zplus (Zmult v (Zmult c k)) (Zmult l k)).

Intros; Repeat (Rewrite Zmult_plus_distr_l Orelse Rewrite Zmult_plus_distr_r);
Repeat Rewrite Zmult_assoc; Repeat Elim Zplus_assoc; Trivial with arith.
Save.

Theorem OMEGA17: 
  (x,y,z:Z)(Zne x ZERO) -> (y=ZERO) -> (Zne (Zplus x (Zmult y z)) ZERO).

Unfold Zne not; Intros x y z H1 H2 H3; Apply H1; 
Apply Zsimpl_plus_l with (Zmult y z); Rewrite Zplus_sym; Rewrite H3; 
Rewrite H2; Auto with arith.
Save.

Theorem OMEGA18:
(x,y,k:Z) (x=(Zmult y k)) -> (Zne x ZERO) -> (Zne y ZERO).

Unfold Zne not; Intros x y k H1 H2 H3; Apply H2; Rewrite H1; Rewrite H3; Auto with arith.
Save.

Theorem OMEGA19:
  (x:Z) (Zne x ZERO) -> 
    (Zle ZERO (Zplus x (NEG xH))) \/ (Zle ZERO (Zplus (Zmult x (NEG xH)) (NEG xH))).

Unfold Zne ; Intros x H; Elim (Zle_or_lt ZERO x); [
  Intros H1; Elim Zle_lt_or_eq with 1:=H1; [
    Intros H2; Left;  Change (Zle ZERO (Zpred x)); Apply Zle_S_n;
    Rewrite <- Zs_pred; Apply Zlt_le_S; Assumption
  | Intros H2; Absurd x=ZERO; Auto with arith]
| Intros H1; Right; Rewrite <- Zopp_one; Rewrite Zplus_sym;
  Apply Zle_left; Apply Zle_S_n; Simpl; Apply Zlt_le_S; Auto with arith].
Save.

Theorem OMEGA20:
  (x,y,z:Z)(Zne x  ZERO) -> (y=ZERO) -> (Zne (Zplus x (Zmult y z)) ZERO).

Unfold Zne not; Intros x y z H1 H2 H3; Apply H1; Rewrite H2 in H3;
Simpl in H3; Rewrite (Zero_right x) in H3; Trivial with arith.
Save.

Definition fast_Zplus_sym := 
[x,y:Z][P:Z -> Prop][H: (P (Zplus y x))]
  (eq_ind_r Z (Zplus y x) P H (Zplus x y) (Zplus_sym x y)).

Definition fast_Zplus_assoc_r :=
[n,m,p:Z][P:Z -> Prop][H : (P (Zplus n (Zplus m p)))]
 (eq_ind_r Z (Zplus n (Zplus m p)) P H (Zplus (Zplus n m) p) (Zplus_assoc_r n m p)).

Definition fast_Zplus_assoc_l :=
[n,m,p:Z][P:Z -> Prop][H : (P (Zplus (Zplus n m) p))]
 (eq_ind_r Z (Zplus (Zplus n m) p) P H (Zplus n (Zplus m p)) 
           (Zplus_assoc_l n m p)).

Definition fast_Zplus_permute :=
[n,m,p:Z][P:Z -> Prop][H : (P (Zplus m (Zplus n p)))]
 (eq_ind_r Z (Zplus m (Zplus n p)) P H (Zplus n (Zplus m p))
           (Zplus_permute n m p)).

Definition fast_OMEGA10 := 
[v,c1,c2,l1,l2,k1,k2:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v (Zplus (Zmult c1 k1) (Zmult c2 k2)))
               (Zplus (Zmult l1 k1) (Zmult l2 k2))))]
 (eq_ind_r Z 
           (Zplus (Zmult v (Zplus (Zmult c1 k1) (Zmult c2 k2)))
            (Zplus (Zmult l1 k1) (Zmult l2 k2)))
           P H 
          (Zplus (Zmult (Zplus (Zmult v c1) l1) k1)
                 (Zmult (Zplus (Zmult v c2) l2) k2))
        (OMEGA10 v c1 c2 l1 l2 k1 k2)).

Definition fast_OMEGA11 := 
[v1,c1,l1,l2,k1:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v1 (Zmult c1 k1)) (Zplus (Zmult l1 k1) l2)))]
 (eq_ind_r Z 
   (Zplus (Zmult v1 (Zmult c1 k1)) (Zplus (Zmult l1 k1) l2))
   P H 
   (Zplus (Zmult (Zplus (Zmult v1 c1) l1) k1) l2)
   (OMEGA11 v1 c1 l1 l2 k1)).
Definition fast_OMEGA12 := 
[v2,c2,l1,l2,k2:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v2 (Zmult c2 k2)) (Zplus l1 (Zmult l2 k2))))]
 (eq_ind_r Z 
   (Zplus (Zmult v2 (Zmult c2 k2)) (Zplus l1 (Zmult l2 k2)))
   P H 
   (Zplus l1 (Zmult (Zplus (Zmult v2 c2) l2) k2))
   (OMEGA12 v2 c2 l1 l2 k2)).

Definition fast_OMEGA15 :=
[v,c1,c2,l1,l2,k2 :Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v (Zplus c1 (Zmult c2 k2))) (Zplus l1 (Zmult l2 k2))))]
 (eq_ind_r Z 
   (Zplus (Zmult v (Zplus c1 (Zmult c2 k2))) (Zplus l1 (Zmult l2 k2)))
   P H 
   (Zplus (Zplus (Zmult v c1) l1) (Zmult (Zplus (Zmult v c2) l2) k2))
   (OMEGA15 v c1 c2 l1 l2 k2)).
Definition fast_OMEGA16 :=
[v,c,l,k :Z][P:Z -> Prop]
[H : (P (Zplus (Zmult v (Zmult c k)) (Zmult l k)))]
 (eq_ind_r Z 
   (Zplus (Zmult v (Zmult c k)) (Zmult l k))
   P H 
   (Zmult (Zplus (Zmult v c) l) k)
   (OMEGA16 v c l k)).

Definition fast_OMEGA13 :=
[v,l1,l2 :Z][x:positive][P:Z -> Prop]
[H : (P (Zplus l1 l2))]
 (eq_ind_r Z 
   (Zplus l1 l2)
   P H 
   (Zplus (Zplus (Zmult v (POS x)) l1) (Zplus (Zmult v (NEG x)) l2))
   (OMEGA13 v l1 l2 x )).

Definition fast_OMEGA14 :=
[v,l1,l2 :Z][x:positive][P:Z -> Prop]
[H : (P (Zplus l1 l2))]
 (eq_ind_r Z 
   (Zplus l1 l2)
   P H 
   (Zplus (Zplus (Zmult v (NEG x)) l1) (Zplus (Zmult v (POS x)) l2))
   (OMEGA14 v l1 l2 x )).
Definition fast_Zred_factor0:=
[x:Z][P:Z -> Prop]
[H : (P (Zmult x (POS xH)) )]
 (eq_ind_r Z 
   (Zmult x (POS xH))
   P H 
   x
   (Zred_factor0 x)).

Definition fast_Zopp_one :=
[x:Z][P:Z -> Prop]
[H : (P (Zmult x (NEG xH)))]
 (eq_ind_r Z 
   (Zmult x (NEG xH))
   P H 
   (Zopp x)
   (Zopp_one x)).

Definition fast_Zmult_sym :=
[x,y :Z][P:Z -> Prop]
[H : (P (Zmult y x))]
 (eq_ind_r Z 
(Zmult y x)
   P H 
(Zmult x y)
   (Zmult_sym x y )).

Definition fast_Zopp_Zplus :=
[x,y :Z][P:Z -> Prop]
[H : (P (Zplus (Zopp x) (Zopp y)) )]
 (eq_ind_r Z 
   (Zplus (Zopp x) (Zopp y))
   P H 
   (Zopp (Zplus x y))
   (Zopp_Zplus x y )).

Definition fast_Zopp_Zopp :=
[x:Z][P:Z -> Prop]
[H : (P x )] (eq_ind_r Z x P H (Zopp (Zopp x)) (Zopp_Zopp x)).

Definition fast_Zopp_Zmult_r :=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zopp y)))]
 (eq_ind_r Z 
   (Zmult x (Zopp y))
   P H 
   (Zopp (Zmult x y))
   (Zopp_Zmult_r x y )).

Definition fast_Zmult_plus_distr :=
[n,m,p:Z][P:Z -> Prop]
[H : (P (Zplus (Zmult n p) (Zmult m p)))]
 (eq_ind_r Z 
   (Zplus (Zmult n p) (Zmult m p))
   P H 
   (Zmult (Zplus n m) p)
   (Zmult_plus_distr_l n m p)).
Definition fast_Zmult_Zopp_left:=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zopp y)))]
 (eq_ind_r Z 
   (Zmult x (Zopp y))
   P H 
   (Zmult (Zopp x) y)
   (Zmult_Zopp_left x y)).

Definition fast_Zmult_assoc_r :=
[n,m,p :Z][P:Z -> Prop]
[H : (P (Zmult n (Zmult m p)))]
 (eq_ind_r Z 
   (Zmult n (Zmult m p))
   P H 
   (Zmult (Zmult n m) p)
   (Zmult_assoc_r n m p)).

Definition fast_Zred_factor1 :=
[x:Z][P:Z -> Prop]
[H : (P (Zmult x (POS (xO xH))) )]
 (eq_ind_r Z 
   (Zmult x (POS (xO xH)))
   P H 
   (Zplus x x)
   (Zred_factor1 x)).

Definition fast_Zred_factor2 :=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zplus (POS xH) y)))]
 (eq_ind_r Z 
   (Zmult x (Zplus (POS xH) y))
   P H 
   (Zplus x (Zmult x y))
   (Zred_factor2 x y)).
Definition fast_Zred_factor3 :=
[x,y:Z][P:Z -> Prop]
[H : (P (Zmult x (Zplus (POS xH) y)))]
 (eq_ind_r Z 
   (Zmult x (Zplus (POS xH) y))
   P H 
   (Zplus (Zmult x y) x)
   (Zred_factor3 x y)).

Definition fast_Zred_factor4 :=
[x,y,z:Z][P:Z -> Prop]
[H : (P (Zmult x (Zplus y z)))]
 (eq_ind_r Z 
   (Zmult x (Zplus y z))
   P H 
   (Zplus (Zmult x y) (Zmult x z))
   (Zred_factor4 x y z)).

Definition fast_Zred_factor5 :=
[x,y:Z][P:Z -> Prop]
[H : (P y)]
 (eq_ind_r Z 
   y
   P H 
   (Zplus (Zmult x ZERO) y)
   (Zred_factor5 x y)).

Definition fast_Zred_factor6 :=
[x :Z][P:Z -> Prop]
[H : (P(Zplus x ZERO) )]
 (eq_ind_r Z 
   (Zplus x ZERO)
   P H 
   x
   (Zred_factor6 x )).

