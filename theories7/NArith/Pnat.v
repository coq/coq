(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require BinPos.

(**********************************************************************)
(** Properties of the injection from binary positive numbers to Peano 
    natural numbers *)

(** Original development by Pierre Crégut, CNET, Lannion, France *)

Require Le.
Require Lt.
Require Gt.
Require Plus.
Require Mult.
Require Minus.

(** [nat_of_P] is a morphism for addition *)

Lemma convert_add_un :
  (x:positive)(m:nat)
    (positive_to_nat (add_un x) m) = (plus m (positive_to_nat x m)).
Proof.
Intro x; NewInduction x as [p IHp|p IHp|]; Simpl; Auto; Intro m; Rewrite IHp;
Rewrite plus_assoc_l; Trivial.
Qed.

Lemma cvt_add_un :
  (p:positive) (convert (add_un p)) = (S (convert p)).
Proof.
  Intro; Change (S (convert p)) with (plus (S O) (convert p));
  Unfold convert; Apply convert_add_un.
Qed.

Theorem convert_add_carry :
  (x,y:positive)(m:nat)
    (positive_to_nat (add_carry x y) m) =
    (plus m (positive_to_nat (add x y) m)).
Proof.
Intro x; NewInduction x as [p IHp|p IHp|];
  Intro y; NewDestruct y; Simpl; Auto with arith; Intro m; [
  Rewrite IHp; Rewrite plus_assoc_l; Trivial with arith
| Rewrite IHp; Rewrite plus_assoc_l; Trivial with arith
| Rewrite convert_add_un; Rewrite plus_assoc_l; Trivial with arith
| Rewrite convert_add_un; Apply plus_assoc_r ].
Qed.

Theorem cvt_carry :
  (x,y:positive)(convert (add_carry x y)) = (S (convert (add x y))).
Proof.
Intros;Unfold convert; Rewrite convert_add_carry; Simpl; Trivial with arith.
Qed.

Theorem add_verif :
  (x,y:positive)(m:nat)
    (positive_to_nat (add x y) m) = 
    (plus (positive_to_nat x m) (positive_to_nat y m)).
Proof.
Intro x; NewInduction x as [p IHp|p IHp|];
  Intro y; NewDestruct y;Simpl;Auto with arith; [
  Intros m;Rewrite convert_add_carry; Rewrite IHp; 
  Rewrite plus_assoc_r; Rewrite plus_assoc_r; 
  Rewrite (plus_permute m (positive_to_nat p (plus m m))); Trivial with arith
| Intros m; Rewrite IHp; Apply plus_assoc_l
| Intros m; Rewrite convert_add_un; 
  Rewrite (plus_sym (plus m (positive_to_nat p (plus m m))));
  Apply plus_assoc_r
| Intros m; Rewrite IHp; Apply plus_permute
| Intros m; Rewrite convert_add_un; Apply plus_assoc_r ].
Qed.

Theorem convert_add:
  (x,y:positive) (convert (add x y)) = (plus (convert x) (convert y)).
Proof.
Intros x y; Exact (add_verif x y (S O)).
Qed.

(** [Pmult_nat] is a morphism for addition *)

Lemma ZL2:
  (y:positive)(m:nat)
    (positive_to_nat y (plus m m)) =
              (plus (positive_to_nat y m) (positive_to_nat y m)).
Proof.
Intro y; NewInduction y as [p H|p H|]; Intro m; [
  Simpl; Rewrite H; Rewrite plus_assoc_r; 
  Rewrite (plus_permute m (positive_to_nat p (plus m m)));
  Rewrite plus_assoc_r; Auto with arith
| Simpl; Rewrite H; Auto with arith
| Simpl; Trivial with arith ].
Qed.

Lemma ZL6:
  (p:positive) (positive_to_nat p (S (S O))) = (plus (convert p) (convert p)).
Proof.
Intro p;Change (2) with (plus (S O) (S O)); Rewrite ZL2; Trivial.
Qed.
 
(** [nat_of_P] is a morphism for multiplication *)

Theorem times_convert :
  (x,y:positive) (convert (times x y)) = (mult (convert x) (convert y)).
Proof.
Intros x y; NewInduction x as [ x' H | x' H | ]; [
  Change (times (xI x') y) with (add y (xO (times x' y))); Rewrite convert_add;
  Unfold 2 3 convert; Simpl; Do 2 Rewrite ZL6; Rewrite H;
  Rewrite -> mult_plus_distr; Reflexivity
| Unfold 1 2 convert; Simpl; Do 2 Rewrite ZL6;
  Rewrite H; Rewrite mult_plus_distr; Reflexivity
| Simpl; Rewrite <- plus_n_O; Reflexivity ].
Qed.
V7only [
  Comments "Compatibility with the old version of times and times_convert".
  Syntactic Definition times1 :=
    [x:positive;_:positive->positive;y:positive](times x y).
  Syntactic Definition times1_convert :=
    [x,y:positive;_:positive->positive](times_convert x y).
].

(** [nat_of_P] maps to the strictly positive subset of [nat] *)

Lemma ZL4: (y:positive) (EX h:nat |(convert y)=(S h)).
Proof.
Intro y; NewInduction y as [p H|p H|]; [
  NewDestruct H as [x H1]; Exists (plus (S x) (S x));
  Unfold convert ;Simpl; Change (2) with (plus (1) (1)); Rewrite ZL2; Unfold convert in H1;
  Rewrite H1; Auto with arith
| NewDestruct H as [x H2]; Exists (plus x (S x)); Unfold convert;
  Simpl; Change (2) with (plus (1) (1)); Rewrite ZL2;Unfold convert in H2; Rewrite H2; Auto with arith
| Exists O ;Auto with arith ].
Qed.

(** Extra lemmas on [lt] on Peano natural numbers *)

Lemma ZL7:
  (m,n:nat) (lt m n) -> (lt (plus m m) (plus n n)).
Proof.
Intros m n H; Apply lt_trans with m:=(plus m n); [
  Apply lt_reg_l with 1:=H
| Rewrite (plus_sym m n); Apply lt_reg_l with 1:=H ].
Qed.

Lemma ZL8:
  (m,n:nat) (lt m n) -> (lt (S (plus m m)) (plus n n)).
Proof.
Intros m n H; Apply le_lt_trans with m:=(plus m n); [
  Change (lt (plus m m) (plus m n)) ; Apply lt_reg_l with 1:=H
| Rewrite (plus_sym m n); Apply lt_reg_l with 1:=H ].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [lt] (expressed
    from [compare] on [positive])

    Part 1: [lt] on [positive] is finer than [lt] on [nat]
*)

Lemma compare_convert_INFERIEUR : 
  (x,y:positive) (compare x y EGAL) = INFERIEUR -> 
    (lt (convert x) (convert y)).
Proof.
Intro x; NewInduction x as [p H|p H|];Intro y; NewDestruct y as [q|q|];
  Intro H2; [
  Unfold convert ;Simpl; Apply lt_n_S; 
  Do 2 Rewrite ZL6; Apply ZL7; Apply H; Simpl in H2; Assumption
| Unfold convert ;Simpl; Do 2 Rewrite ZL6; 
  Apply ZL8; Apply H;Simpl in H2; Apply ZLSI;Assumption
| Simpl; Discriminate H2
| Simpl; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Elim (ZLII p q H2); [
    Intros H3;Apply lt_S;Apply ZL7; Apply H;Apply H3
  | Intros E;Rewrite E;Apply lt_n_Sn]
| Simpl; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply ZL7;Apply H;Assumption
| Simpl; Discriminate H2
| Unfold convert ;Simpl; Apply lt_n_S; Rewrite ZL6;
  Elim (ZL4 q);Intros h H3; Rewrite H3;Simpl; Apply lt_O_Sn
| Unfold convert ;Simpl; Rewrite ZL6; Elim (ZL4 q);Intros h H3;
  Rewrite H3; Simpl; Rewrite <- plus_n_Sm; Apply lt_n_S; Apply lt_O_Sn
| Simpl; Discriminate H2 ].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [gt] (expressed
    from [compare] on [positive])

    Part 1: [gt] on [positive] is finer than [gt] on [nat]
*)

Lemma compare_convert_SUPERIEUR : 
  (x,y:positive) (compare x y EGAL)=SUPERIEUR -> (gt (convert x) (convert y)).
Proof.
Unfold gt; Intro x; NewInduction x as [p H|p H|];
  Intro y; NewDestruct y as [q|q|]; Intro H2; [
  Simpl; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply lt_n_S; Apply ZL7; Apply H;Assumption
| Simpl; Unfold convert ;Simpl; Do 2 Rewrite ZL6;
  Elim (ZLSS p q H2); [
    Intros H3;Apply lt_S;Apply ZL7;Apply H;Assumption
  | Intros E;Rewrite E;Apply lt_n_Sn]
| Unfold convert ;Simpl; Rewrite ZL6;Elim (ZL4 p);
  Intros h H3;Rewrite H3;Simpl; Apply lt_n_S; Apply lt_O_Sn
| Simpl;Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply ZL8; Apply H; Apply ZLIS; Assumption
| Simpl; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply ZL7;Apply H;Assumption
| Unfold convert ;Simpl; Rewrite ZL6; Elim (ZL4 p);
  Intros h H3;Rewrite H3;Simpl; Rewrite <- plus_n_Sm;Apply lt_n_S;
  Apply lt_O_Sn
| Simpl; Discriminate H2
| Simpl; Discriminate H2
| Simpl; Discriminate H2 ].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [lt] (expressed
    from [compare] on [positive])

    Part 2: [lt] on [nat] is finer than [lt] on [positive]
*)

Lemma convert_compare_INFERIEUR : 
  (x,y:positive)(lt (convert x) (convert y)) -> (compare x y EGAL) = INFERIEUR.
Proof.
Intros x y; Unfold gt; Elim (Dcompare (compare x y EGAL)); [
  Intros E; Rewrite (compare_convert_EGAL x y E); 
  Intros H;Absurd (lt (convert y) (convert y)); [ Apply lt_n_n | Assumption ]
| Intros H;Elim H; [
    Auto
  | Intros H1 H2; Absurd (lt (convert x) (convert y)); [
      Apply lt_not_sym; Change (gt (convert x) (convert y)); 
      Apply compare_convert_SUPERIEUR; Assumption
    | Assumption ]]].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [gt] (expressed
    from [compare] on [positive])

    Part 2: [gt] on [nat] is finer than [gt] on [positive]
*)

Lemma convert_compare_SUPERIEUR : 
  (x,y:positive)(gt (convert x) (convert y)) -> (compare x y EGAL) = SUPERIEUR.
Proof.
Intros x y; Unfold gt; Elim (Dcompare (compare x y EGAL)); [
  Intros E; Rewrite (compare_convert_EGAL x y E); 
  Intros H;Absurd (lt (convert y) (convert y)); [ Apply lt_n_n | Assumption ]
| Intros H;Elim H; [
    Intros H1 H2; Absurd (lt (convert y) (convert x)); [
      Apply lt_not_sym; Apply compare_convert_INFERIEUR; Assumption
    | Assumption ]
  | Auto]].
Qed.

(** [nat_of_P] is strictly positive *)

Lemma compare_positive_to_nat_O : 
	(p:positive)(m:nat)(le m (positive_to_nat p m)).
NewInduction p; Simpl; Auto with arith.
Intro m; Apply le_trans with (plus m m);  Auto with arith.
Qed.

Lemma compare_convert_O : (p:positive)(lt O (convert p)).
Intro; Unfold convert; Apply lt_le_trans with (S O); Auto with arith.
Apply compare_positive_to_nat_O.
Qed.

(** Pmult_nat permutes with multiplication *)

Lemma positive_to_nat_mult : (p:positive) (n,m:nat)
    (positive_to_nat p (mult m n))=(mult m (positive_to_nat p n)).
Proof.
  Induction p. Intros. Simpl. Rewrite mult_plus_distr_r. Rewrite <- (mult_plus_distr_r m n n).
  Rewrite (H (plus n n) m). Reflexivity.
  Intros. Simpl. Rewrite <- (mult_plus_distr_r m n n). Apply H.
  Trivial.
Qed.

Lemma positive_to_nat_2 : (p:positive)
    (positive_to_nat p (2))=(mult (2) (positive_to_nat p (1))).
Proof.
  Intros. Rewrite <- positive_to_nat_mult. Reflexivity.
Qed.

Lemma positive_to_nat_4 : (p:positive)
    (positive_to_nat p (4))=(mult (2) (positive_to_nat p (2))).
Proof.
  Intros. Rewrite <- positive_to_nat_mult. Reflexivity.
Qed.

(** Mapping of xH, xO and xI through [nat_of_P] *)

Lemma convert_xH : (convert xH)=(1).
Proof.
  Reflexivity.
Qed.

Lemma convert_xO : (p:positive) (convert (xO p))=(mult (2) (convert p)).
Proof.
  Induction p. Unfold convert. Simpl. Intros. Rewrite positive_to_nat_2.
  Rewrite positive_to_nat_4. Rewrite H. Simpl. Rewrite <- plus_Snm_nSm. Reflexivity.
  Unfold convert. Simpl. Intros. Rewrite positive_to_nat_2. Rewrite positive_to_nat_4.
  Rewrite H. Reflexivity.
  Reflexivity.
Qed.

Lemma convert_xI : (p:positive) (convert (xI p))=(S (mult (2) (convert p))).
Proof.
  Induction p. Unfold convert. Simpl. Intro p0. Intro. Rewrite positive_to_nat_2.
  Rewrite positive_to_nat_4; Injection H; Intro H1; Rewrite H1; Rewrite <- plus_Snm_nSm; Reflexivity.
  Unfold convert. Simpl. Intros. Rewrite positive_to_nat_2. Rewrite positive_to_nat_4.
  Injection H; Intro H1; Rewrite H1; Reflexivity.
  Reflexivity.
Qed.

(**********************************************************************)
(** Properties of the shifted injection from Peano natural numbers to 
    binary positive numbers *)

(** Composition of [P_of_succ_nat] and [nat_of_P] is successor on [nat] *)

Theorem bij1 : (m:nat) (convert (anti_convert m)) = (S m).
Proof.
Intro m; NewInduction m as [|n H]; [
  Reflexivity
| Simpl; Rewrite cvt_add_un; Rewrite H; Auto ].
Qed.

(** Miscellaneous lemmas on [P_of_succ_nat] *)

Lemma ZL3: (x:nat) (add_un (anti_convert (plus x x))) =  (xO (anti_convert x)).
Proof.
Intro x; NewInduction x as [|n H]; [
  Simpl; Auto with arith
| Simpl; Rewrite  plus_sym; Simpl; Rewrite  H; Rewrite  ZL1;Auto with arith].
Qed.

Lemma ZL5: (x:nat) (anti_convert (plus (S x) (S x))) =  (xI (anti_convert x)).
Proof.
Intro x; NewInduction x as [|n H];Simpl; [
  Auto with arith
| Rewrite <- plus_n_Sm; Simpl; Simpl in H; Rewrite H; Auto with arith].
Qed.

(** Composition of [nat_of_P] and [P_of_succ_nat] is successor on [positive] *)

Theorem bij2 : (x:positive) (anti_convert (convert x)) = (add_un x).
Proof.
Intro x; NewInduction x as [p H|p H|]; [
  Simpl; Rewrite <- H; Change (2) with (plus (1) (1));
  Rewrite ZL2; Elim (ZL4 p); 
  Unfold convert; Intros n H1;Rewrite H1; Rewrite ZL3; Auto with arith
| Unfold convert ;Simpl; Change (2) with (plus (1) (1));
  Rewrite ZL2;
  Rewrite <- (sub_add_one
               (anti_convert
                 (plus (positive_to_nat p (S O)) (positive_to_nat p (S O)))));
  Rewrite <- (sub_add_one (xI p));
  Simpl;Rewrite <- H;Elim (ZL4 p); Unfold convert ;Intros n H1;Rewrite H1;
  Rewrite ZL5; Simpl; Trivial with arith
| Unfold convert; Simpl; Auto with arith ].
Qed.

(** Composition of [nat_of_P], [P_of_succ_nat] and [Ppred] is identity
    on [positive] *)

Theorem bij3: (x:positive)(sub_un (anti_convert (convert x))) = x.
Proof.
Intros x; Rewrite bij2; Rewrite sub_add_one; Trivial with arith.
Qed.

(**********************************************************************)
(** Extra properties of the injection from binary positive numbers to Peano 
    natural numbers *)

(** [nat_of_P] is a morphism for subtraction on positive numbers *)

Theorem true_sub_convert:
  (x,y:positive) (compare x y EGAL) = SUPERIEUR -> 
     (convert (true_sub x y)) = (minus (convert x) (convert y)).
Proof.
Intros x y H; Apply plus_reg_l with (convert y);
Rewrite le_plus_minus_r; [
  Rewrite <- convert_add; Rewrite sub_add; Auto with arith
| Apply lt_le_weak; Exact (compare_convert_SUPERIEUR x y H)].
Qed.

(** [nat_of_P] is injective *)

Lemma convert_intro : (x,y:positive)(convert x)=(convert y) -> x=y.
Proof.
Intros x y H;Rewrite <- (bij3 x);Rewrite <- (bij3 y); Rewrite H; Trivial with arith.
Qed.

Lemma ZL16: (p,q:positive)(lt (minus (convert p) (convert q)) (convert p)).
Proof.
Intros p q; Elim (ZL4 p);Elim (ZL4 q); Intros h H1 i H2; 
Rewrite H1;Rewrite H2; Simpl;Unfold lt; Apply le_n_S; Apply le_minus.
Qed.

Lemma ZL17: (p,q:positive)(lt (convert p) (convert (add p q))).
Proof.
Intros p q; Rewrite convert_add;Unfold lt;Elim (ZL4 q); Intros k H;Rewrite H;
Rewrite plus_sym;Simpl; Apply le_n_S; Apply le_plus_r.
Qed.

(** Comparison and subtraction *)

Lemma compare_true_sub_right :
  (p,q,z:positive)
  (compare q p EGAL)=INFERIEUR->
  (compare z p EGAL)=SUPERIEUR->
  (compare z q EGAL)=SUPERIEUR->
  (compare (true_sub z p) (true_sub z q) EGAL)=INFERIEUR.
Proof.
Intros; Apply convert_compare_INFERIEUR; Rewrite true_sub_convert; [
  Rewrite true_sub_convert; [
    Apply simpl_lt_plus_l with p:=(convert q); Rewrite le_plus_minus_r; [
      Rewrite plus_sym; Apply simpl_lt_plus_l with p:=(convert p);
        Rewrite plus_assoc_l; Rewrite le_plus_minus_r; [
          Rewrite (plus_sym (convert p)); Apply lt_reg_l;
          Apply compare_convert_INFERIEUR; Assumption 
        | Apply lt_le_weak; Apply compare_convert_INFERIEUR;
          Apply ZC1; Assumption ]
      | Apply lt_le_weak;Apply compare_convert_INFERIEUR;
        Apply ZC1; Assumption ]
    | Assumption ]
  | Assumption ].
Qed.

Lemma compare_true_sub_left :
  (p,q,z:positive)
  (compare q p EGAL)=INFERIEUR->
  (compare p z EGAL)=SUPERIEUR->
  (compare q z EGAL)=SUPERIEUR->
  (compare (true_sub q z) (true_sub p z) EGAL)=INFERIEUR.
Proof.
Intros p q z; Intros; 
  Apply convert_compare_INFERIEUR; Rewrite true_sub_convert; [
  Rewrite true_sub_convert; [
    Unfold gt; Apply simpl_lt_plus_l with p:=(convert z);
    Rewrite le_plus_minus_r; [
      Rewrite le_plus_minus_r; [
        Apply compare_convert_INFERIEUR;Assumption
      | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Apply ZC1;Assumption]
    | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Apply ZC1; Assumption]
  | Assumption]
| Assumption].
Qed.

(** Distributivity of multiplication over subtraction *)

Theorem times_true_sub_distr:
  (x,y,z:positive) (compare y z EGAL) = SUPERIEUR -> 
      (times x (true_sub y z)) = (true_sub (times x y) (times x z)).
Proof.
Intros x y z H; Apply convert_intro;
Rewrite times_convert; Rewrite true_sub_convert; [
  Rewrite true_sub_convert; [
    Do 2 Rewrite times_convert;
    Do 3 Rewrite (mult_sym (convert x));Apply mult_minus_distr
  | Apply convert_compare_SUPERIEUR; Do 2 Rewrite times_convert; 
    Unfold gt; Elim (ZL4 x);Intros h H1;Rewrite H1; Apply lt_mult_left;
    Exact (compare_convert_SUPERIEUR y z H) ]
| Assumption ].
Qed.

