(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(** Definition of finite sets as trees indexed by adresses *)

Require Import Bool.
Require Import Sumbool.
Require Import ZArith.
Require Import Addr.
Require Import Adist.
Require Import Addec.


Section MapDefs.

(** We define maps from ad to A. *)
  Variable A : Set.  

  Inductive Map : Set :=
    | M0 : Map
    | M1 : ad -> A -> Map
    | M2 : Map -> Map -> Map.

  Inductive option : Set :=
    | NONE : option
    | SOME : A -> option.

  Lemma option_sum : forall o:option, {y : A | o = SOME y} + {o = NONE}.
  Proof.
    simple induction o. right. reflexivity.
    left. split with a. reflexivity.
  Qed.

  (** The semantics of maps is given by the function [MapGet].
      The semantics of a map [m] is a partial, finite function from
      [ad] to [A]: *)

  Fixpoint MapGet (m:Map) : ad -> option :=
    match m with
    | M0 => fun a:ad => NONE
    | M1 x y => fun a:ad => if ad_eq x a then SOME y else NONE
    | M2 m1 m2 =>
        fun a:ad =>
          match a with
          | ad_z => MapGet m1 ad_z
          | ad_x xH => MapGet m2 ad_z
          | ad_x (xO p) => MapGet m1 (ad_x p)
          | ad_x (xI p) => MapGet m2 (ad_x p)
          end
    end.

  Definition newMap := M0.

  Definition MapSingleton := M1.

  Definition eqm (g g':ad -> option) := forall a:ad, g a = g' a.

  Lemma newMap_semantics : eqm (MapGet newMap) (fun a:ad => NONE).
  Proof.
    simpl in |- *. unfold eqm in |- *. trivial.
  Qed.

  Lemma MapSingleton_semantics :
   forall (a:ad) (y:A),
     eqm (MapGet (MapSingleton a y))
       (fun a':ad => if ad_eq a a' then SOME y else NONE).
  Proof.
    simpl in |- *. unfold eqm in |- *. trivial.
  Qed.

  Lemma M1_semantics_1 : forall (a:ad) (y:A), MapGet (M1 a y) a = SOME y.
  Proof.
    unfold MapGet in |- *. intros. rewrite (ad_eq_correct a). reflexivity.
  Qed.

  Lemma M1_semantics_2 :
   forall (a a':ad) (y:A), ad_eq a a' = false -> MapGet (M1 a y) a' = NONE.
  Proof.
    intros. simpl in |- *. rewrite H. reflexivity.
  Qed.

  Lemma Map2_semantics_1 :
   forall m m':Map,
     eqm (MapGet m) (fun a:ad => MapGet (M2 m m') (ad_double a)).
  Proof.
    unfold eqm in |- *. simple induction a; trivial.
  Qed.

  Lemma Map2_semantics_1_eq :
   forall (m m':Map) (f:ad -> option),
     eqm (MapGet (M2 m m')) f -> eqm (MapGet m) (fun a:ad => f (ad_double a)).
  Proof.
    unfold eqm in |- *.
    intros.
    rewrite <- (H (ad_double a)).
    exact (Map2_semantics_1 m m' a).
  Qed.

  Lemma Map2_semantics_2 :
   forall m m':Map,
     eqm (MapGet m') (fun a:ad => MapGet (M2 m m') (ad_double_plus_un a)).
  Proof.
    unfold eqm in |- *. simple induction a; trivial.
  Qed.

  Lemma Map2_semantics_2_eq :
   forall (m m':Map) (f:ad -> option),
     eqm (MapGet (M2 m m')) f ->
     eqm (MapGet m') (fun a:ad => f (ad_double_plus_un a)).
  Proof.
    unfold eqm in |- *.
    intros.
    rewrite <- (H (ad_double_plus_un a)).
    exact (Map2_semantics_2 m m' a).
  Qed.

  Lemma MapGet_M2_bit_0_0 :
   forall a:ad,
     ad_bit_0 a = false ->
     forall m m':Map, MapGet (M2 m m') a = MapGet m (ad_div_2 a).
  Proof.
    simple induction a; trivial. simple induction p. intros. discriminate H0.
    trivial.
    intros. discriminate H.
  Qed.

  Lemma MapGet_M2_bit_0_1 :
   forall a:ad,
     ad_bit_0 a = true ->
     forall m m':Map, MapGet (M2 m m') a = MapGet m' (ad_div_2 a).
  Proof.
    simple induction a. intros. discriminate H.
    simple induction p. trivial.
    intros. discriminate H0.
    trivial.
  Qed.

  Lemma MapGet_M2_bit_0_if :
   forall (m m':Map) (a:ad),
     MapGet (M2 m m') a =
     (if ad_bit_0 a then MapGet m' (ad_div_2 a) else MapGet m (ad_div_2 a)).
  Proof.
    intros. elim (sumbool_of_bool (ad_bit_0 a)). intro H. rewrite H.
    apply MapGet_M2_bit_0_1; assumption.
    intro H. rewrite H. apply MapGet_M2_bit_0_0; assumption.
  Qed.

  Lemma MapGet_M2_bit_0 :
   forall (m m' m'':Map) (a:ad),
     (if ad_bit_0 a then MapGet (M2 m' m) a else MapGet (M2 m m'') a) =
     MapGet m (ad_div_2 a).
  Proof.
    intros. elim (sumbool_of_bool (ad_bit_0 a)). intro H. rewrite H.
    apply MapGet_M2_bit_0_1; assumption.
    intro H. rewrite H. apply MapGet_M2_bit_0_0; assumption.
  Qed.

  Lemma Map2_semantics_3 :
   forall m m':Map,
     eqm (MapGet (M2 m m'))
       (fun a:ad =>
          match ad_bit_0 a with
          | false => MapGet m (ad_div_2 a)
          | true => MapGet m' (ad_div_2 a)
          end).
  Proof.
    unfold eqm in |- *.
    simple induction a; trivial.
    simple induction p; trivial.
  Qed.

  Lemma Map2_semantics_3_eq :
   forall (m m':Map) (f f':ad -> option),
     eqm (MapGet m) f ->
     eqm (MapGet m') f' ->
     eqm (MapGet (M2 m m'))
       (fun a:ad =>
          match ad_bit_0 a with
          | false => f (ad_div_2 a)
          | true => f' (ad_div_2 a)
          end).
  Proof.
    unfold eqm in |- *.
    intros.
    rewrite <- (H (ad_div_2 a)).
    rewrite <- (H0 (ad_div_2 a)).
    exact (Map2_semantics_3 m m' a).
  Qed.

  Fixpoint MapPut1 (a:ad) (y:A) (a':ad) (y':A) (p:positive) {struct p} :
   Map :=
    match p with
    | xO p' =>
        let m := MapPut1 (ad_div_2 a) y (ad_div_2 a') y' p' in
        match ad_bit_0 a with
        | false => M2 m M0
        | true => M2 M0 m
        end
    | _ =>
        match ad_bit_0 a with
        | false => M2 (M1 (ad_div_2 a) y) (M1 (ad_div_2 a') y')
        | true => M2 (M1 (ad_div_2 a') y') (M1 (ad_div_2 a) y)
        end
    end.

  Lemma MapGet_if_commute :
   forall (b:bool) (m m':Map) (a:ad),
     MapGet (if b then m else m') a = (if b then MapGet m a else MapGet m' a).
  Proof.
    intros. case b; trivial.
  Qed.

  (*i
  Lemma MapGet_M2_bit_0_1' : (m,m',m'',m''':Map)
      (a:ad) (MapGet (if (ad_bit_0 a) then (M2 m m') else (M2 m'' m''')) a)=
             (MapGet (if (ad_bit_0 a) then m' else m'') (ad_div_2 a)).
  Proof.
    Intros. Rewrite (MapGet_if_commute (ad_bit_0 a)). Rewrite (MapGet_if_commute (ad_bit_0 a)).
    Cut (ad_bit_0 a)=false\/(ad_bit_0 a)=true. Intros. Elim H. Intros. Rewrite H0.
    Apply MapGet_M2_bit_0_0. Assumption.
    Intros. Rewrite H0. Apply MapGet_M2_bit_0_1. Assumption.
    Case (ad_bit_0 a); Auto.
  Qed.
  i*)

  Lemma MapGet_if_same :
   forall (m:Map) (b:bool) (a:ad), MapGet (if b then m else m) a = MapGet m a.
  Proof.
    simple induction b; trivial.
  Qed.

  Lemma MapGet_M2_bit_0_2 :
   forall (m m' m'':Map) (a:ad),
     MapGet (if ad_bit_0 a then M2 m m' else M2 m' m'') a =
     MapGet m' (ad_div_2 a).
  Proof.
    intros. rewrite MapGet_if_commute. apply MapGet_M2_bit_0.
  Qed.

  Lemma MapPut1_semantics_1 :
   forall (p:positive) (a a':ad) (y y':A),
     ad_xor a a' = ad_x p -> MapGet (MapPut1 a y a' y' p) a = SOME y.
  Proof.
    simple induction p. intros. unfold MapPut1 in |- *. rewrite MapGet_M2_bit_0_2. apply M1_semantics_1.
    intros. simpl in |- *. rewrite MapGet_M2_bit_0_2. apply H. rewrite <- ad_xor_div_2. rewrite H0.
    reflexivity.
    intros. unfold MapPut1 in |- *. rewrite MapGet_M2_bit_0_2. apply M1_semantics_1.
  Qed.

  Lemma MapPut1_semantics_2 :
   forall (p:positive) (a a':ad) (y y':A),
     ad_xor a a' = ad_x p -> MapGet (MapPut1 a y a' y' p) a' = SOME y'.
  Proof.
    simple induction p. intros. unfold MapPut1 in |- *. rewrite (ad_neg_bit_0_2 a a' p0 H0).
    rewrite if_negb. rewrite MapGet_M2_bit_0_2. apply M1_semantics_1.
    intros. simpl in |- *. rewrite (ad_same_bit_0 a a' p0 H0). rewrite MapGet_M2_bit_0_2.
    apply H. rewrite <- ad_xor_div_2. rewrite H0. reflexivity.
    intros. unfold MapPut1 in |- *. rewrite (ad_neg_bit_0_1 a a' H). rewrite if_negb.
    rewrite MapGet_M2_bit_0_2. apply M1_semantics_1.
  Qed.

  Lemma MapGet_M2_both_NONE :
   forall (m m':Map) (a:ad),
     MapGet m (ad_div_2 a) = NONE ->
     MapGet m' (ad_div_2 a) = NONE -> MapGet (M2 m m') a = NONE.
  Proof.
    intros. rewrite (Map2_semantics_3 m m' a). 
    case (ad_bit_0 a); assumption.
  Qed.
 
  Lemma MapPut1_semantics_3 :
   forall (p:positive) (a a' a0:ad) (y y':A),
     ad_xor a a' = ad_x p ->
     ad_eq a a0 = false ->
     ad_eq a' a0 = false -> MapGet (MapPut1 a y a' y' p) a0 = NONE.
  Proof.
    simple induction p. intros. unfold MapPut1 in |- *. elim (ad_neq a a0 H1). intro. rewrite H3. rewrite if_negb.
    rewrite MapGet_M2_bit_0_2. apply M1_semantics_2. apply ad_div_bit_neq. assumption.
    rewrite (ad_neg_bit_0_2 a a' p0 H0) in H3. rewrite (negb_intro (ad_bit_0 a')).
    rewrite (negb_intro (ad_bit_0 a0)). rewrite H3. reflexivity.
    intro. elim (ad_neq a' a0 H2). intro. rewrite (ad_neg_bit_0_2 a a' p0 H0). rewrite H4.
    rewrite (negb_elim (ad_bit_0 a0)). rewrite MapGet_M2_bit_0_2.
    apply M1_semantics_2; assumption.
    intro; case (ad_bit_0 a); apply MapGet_M2_both_NONE; apply M1_semantics_2;
     assumption.
    intros. simpl in |- *. elim (ad_neq a a0 H1). intro. rewrite H3. rewrite if_negb.
    rewrite MapGet_M2_bit_0_2. reflexivity.
    intro. elim (ad_neq a' a0 H2). intro. rewrite (ad_same_bit_0 a a' p0 H0). rewrite H4.
    rewrite if_negb. rewrite MapGet_M2_bit_0_2. reflexivity.
    intro. cut (ad_xor (ad_div_2 a) (ad_div_2 a') = ad_x p0). intro.
    case (ad_bit_0 a); apply MapGet_M2_both_NONE; trivial; apply H;
     assumption.
    rewrite <- ad_xor_div_2. rewrite H0. reflexivity.
    intros. simpl in |- *. elim (ad_neq a a0 H0). intro. rewrite H2. rewrite if_negb.
    rewrite MapGet_M2_bit_0_2. apply M1_semantics_2. apply ad_div_bit_neq. assumption.
    rewrite (ad_neg_bit_0_1 a a' H) in H2. rewrite (negb_intro (ad_bit_0 a')).
    rewrite (negb_intro (ad_bit_0 a0)). rewrite H2. reflexivity.
    intro. elim (ad_neq a' a0 H1). intro. rewrite (ad_neg_bit_0_1 a a' H). rewrite H3.
    rewrite (negb_elim (ad_bit_0 a0)). rewrite MapGet_M2_bit_0_2.
    apply M1_semantics_2; assumption.
    intro. case (ad_bit_0 a); apply MapGet_M2_both_NONE; apply M1_semantics_2;
  assumption.
  Qed.

  Lemma MapPut1_semantics :
   forall (p:positive) (a a':ad) (y y':A),
     ad_xor a a' = ad_x p ->
     eqm (MapGet (MapPut1 a y a' y' p))
       (fun a0:ad =>
          if ad_eq a a0
          then SOME y
          else if ad_eq a' a0 then SOME y' else NONE).
  Proof.
    unfold eqm in |- *. intros. elim (sumbool_of_bool (ad_eq a a0)). intro H0. rewrite H0.
    rewrite <- (ad_eq_complete _ _ H0). exact (MapPut1_semantics_1 p a a' y y' H).
    intro H0. rewrite H0. elim (sumbool_of_bool (ad_eq a' a0)). intro H1.
    rewrite <- (ad_eq_complete _ _ H1). rewrite (ad_eq_correct a').
    exact (MapPut1_semantics_2 p a a' y y' H).
    intro H1. rewrite H1. exact (MapPut1_semantics_3 p a a' a0 y y' H H0 H1).
  Qed.

  Lemma MapPut1_semantics' :
   forall (p:positive) (a a':ad) (y y':A),
     ad_xor a a' = ad_x p ->
     eqm (MapGet (MapPut1 a y a' y' p))
       (fun a0:ad =>
          if ad_eq a' a0
          then SOME y'
          else if ad_eq a a0 then SOME y else NONE).
  Proof.
    unfold eqm in |- *. intros. rewrite (MapPut1_semantics p a a' y y' H a0).
    elim (sumbool_of_bool (ad_eq a a0)). intro H0. rewrite H0.
    rewrite <- (ad_eq_complete a a0 H0). rewrite (ad_eq_comm a' a).
    rewrite (ad_xor_eq_false a a' p H). reflexivity.
    intro H0. rewrite H0. reflexivity.
  Qed.

  Fixpoint MapPut (m:Map) : ad -> A -> Map :=
    match m with
    | M0 => M1
    | M1 a y =>
        fun (a':ad) (y':A) =>
          match ad_xor a a' with
          | ad_z => M1 a' y'
          | ad_x p => MapPut1 a y a' y' p
          end
    | M2 m1 m2 =>
        fun (a:ad) (y:A) =>
          match a with
          | ad_z => M2 (MapPut m1 ad_z y) m2
          | ad_x xH => M2 m1 (MapPut m2 ad_z y)
          | ad_x (xO p) => M2 (MapPut m1 (ad_x p) y) m2
          | ad_x (xI p) => M2 m1 (MapPut m2 (ad_x p) y)
          end
    end.

  Lemma MapPut_semantics_1 :
   forall (a:ad) (y:A) (a0:ad),
     MapGet (MapPut M0 a y) a0 = MapGet (M1 a y) a0.
  Proof.
    trivial.
  Qed.

  Lemma MapPut_semantics_2_1 :
   forall (a:ad) (y y':A) (a0:ad),
     MapGet (MapPut (M1 a y) a y') a0 =
     (if ad_eq a a0 then SOME y' else NONE).
  Proof.
    simpl in |- *. intros. rewrite (ad_xor_nilpotent a). trivial.
  Qed.

  Lemma MapPut_semantics_2_2 :
   forall (a a':ad) (y y':A) (a0 a'':ad),
     ad_xor a a' = a'' ->
     MapGet (MapPut (M1 a y) a' y') a0 =
     (if ad_eq a' a0 then SOME y' else if ad_eq a a0 then SOME y else NONE).
  Proof.
    simple induction a''. intro. rewrite (ad_xor_eq _ _ H). rewrite MapPut_semantics_2_1.
    case (ad_eq a' a0); trivial.
    intros. simpl in |- *. rewrite H. rewrite (MapPut1_semantics p a a' y y' H a0).
    elim (sumbool_of_bool (ad_eq a a0)). intro H0. rewrite H0. rewrite <- (ad_eq_complete _ _ H0).
    rewrite (ad_eq_comm a' a). rewrite (ad_xor_eq_false _ _ _ H). reflexivity.
    intro H0. rewrite H0. reflexivity.
  Qed.

  Lemma MapPut_semantics_2 :
   forall (a a':ad) (y y':A) (a0:ad),
     MapGet (MapPut (M1 a y) a' y') a0 =
     (if ad_eq a' a0 then SOME y' else if ad_eq a a0 then SOME y else NONE).
  Proof.
    intros. apply MapPut_semantics_2_2 with (a'' := ad_xor a a'); trivial.
  Qed.

  Lemma MapPut_semantics_3_1 :
   forall (m m':Map) (a:ad) (y:A),
     MapPut (M2 m m') a y =
     (if ad_bit_0 a
      then M2 m (MapPut m' (ad_div_2 a) y)
      else M2 (MapPut m (ad_div_2 a) y) m').
  Proof.
    simple induction a. trivial.
    simple induction p; trivial.
  Qed.

  Lemma MapPut_semantics :
   forall (m:Map) (a:ad) (y:A),
     eqm (MapGet (MapPut m a y))
       (fun a':ad => if ad_eq a a' then SOME y else MapGet m a').
  Proof.
    unfold eqm in |- *. simple induction m. exact MapPut_semantics_1.
    intros. unfold MapGet at 2 in |- *. apply MapPut_semantics_2; assumption.
    intros. rewrite MapPut_semantics_3_1. rewrite (MapGet_M2_bit_0_if m0 m1 a0).
    elim (sumbool_of_bool (ad_bit_0 a)). intro H1. rewrite H1. rewrite MapGet_M2_bit_0_if.
    elim (sumbool_of_bool (ad_bit_0 a0)). intro H2. rewrite H2.
    rewrite (H0 (ad_div_2 a) y (ad_div_2 a0)). elim (sumbool_of_bool (ad_eq a a0)).
    intro H3. rewrite H3. rewrite (ad_div_eq _ _ H3). reflexivity.
    intro H3. rewrite H3. rewrite <- H2 in H1. rewrite (ad_div_bit_neq _ _ H3 H1). reflexivity.
    intro H2. rewrite H2. rewrite (ad_eq_comm a a0). rewrite (ad_bit_0_neq a0 a H2 H1).
    reflexivity.
    intro H1. rewrite H1. rewrite MapGet_M2_bit_0_if. elim (sumbool_of_bool (ad_bit_0 a0)).
    intro H2. rewrite H2. rewrite (ad_bit_0_neq a a0 H1 H2). reflexivity.
    intro H2. rewrite H2. rewrite (H (ad_div_2 a) y (ad_div_2 a0)).
    elim (sumbool_of_bool (ad_eq a a0)). intro H3. rewrite H3.
    rewrite (ad_div_eq a a0 H3). reflexivity.
    intro H3. rewrite H3. rewrite <- H2 in H1. rewrite (ad_div_bit_neq a a0 H3 H1). reflexivity.
  Qed.

  Fixpoint MapPut_behind (m:Map) : ad -> A -> Map :=
    match m with
    | M0 => M1
    | M1 a y =>
        fun (a':ad) (y':A) =>
          match ad_xor a a' with
          | ad_z => m
          | ad_x p => MapPut1 a y a' y' p
          end
    | M2 m1 m2 =>
        fun (a:ad) (y:A) =>
          match a with
          | ad_z => M2 (MapPut_behind m1 ad_z y) m2
          | ad_x xH => M2 m1 (MapPut_behind m2 ad_z y)
          | ad_x (xO p) => M2 (MapPut_behind m1 (ad_x p) y) m2
          | ad_x (xI p) => M2 m1 (MapPut_behind m2 (ad_x p) y)
          end
    end.

  Lemma MapPut_behind_semantics_3_1 :
   forall (m m':Map) (a:ad) (y:A),
     MapPut_behind (M2 m m') a y =
     (if ad_bit_0 a
      then M2 m (MapPut_behind m' (ad_div_2 a) y)
      else M2 (MapPut_behind m (ad_div_2 a) y) m').
  Proof.
    simple induction a. trivial.
    simple induction p; trivial.
  Qed.

  Lemma MapPut_behind_as_before_1 :
   forall a a' a0:ad,
     ad_eq a' a0 = false ->
     forall y y':A,
       MapGet (MapPut (M1 a y) a' y') a0 =
       MapGet (MapPut_behind (M1 a y) a' y') a0.
  Proof.
    intros a a' a0. simpl in |- *. intros H y y'. elim (ad_sum (ad_xor a a')). intro H0. elim H0.
    intros p H1. rewrite H1. reflexivity.
    intro H0. rewrite H0. rewrite (ad_xor_eq _ _ H0). rewrite (M1_semantics_2 a' a0 y H).
    exact (M1_semantics_2 a' a0 y' H).
  Qed.

  Lemma MapPut_behind_as_before :
   forall (m:Map) (a:ad) (y:A) (a0:ad),
     ad_eq a a0 = false ->
     MapGet (MapPut m a y) a0 = MapGet (MapPut_behind m a y) a0.
  Proof.
    simple induction m. trivial.
    intros a y a' y' a0 H. exact (MapPut_behind_as_before_1 a a' a0 H y y').
    intros. rewrite MapPut_semantics_3_1. rewrite MapPut_behind_semantics_3_1.
    elim (sumbool_of_bool (ad_bit_0 a)). intro H2. rewrite H2. rewrite MapGet_M2_bit_0_if.
    rewrite MapGet_M2_bit_0_if. elim (sumbool_of_bool (ad_bit_0 a0)). intro H3.
    rewrite H3. apply H0. rewrite <- H3 in H2. exact (ad_div_bit_neq a a0 H1 H2).
    intro H3. rewrite H3. reflexivity.
    intro H2. rewrite H2. rewrite MapGet_M2_bit_0_if. rewrite MapGet_M2_bit_0_if.
    elim (sumbool_of_bool (ad_bit_0 a0)). intro H3. rewrite H3. reflexivity.
    intro H3. rewrite H3. apply H. rewrite <- H3 in H2. exact (ad_div_bit_neq a a0 H1 H2).
  Qed.

  Lemma MapPut_behind_new :
   forall (m:Map) (a:ad) (y:A),
     MapGet (MapPut_behind m a y) a =
     match MapGet m a with
     | SOME y' => SOME y'
     | _ => SOME y
     end.
  Proof.
    simple induction m. simpl in |- *. intros. rewrite (ad_eq_correct a). reflexivity.
    intros. elim (ad_sum (ad_xor a a1)). intro H. elim H. intros p H0. simpl in |- *.
    rewrite H0. rewrite (ad_xor_eq_false a a1 p). exact (MapPut1_semantics_2 p a a1 a0 y H0).
    assumption.
    intro H. simpl in |- *. rewrite H. rewrite <- (ad_xor_eq _ _ H). rewrite (ad_eq_correct a).
    exact (M1_semantics_1 a a0).
    intros. rewrite MapPut_behind_semantics_3_1. rewrite (MapGet_M2_bit_0_if m0 m1 a).
    elim (sumbool_of_bool (ad_bit_0 a)). intro H1. rewrite H1. rewrite (MapGet_M2_bit_0_1 a H1).
    exact (H0 (ad_div_2 a) y).
    intro H1. rewrite H1. rewrite (MapGet_M2_bit_0_0 a H1). exact (H (ad_div_2 a) y).
  Qed.

  Lemma MapPut_behind_semantics :
   forall (m:Map) (a:ad) (y:A),
     eqm (MapGet (MapPut_behind m a y))
       (fun a':ad =>
          match MapGet m a' with
          | SOME y' => SOME y'
          | _ => if ad_eq a a' then SOME y else NONE
          end).
  Proof.
    unfold eqm in |- *. intros. elim (sumbool_of_bool (ad_eq a a0)). intro H. rewrite H.
    rewrite (ad_eq_complete _ _ H). apply MapPut_behind_new.
    intro H. rewrite H. rewrite <- (MapPut_behind_as_before m a y a0 H).
    rewrite (MapPut_semantics m a y a0). rewrite H. case (MapGet m a0); trivial.
  Qed.

  Definition makeM2 (m m':Map) :=
    match m, m' with
    | M0, M0 => M0
    | M0, M1 a y => M1 (ad_double_plus_un a) y
    | M1 a y, M0 => M1 (ad_double a) y
    | _, _ => M2 m m'
    end.

  Lemma makeM2_M2 :
   forall m m':Map, eqm (MapGet (makeM2 m m')) (MapGet (M2 m m')).
  Proof.
    unfold eqm in |- *. intros. elim (sumbool_of_bool (ad_bit_0 a)). intro H.
    rewrite (MapGet_M2_bit_0_1 a H m m'). case m'. case m. reflexivity.
    intros a0 y. simpl in |- *. rewrite (ad_bit_0_1_not_double a H a0). reflexivity.
    intros m1 m2. unfold makeM2 in |- *. rewrite MapGet_M2_bit_0_1. reflexivity.
    assumption.
    case m. intros a0 y. simpl in |- *. elim (sumbool_of_bool (ad_eq a0 (ad_div_2 a))).
    intro H0. rewrite H0. rewrite (ad_eq_complete _ _ H0). rewrite (ad_div_2_double_plus_un a H).
    rewrite (ad_eq_correct a). reflexivity.
    intro H0. rewrite H0. rewrite (ad_eq_comm a0 (ad_div_2 a)) in H0.
    rewrite (ad_not_div_2_not_double_plus_un a a0 H0). reflexivity.
    intros a0 y0 a1 y1. unfold makeM2 in |- *. rewrite MapGet_M2_bit_0_1. reflexivity.
    assumption.
    intros m1 m2 a0 y. unfold makeM2 in |- *. rewrite MapGet_M2_bit_0_1. reflexivity.
    assumption.
    intros m1 m2. unfold makeM2 in |- *.
    cut (MapGet (M2 m (M2 m1 m2)) a = MapGet (M2 m1 m2) (ad_div_2 a)). 
    case m; trivial.
    exact (MapGet_M2_bit_0_1 a H m (M2 m1 m2)).
    intro H. rewrite (MapGet_M2_bit_0_0 a H m m'). case m. case m'. reflexivity.
    intros a0 y. simpl in |- *. rewrite (ad_bit_0_0_not_double_plus_un a H a0). reflexivity.
    intros m1 m2. unfold makeM2 in |- *. rewrite MapGet_M2_bit_0_0. reflexivity.
    assumption.
    case m'. intros a0 y. simpl in |- *. elim (sumbool_of_bool (ad_eq a0 (ad_div_2 a))). intro H0.
    rewrite H0. rewrite (ad_eq_complete _ _ H0). rewrite (ad_div_2_double a H).
    rewrite (ad_eq_correct a). reflexivity.
    intro H0. rewrite H0. rewrite (ad_eq_comm (ad_double a0) a).
    rewrite (ad_eq_comm a0 (ad_div_2 a)) in H0. rewrite (ad_not_div_2_not_double a a0 H0).
    reflexivity.
    intros a0 y0 a1 y1. unfold makeM2 in |- *. rewrite MapGet_M2_bit_0_0. reflexivity.
    assumption.
    intros m1 m2 a0 y. unfold makeM2 in |- *. rewrite MapGet_M2_bit_0_0. reflexivity.
    assumption.
    intros m1 m2. unfold makeM2 in |- *. exact (MapGet_M2_bit_0_0 a H (M2 m1 m2) m').
  Qed.

  Fixpoint MapRemove (m:Map) : ad -> Map :=
    match m with
    | M0 => fun _:ad => M0
    | M1 a y =>
        fun a':ad => match ad_eq a a' with
                     | true => M0
                     | false => m
                     end
    | M2 m1 m2 =>
        fun a:ad =>
          if ad_bit_0 a
          then makeM2 m1 (MapRemove m2 (ad_div_2 a))
          else makeM2 (MapRemove m1 (ad_div_2 a)) m2
    end.

  Lemma MapRemove_semantics :
   forall (m:Map) (a:ad),
     eqm (MapGet (MapRemove m a))
       (fun a':ad => if ad_eq a a' then NONE else MapGet m a').
  Proof.
    unfold eqm in |- *. simple induction m. simpl in |- *. intros. case (ad_eq a a0); trivial.
    intros. simpl in |- *. elim (sumbool_of_bool (ad_eq a1 a2)). intro H. rewrite H.
    elim (sumbool_of_bool (ad_eq a a1)). intro H0. rewrite H0. reflexivity.
    intro H0. rewrite H0. rewrite (ad_eq_complete _ _ H) in H0. exact (M1_semantics_2 a a2 a0 H0).
    intro H. elim (sumbool_of_bool (ad_eq a a1)). intro H0. rewrite H0. rewrite H.
    rewrite <- (ad_eq_complete _ _ H0) in H. rewrite H. reflexivity.
    intro H0. rewrite H0. rewrite H. reflexivity.
    intros. change
   (MapGet
      (if ad_bit_0 a
       then makeM2 m0 (MapRemove m1 (ad_div_2 a))
       else makeM2 (MapRemove m0 (ad_div_2 a)) m1) a0 =
    (if ad_eq a a0 then NONE else MapGet (M2 m0 m1) a0)) 
  in |- *.
    elim (sumbool_of_bool (ad_bit_0 a)). intro H1. rewrite H1.
    rewrite (makeM2_M2 m0 (MapRemove m1 (ad_div_2 a)) a0). elim (sumbool_of_bool (ad_bit_0 a0)).
    intro H2. rewrite MapGet_M2_bit_0_1. rewrite (H0 (ad_div_2 a) (ad_div_2 a0)).
    elim (sumbool_of_bool (ad_eq a a0)). intro H3. rewrite H3. rewrite (ad_div_eq _ _ H3).
    reflexivity.
    intro H3. rewrite H3. rewrite <- H2 in H1. rewrite (ad_div_bit_neq _ _ H3 H1).
    rewrite (MapGet_M2_bit_0_1 a0 H2 m0 m1). reflexivity.
    assumption.
    intro H2. rewrite (MapGet_M2_bit_0_0 a0 H2 m0 (MapRemove m1 (ad_div_2 a))).
    rewrite (ad_eq_comm a a0). rewrite (ad_bit_0_neq _ _ H2 H1).
    rewrite (MapGet_M2_bit_0_0 a0 H2 m0 m1). reflexivity.
    intro H1. rewrite H1. rewrite (makeM2_M2 (MapRemove m0 (ad_div_2 a)) m1 a0).
    elim (sumbool_of_bool (ad_bit_0 a0)). intro H2. rewrite MapGet_M2_bit_0_1.
    rewrite (MapGet_M2_bit_0_1 a0 H2 m0 m1). rewrite (ad_bit_0_neq a a0 H1 H2). reflexivity.
    assumption.
    intro H2. rewrite MapGet_M2_bit_0_0. rewrite (H (ad_div_2 a) (ad_div_2 a0)).
    rewrite (MapGet_M2_bit_0_0 a0 H2 m0 m1). elim (sumbool_of_bool (ad_eq a a0)). intro H3.
    rewrite H3. rewrite (ad_div_eq _ _ H3). reflexivity.
    intro H3. rewrite H3. rewrite <- H2 in H1. rewrite (ad_div_bit_neq _ _ H3 H1). reflexivity.
    assumption.
  Qed.

  Fixpoint MapCard (m:Map) : nat :=
    match m with
    | M0 => 0
    | M1 _ _ => 1
    | M2 m m' => MapCard m + MapCard m'
    end.

  Fixpoint MapMerge (m:Map) : Map -> Map :=
    match m with
    | M0 => fun m':Map => m'
    | M1 a y => fun m':Map => MapPut_behind m' a y
    | M2 m1 m2 =>
        fun m':Map =>
          match m' with
          | M0 => m
          | M1 a' y' => MapPut m a' y'
          | M2 m'1 m'2 => M2 (MapMerge m1 m'1) (MapMerge m2 m'2)
          end
    end.

  Lemma MapMerge_semantics :
   forall m m':Map,
     eqm (MapGet (MapMerge m m'))
       (fun a0:ad =>
          match MapGet m' a0 with
          | SOME y' => SOME y'
          | NONE => MapGet m a0
          end).
  Proof.
    unfold eqm in |- *. simple induction m. intros. simpl in |- *. case (MapGet m' a); trivial.
    intros. simpl in |- *. rewrite (MapPut_behind_semantics m' a a0 a1). reflexivity.
    simple induction m'. trivial.
    intros. unfold MapMerge in |- *. rewrite (MapPut_semantics (M2 m0 m1) a a0 a1).
    elim (sumbool_of_bool (ad_eq a a1)). intro H1. rewrite H1. rewrite (ad_eq_complete _ _ H1).
    rewrite (M1_semantics_1 a1 a0). reflexivity.
    intro H1. rewrite H1. rewrite (M1_semantics_2 a a1 a0 H1). reflexivity.
    intros. cut (MapMerge (M2 m0 m1) (M2 m2 m3) = M2 (MapMerge m0 m2) (MapMerge m1 m3)).
    intro. rewrite H3. rewrite MapGet_M2_bit_0_if. rewrite (H0 m3 (ad_div_2 a)).
    rewrite (H m2 (ad_div_2 a)). rewrite (MapGet_M2_bit_0_if m2 m3 a).
    rewrite (MapGet_M2_bit_0_if m0 m1 a). case (ad_bit_0 a); trivial.
    reflexivity.
  Qed.

  (** [MapInter], [MapRngRestrTo], [MapRngRestrBy], [MapInverse] 
      not implemented: need a decidable equality on [A]. *)

  Fixpoint MapDelta (m:Map) : Map -> Map :=
    match m with
    | M0 => fun m':Map => m'
    | M1 a y =>
        fun m':Map =>
          match MapGet m' a with
          | NONE => MapPut m' a y
          | _ => MapRemove m' a
          end
    | M2 m1 m2 =>
        fun m':Map =>
          match m' with
          | M0 => m
          | M1 a' y' =>
              match MapGet m a' with
              | NONE => MapPut m a' y'
              | _ => MapRemove m a'
              end
          | M2 m'1 m'2 => makeM2 (MapDelta m1 m'1) (MapDelta m2 m'2)
          end
    end.

  Lemma MapDelta_semantics_comm :
   forall m m':Map, eqm (MapGet (MapDelta m m')) (MapGet (MapDelta m' m)).
  Proof.
    unfold eqm in |- *. simple induction m. simple induction m'; reflexivity.
    simple induction m'. reflexivity.
    unfold MapDelta in |- *. intros. elim (sumbool_of_bool (ad_eq a a1)). intro H.
    rewrite <- (ad_eq_complete _ _ H). rewrite (M1_semantics_1 a a2).
    rewrite (M1_semantics_1 a a0). simpl in |- *. rewrite (ad_eq_correct a). reflexivity.
    intro H. rewrite (M1_semantics_2 a a1 a0 H). rewrite (ad_eq_comm a a1) in H.
    rewrite (M1_semantics_2 a1 a a2 H). rewrite (MapPut_semantics (M1 a a0) a1 a2 a3).
    rewrite (MapPut_semantics (M1 a1 a2) a a0 a3). elim (sumbool_of_bool (ad_eq a a3)).
    intro H0. rewrite H0. rewrite (ad_eq_complete _ _ H0) in H. rewrite H.
    rewrite (ad_eq_complete _ _ H0). rewrite (M1_semantics_1 a3 a0). reflexivity.
    intro H0. rewrite H0. rewrite (M1_semantics_2 a a3 a0 H0).
    elim (sumbool_of_bool (ad_eq a1 a3)). intro H1. rewrite H1.
    rewrite (ad_eq_complete _ _ H1). exact (M1_semantics_1 a3 a2).
    intro H1. rewrite H1. exact (M1_semantics_2 a1 a3 a2 H1).
    intros. reflexivity.
    simple induction m'. reflexivity.
    reflexivity.
    intros. simpl in |- *. rewrite (makeM2_M2 (MapDelta m0 m2) (MapDelta m1 m3) a).
    rewrite (makeM2_M2 (MapDelta m2 m0) (MapDelta m3 m1) a).
    rewrite (MapGet_M2_bit_0_if (MapDelta m0 m2) (MapDelta m1 m3) a).
    rewrite (MapGet_M2_bit_0_if (MapDelta m2 m0) (MapDelta m3 m1) a).
    rewrite (H0 m3 (ad_div_2 a)). rewrite (H m2 (ad_div_2 a)). reflexivity.
  Qed.

  Lemma MapDelta_semantics_1_1 :
   forall (a:ad) (y:A) (m':Map) (a0:ad),
     MapGet (M1 a y) a0 = NONE ->
     MapGet m' a0 = NONE -> MapGet (MapDelta (M1 a y) m') a0 = NONE.
  Proof.
    intros. unfold MapDelta in |- *. elim (sumbool_of_bool (ad_eq a a0)). intro H1.
    rewrite (ad_eq_complete _ _ H1) in H. rewrite (M1_semantics_1 a0 y) in H. discriminate H.
    intro H1. case (MapGet m' a). rewrite (MapPut_semantics m' a y a0). rewrite H1. assumption.
    rewrite (MapRemove_semantics m' a a0). rewrite H1. trivial.
  Qed.

  Lemma MapDelta_semantics_1 :
   forall (m m':Map) (a:ad),
     MapGet m a = NONE ->
     MapGet m' a = NONE -> MapGet (MapDelta m m') a = NONE.
  Proof.
    simple induction m. trivial.
    exact MapDelta_semantics_1_1.
    simple induction m'. trivial.
    intros. rewrite (MapDelta_semantics_comm (M2 m0 m1) (M1 a a0) a1).
    apply MapDelta_semantics_1_1; trivial.
    intros. simpl in |- *. rewrite (makeM2_M2 (MapDelta m0 m2) (MapDelta m1 m3) a).
    rewrite MapGet_M2_bit_0_if. elim (sumbool_of_bool (ad_bit_0 a)). intro H5. rewrite H5.
    apply H0. rewrite (MapGet_M2_bit_0_1 a H5 m0 m1) in H3. exact H3.
    rewrite (MapGet_M2_bit_0_1 a H5 m2 m3) in H4. exact H4.
    intro H5. rewrite H5. apply H. rewrite (MapGet_M2_bit_0_0 a H5 m0 m1) in H3. exact H3.
    rewrite (MapGet_M2_bit_0_0 a H5 m2 m3) in H4. exact H4.
  Qed.

  Lemma MapDelta_semantics_2_1 :
   forall (a:ad) (y:A) (m':Map) (a0:ad) (y0:A),
     MapGet (M1 a y) a0 = NONE ->
     MapGet m' a0 = SOME y0 -> MapGet (MapDelta (M1 a y) m') a0 = SOME y0.
  Proof.
    intros. unfold MapDelta in |- *. elim (sumbool_of_bool (ad_eq a a0)). intro H1.
    rewrite (ad_eq_complete _ _ H1) in H. rewrite (M1_semantics_1 a0 y) in H. discriminate H.
    intro H1. case (MapGet m' a). rewrite (MapPut_semantics m' a y a0). rewrite H1. assumption.
    rewrite (MapRemove_semantics m' a a0). rewrite H1. trivial.
  Qed.

  Lemma MapDelta_semantics_2_2 :
   forall (a:ad) (y:A) (m':Map) (a0:ad) (y0:A),
     MapGet (M1 a y) a0 = SOME y0 ->
     MapGet m' a0 = NONE -> MapGet (MapDelta (M1 a y) m') a0 = SOME y0.
  Proof.
    intros. unfold MapDelta in |- *. elim (sumbool_of_bool (ad_eq a a0)). intro H1.
    rewrite (ad_eq_complete _ _ H1) in H. rewrite (ad_eq_complete _ _ H1).
    rewrite H0. rewrite (MapPut_semantics m' a0 y a0). rewrite (ad_eq_correct a0).
    rewrite (M1_semantics_1 a0 y) in H. simple inversion H. assumption.
    intro H1. rewrite (M1_semantics_2 a a0 y H1) in H. discriminate H.
  Qed.

  Lemma MapDelta_semantics_2 :
   forall (m m':Map) (a:ad) (y:A),
     MapGet m a = NONE ->
     MapGet m' a = SOME y -> MapGet (MapDelta m m') a = SOME y.
  Proof.
    simple induction m. trivial.
    exact MapDelta_semantics_2_1.
    simple induction m'. intros. discriminate H2.
    intros. rewrite (MapDelta_semantics_comm (M2 m0 m1) (M1 a a0) a1).
    apply MapDelta_semantics_2_2; assumption.
    intros. simpl in |- *. rewrite (makeM2_M2 (MapDelta m0 m2) (MapDelta m1 m3) a).
    rewrite MapGet_M2_bit_0_if. elim (sumbool_of_bool (ad_bit_0 a)). intro H5. rewrite H5.
    apply H0. rewrite <- (MapGet_M2_bit_0_1 a H5 m0 m1). assumption.
    rewrite <- (MapGet_M2_bit_0_1 a H5 m2 m3). assumption.
    intro H5. rewrite H5. apply H. rewrite <- (MapGet_M2_bit_0_0 a H5 m0 m1). assumption.
    rewrite <- (MapGet_M2_bit_0_0 a H5 m2 m3). assumption.
  Qed.

  Lemma MapDelta_semantics_3_1 :
   forall (a0:ad) (y0:A) (m':Map) (a:ad) (y y':A),
     MapGet (M1 a0 y0) a = SOME y ->
     MapGet m' a = SOME y' -> MapGet (MapDelta (M1 a0 y0) m') a = NONE.
  Proof.
    intros. unfold MapDelta in |- *. elim (sumbool_of_bool (ad_eq a0 a)). intro H1.
    rewrite (ad_eq_complete a0 a H1). rewrite H0. rewrite (MapRemove_semantics m' a a).
    rewrite (ad_eq_correct a). reflexivity.
    intro H1. rewrite (M1_semantics_2 a0 a y0 H1) in H. discriminate H.
  Qed.

  Lemma MapDelta_semantics_3 :
   forall (m m':Map) (a:ad) (y y':A),
     MapGet m a = SOME y ->
     MapGet m' a = SOME y' -> MapGet (MapDelta m m') a = NONE.
  Proof.
    simple induction m. intros. discriminate H.
    exact MapDelta_semantics_3_1.
    simple induction m'. intros. discriminate H2.
    intros. rewrite (MapDelta_semantics_comm (M2 m0 m1) (M1 a a0) a1).
    exact (MapDelta_semantics_3_1 a a0 (M2 m0 m1) a1 y' y H2 H1).
    intros. simpl in |- *. rewrite (makeM2_M2 (MapDelta m0 m2) (MapDelta m1 m3) a).
    rewrite MapGet_M2_bit_0_if. elim (sumbool_of_bool (ad_bit_0 a)). intro H5. rewrite H5.
    apply (H0 m3 (ad_div_2 a) y y'). rewrite <- (MapGet_M2_bit_0_1 a H5 m0 m1). assumption.
    rewrite <- (MapGet_M2_bit_0_1 a H5 m2 m3). assumption.
    intro H5. rewrite H5. apply (H m2 (ad_div_2 a) y y').
    rewrite <- (MapGet_M2_bit_0_0 a H5 m0 m1). assumption.
    rewrite <- (MapGet_M2_bit_0_0 a H5 m2 m3). assumption.
  Qed.

  Lemma MapDelta_semantics :
   forall m m':Map,
     eqm (MapGet (MapDelta m m'))
       (fun a0:ad =>
          match MapGet m a0, MapGet m' a0 with
          | NONE, SOME y' => SOME y'
          | SOME y, NONE => SOME y
          | _, _ => NONE
          end).
  Proof.
    unfold eqm in |- *. intros. elim (option_sum (MapGet m' a)). intro H. elim H. intros a0 H0.
    rewrite H0. elim (option_sum (MapGet m a)). intro H1. elim H1. intros a1 H2. rewrite H2.
    exact (MapDelta_semantics_3 m m' a a1 a0 H2 H0).
    intro H1. rewrite H1. exact (MapDelta_semantics_2 m m' a a0 H1 H0).
    intro H. rewrite H. elim (option_sum (MapGet m a)). intro H0. elim H0. intros a0 H1.
    rewrite H1. rewrite (MapDelta_semantics_comm m m' a).
    exact (MapDelta_semantics_2 m' m a a0 H H1).
    intro H0. rewrite H0. exact (MapDelta_semantics_1 m m' a H0 H).
  Qed.

  Definition MapEmptyp (m:Map) := match m with
                                  | M0 => true
                                  | _ => false
                                  end.

  Lemma MapEmptyp_correct : MapEmptyp M0 = true.
  Proof.
    reflexivity.
  Qed.

  Lemma MapEmptyp_complete : forall m:Map, MapEmptyp m = true -> m = M0.
  Proof.
    simple induction m; trivial. intros. discriminate H.
    intros. discriminate H1.
  Qed.

  (** [MapSplit] not implemented: not the preferred way of recursing over Maps
      (use [MapSweep], [MapCollect], or [MapFold] in Mapiter.v. *)

End MapDefs.