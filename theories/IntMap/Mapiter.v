(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

Require Import Bool.
Require Import Sumbool.
Require Import NArith.
Require Import Ndigits.
Require Import Ndec.
Require Import Map.
Require Import Mapaxioms.
Require Import Fset.
Require Import List.

Section MapIter.

  Variable A : Type.

  Section MapSweepDef.

  Variable f : ad -> A -> bool.

  Definition MapSweep2 (a0:ad) (y:A) :=
    if f a0 y then Some (a0, y) else None.

  Fixpoint MapSweep1 (pf:ad -> ad) (m:Map A) {struct m} : 
   option (ad * A) :=
    match m with
    | M0 => None
    | M1 a y => MapSweep2 (pf a) y
    | M2 m m' =>
        match MapSweep1 (fun a:ad => pf (Ndouble a)) m with
        | Some r => Some r
        | None => MapSweep1 (fun a:ad => pf (Ndouble_plus_one a)) m'
        end
    end.

  Definition MapSweep (m:Map A) := MapSweep1 (fun a:ad => a) m.

  Lemma MapSweep_semantics_1_1 :
   forall (m:Map A) (pf:ad -> ad) (a:ad) (y:A),
     MapSweep1 pf m = Some (a, y) -> f a y = true.
  Proof.
    simple induction m. intros. discriminate H.
    simpl in |- *. intros a y pf a0 y0. elim (sumbool_of_bool (f (pf a) y)). intro H. unfold MapSweep2 in |- *.
    rewrite H. intro H0. inversion H0. rewrite <- H3. assumption.
    intro H. unfold MapSweep2 in |- *. rewrite H. intro H0. discriminate H0.
    simpl in |- *. intros. elim (option_sum (ad * A) (MapSweep1 (fun a0:ad => pf (Ndouble a0)) m0)).
    intro H2. elim H2. intros r H3. rewrite H3 in H1. inversion H1. rewrite H5 in H3.
    exact (H (fun a0:ad => pf (Ndouble a0)) a y H3).
    intro H2. rewrite H2 in H1. exact (H0 (fun a0:ad => pf (Ndouble_plus_one a0)) a y H1).
  Qed.

  Lemma MapSweep_semantics_1 :
   forall (m:Map A) (a:ad) (y:A), MapSweep m = Some (a, y) -> f a y = true.
  Proof.
    intros. exact (MapSweep_semantics_1_1 m (fun a:ad => a) a y H).
  Qed.

  Lemma MapSweep_semantics_2_1 :
   forall (m:Map A) (pf:ad -> ad) (a:ad) (y:A),
     MapSweep1 pf m = Some (a, y) -> {a' : ad | a = pf a'}.
  Proof.
    simple induction m. intros. discriminate H.
    simpl in |- *. unfold MapSweep2 in |- *. intros a y pf a0 y0. case (f (pf a) y). intros. split with a.
    inversion H. reflexivity.
    intro. discriminate H.
    intros m0 H m1 H0 pf a y. simpl in |- *.
    elim
     (option_sum (ad * A) (MapSweep1 (fun a0:ad => pf (Ndouble a0)) m0)). intro H1. elim H1.
    intros r H2. rewrite H2. intro H3. inversion H3. rewrite H5 in H2.
    elim (H (fun a0:ad => pf (Ndouble a0)) a y H2). intros a0 H6. split with (Ndouble a0).
    assumption.
    intro H1. rewrite H1. intro H2. elim (H0 (fun a0:ad => pf (Ndouble_plus_one a0)) a y H2).
    intros a0 H3. split with (Ndouble_plus_one a0). assumption.
  Qed.

  Lemma MapSweep_semantics_2_2 :
   forall (m:Map A) (pf fp:ad -> ad),
     (forall a0:ad, fp (pf a0) = a0) ->
     forall (a:ad) (y:A),
       MapSweep1 pf m = Some (a, y) -> MapGet A m (fp a) = Some y.
  Proof.
    simple induction m. intros. discriminate H0.
    simpl in |- *. intros a y pf fp H a0 y0. unfold MapSweep2 in |- *. elim (sumbool_of_bool (f (pf a) y)).
    intro H0. rewrite H0. intro H1. inversion H1. rewrite (H a). rewrite (Neqb_correct a).
    reflexivity.
    intro H0. rewrite H0. intro H1. discriminate H1.
    intros. rewrite (MapGet_M2_bit_0_if A m0 m1 (fp a)). elim (sumbool_of_bool (Nbit0 (fp a))).
    intro H3. rewrite H3. elim (option_sum (ad * A) (MapSweep1 (fun a0:ad => pf (Ndouble a0)) m0)).
    intro H4. simpl in H2. apply
  (H0 (fun a0:ad => pf (Ndouble_plus_one a0))
     (fun a0:ad => Ndiv2 (fp a0))).
    intro. rewrite H1. apply Ndouble_plus_one_div2.
    elim
     (option_sum (ad * A) (MapSweep1 (fun a0:ad => pf (Ndouble a0)) m0)). intro H5. elim H5.
    intros r H6. rewrite H6 in H2. inversion H2. rewrite H8 in H6.
    elim (MapSweep_semantics_2_1 m0 (fun a0:ad => pf (Ndouble a0)) a y H6). intros a0 H9.
    rewrite H9 in H3. rewrite (H1 (Ndouble a0)) in H3. rewrite (Ndouble_bit0 a0) in H3.
    discriminate H3.
    intro H5. rewrite H5 in H2. assumption.
    intro H4. simpl in H2. rewrite H4 in H2.
    apply
     (H0 (fun a0:ad => pf (Ndouble_plus_one a0))
        (fun a0:ad => Ndiv2 (fp a0))). intro.
    rewrite H1. apply Ndouble_plus_one_div2.
    assumption.
    intro H3. rewrite H3. simpl in H2.
    elim
     (option_sum (ad * A) (MapSweep1 (fun a0:ad => pf (Ndouble a0)) m0)). intro H4. elim H4.
    intros r H5. rewrite H5 in H2. inversion H2. rewrite H7 in H5.
    apply
     (H (fun a0:ad => pf (Ndouble a0)) (fun a0:ad => Ndiv2 (fp a0))). intro. rewrite H1.
    apply Ndouble_div2.
    assumption.
    intro H4. rewrite H4 in H2.
    elim
     (MapSweep_semantics_2_1 m1 (fun a0:ad => pf (Ndouble_plus_one a0)) a y
        H2).
    intros a0 H5. rewrite H5 in H3. rewrite (H1 (Ndouble_plus_one a0)) in H3.
    rewrite (Ndouble_plus_one_bit0 a0) in H3. discriminate H3.
  Qed.

  Lemma MapSweep_semantics_2 :
   forall (m:Map A) (a:ad) (y:A),
     MapSweep m = Some (a, y) -> MapGet A m a = Some y.
  Proof.
    intros.
    exact
     (MapSweep_semantics_2_2 m (fun a0:ad => a0) (fun a0:ad => a0)
        (fun a0:ad => refl_equal a0) a y H).
  Qed.

  Lemma MapSweep_semantics_3_1 :
   forall (m:Map A) (pf:ad -> ad),
     MapSweep1 pf m = None ->
     forall (a:ad) (y:A), MapGet A m a = Some y -> f (pf a) y = false.
  Proof.
    simple induction m. intros. discriminate H0.
    simpl in |- *. unfold MapSweep2 in |- *. intros a y pf. elim (sumbool_of_bool (f (pf a) y)). intro H.
    rewrite H. intro. discriminate H0.
    intro H. rewrite H. intros H0 a0 y0. elim (sumbool_of_bool (Neqb a a0)). intro H1. rewrite H1.
    intro H2. inversion H2. rewrite <- H4. rewrite <- (Neqb_complete _ _ H1). assumption.
    intro H1. rewrite H1. intro. discriminate H2.
    intros. simpl in H1. elim (option_sum (ad * A) (MapSweep1 (fun a:ad => pf (Ndouble a)) m0)).
    intro H3. elim H3. intros r H4. rewrite H4 in H1. discriminate H1.
    intro H3. rewrite H3 in H1. elim (sumbool_of_bool (Nbit0 a)). intro H4.
    rewrite (MapGet_M2_bit_0_1 A a H4 m0 m1) in H2. rewrite <- (Ndiv2_double_plus_one a H4).
    exact (H0 (fun a:ad => pf (Ndouble_plus_one a)) H1 (Ndiv2 a) y H2).
    intro H4. rewrite (MapGet_M2_bit_0_0 A a H4 m0 m1) in H2. rewrite <- (Ndiv2_double a H4).
    exact (H (fun a:ad => pf (Ndouble a)) H3 (Ndiv2 a) y H2).
  Qed.

  Lemma MapSweep_semantics_3 :
   forall m:Map A,
     MapSweep m = None ->
     forall (a:ad) (y:A), MapGet A m a = Some y -> f a y = false.
  Proof.
    intros.
    exact (MapSweep_semantics_3_1 m (fun a0:ad => a0) H a y H0).
  Qed.

  Lemma MapSweep_semantics_4_1 :
   forall (m:Map A) (pf:ad -> ad) (a:ad) (y:A),
     MapGet A m a = Some y ->
     f (pf a) y = true ->
     {a' : ad &  {y' : A | MapSweep1 pf m = Some (a', y')}}.
  Proof.
    simple induction m. intros. discriminate H.
    intros. elim (sumbool_of_bool (Neqb a a1)). intro H1. split with (pf a1). split with y.
    rewrite (Neqb_complete _ _ H1). unfold MapSweep1, MapSweep2 in |- *.
    rewrite (Neqb_complete _ _ H1) in H. rewrite (M1_semantics_1 _ a1 a0) in H.
    inversion H. rewrite H0. reflexivity.

    intro H1. rewrite (M1_semantics_2 _ a a1 a0 H1) in H. discriminate H.

    intros. elim (sumbool_of_bool (Nbit0 a)). intro H3.
    rewrite (MapGet_M2_bit_0_1 _ _ H3 m0 m1) in H.
    rewrite <- (Ndiv2_double_plus_one a H3) in H0.
    elim (X0 (fun a0:ad => pf (Ndouble_plus_one a0)) (Ndiv2 a) y H H0). intros a'' H4. elim H4.
    intros y'' H5. simpl in |- *. elim (option_sum _ (MapSweep1 (fun a:ad => pf (Ndouble a)) m0)).
    intro H6. elim H6. intro r. elim r. intros a''' y''' H7. rewrite H7. split with a'''.
    split with y'''. reflexivity.
    intro H6. rewrite H6. split with a''. split with y''. assumption.
    intro H3. rewrite (MapGet_M2_bit_0_0 _ _ H3 m0 m1) in H.
    rewrite <- (Ndiv2_double a H3) in H0.
    elim (X (fun a0:ad => pf (Ndouble a0)) (Ndiv2 a) y H H0). intros a'' H4. elim H4.
    intros y'' H5. split with a''. split with y''. simpl in |- *. rewrite H5. reflexivity.
  Qed.

  Lemma MapSweep_semantics_4 :
   forall (m:Map A) (a:ad) (y:A),
     MapGet A m a = Some y ->
     f a y = true -> {a' : ad &  {y' : A | MapSweep m = Some (a', y')}}.
  Proof.
    intros. exact (MapSweep_semantics_4_1 m (fun a0:ad => a0) a y H H0).
  Qed.

  End MapSweepDef.

  Variable B : Type.

  Fixpoint MapCollect1 (f:ad -> A -> Map B) (pf:ad -> ad) 
   (m:Map A) {struct m} : Map B :=
    match m with
    | M0 => M0 B
    | M1 a y => f (pf a) y
    | M2 m1 m2 =>
        MapMerge B (MapCollect1 f (fun a0:ad => pf (Ndouble a0)) m1)
          (MapCollect1 f (fun a0:ad => pf (Ndouble_plus_one a0)) m2)
    end.

  Definition MapCollect (f:ad -> A -> Map B) (m:Map A) :=
    MapCollect1 f (fun a:ad => a) m.

  Section MapFoldDef.

    Variable M : Type.
    Variable neutral : M.
    Variable op : M -> M -> M.

    Fixpoint MapFold1 (f:ad -> A -> M) (pf:ad -> ad) 
     (m:Map A) {struct m} : M :=
      match m with
      | M0 => neutral
      | M1 a y => f (pf a) y
      | M2 m1 m2 =>
          op (MapFold1 f (fun a0:ad => pf (Ndouble a0)) m1)
            (MapFold1 f (fun a0:ad => pf (Ndouble_plus_one a0)) m2)
      end.

    Definition MapFold (f:ad -> A -> M) (m:Map A) :=
      MapFold1 f (fun a:ad => a) m.

    Lemma MapFold_empty : forall f:ad -> A -> M, MapFold f (M0 A) = neutral.
    Proof.
      trivial.
    Qed.

    Lemma MapFold_M1 :
     forall (f:ad -> A -> M) (a:ad) (y:A), MapFold f (M1 A a y) = f a y.
    Proof.
      trivial.
    Qed.

    Variable State : Type.
    Variable f : State -> ad -> A -> State * M.

    Fixpoint MapFold1_state (state:State) (pf:ad -> ad) 
     (m:Map A) {struct m} : State * M :=
      match m with
      | M0 => (state, neutral)
      | M1 a y => f state (pf a) y
      | M2 m1 m2 =>
          match MapFold1_state state (fun a0:ad => pf (Ndouble a0)) m1 with
          | (state1, x1) =>
              match
                MapFold1_state state1
                  (fun a0:ad => pf (Ndouble_plus_one a0)) m2
              with
              | (state2, x2) => (state2, op x1 x2)
              end
          end
      end.

    Definition MapFold_state (state:State) :=
      MapFold1_state state (fun a:ad => a).

    Lemma pair_sp : forall (B C:Type) (x:B * C), x = (fst x, snd x).
    Proof.
      simple induction x. trivial.
    Qed.

    Lemma MapFold_state_stateless_1 :
     forall (m:Map A) (g:ad -> A -> M) (pf:ad -> ad),
       (forall (state:State) (a:ad) (y:A), snd (f state a y) = g a y) ->
       forall state:State, snd (MapFold1_state state pf m) = MapFold1 g pf m.
    Proof.
      simple induction m. trivial.
      intros. simpl in |- *. apply H.
      intros. simpl in |- *. rewrite
  (pair_sp _ _ (MapFold1_state state (fun a0:ad => pf (Ndouble a0)) m0))
  .
      rewrite (H g (fun a0:ad => pf (Ndouble a0)) H1 state).
      rewrite
       (pair_sp _ _
          (MapFold1_state
             (fst (MapFold1_state state (fun a0:ad => pf (Ndouble a0)) m0))
             (fun a0:ad => pf (Ndouble_plus_one a0)) m1))
       .
      simpl in |- *.
      rewrite
       (H0 g (fun a0:ad => pf (Ndouble_plus_one a0)) H1
          (fst (MapFold1_state state (fun a0:ad => pf (Ndouble a0)) m0)))
       .
      reflexivity.
    Qed.

    Lemma MapFold_state_stateless :
     forall g:ad -> A -> M,
       (forall (state:State) (a:ad) (y:A), snd (f state a y) = g a y) ->
       forall (state:State) (m:Map A),
         snd (MapFold_state state m) = MapFold g m.
    Proof.
      intros. exact (MapFold_state_stateless_1 m g (fun a0:ad => a0) H state).
    Qed.

  End MapFoldDef.

  Lemma MapCollect_as_Fold :
   forall (f:ad -> A -> Map B) (m:Map A),
     MapCollect f m = MapFold (Map B) (M0 B) (MapMerge B) f m.
  Proof.
    simple induction m; trivial.
  Qed.

  Definition alist := list (ad * A).
  Definition anil := nil (A:=(ad * A)).
  Definition acons := cons (A:=(ad * A)).
  Definition aapp := app (A:=(ad * A)).

  Definition alist_of_Map :=
    MapFold alist anil aapp (fun (a:ad) (y:A) => acons (a, y) anil).

  Fixpoint alist_semantics (l:alist) : ad -> option A :=
    match l with
    | nil => fun _:ad => None
    | (a, y) :: l' =>
        fun a0:ad => if Neqb a a0 then Some y else alist_semantics l' a0
    end.

  Lemma alist_semantics_app :
   forall (l l':alist) (a:ad),
     alist_semantics (aapp l l') a =
     match alist_semantics l a with
     | None => alist_semantics l' a
     | Some y => Some y
     end.
  Proof.
    unfold aapp in |- *. simple induction l. trivial.
    intros. elim a. intros a1 y1. simpl in |- *. case (Neqb a1 a0). reflexivity.
    apply H.
  Qed.

  Lemma alist_of_Map_semantics_1_1 :
   forall (m:Map A) (pf:ad -> ad) (a:ad) (y:A),
     alist_semantics
       (MapFold1 alist anil aapp (fun (a0:ad) (y:A) => acons (a0, y) anil) pf
          m) a = Some y -> {a' : ad | a = pf a'}.
  Proof.
    simple induction m. simpl in |- *. intros. discriminate H.
    simpl in |- *. intros a y pf a0 y0. elim (sumbool_of_bool (Neqb (pf a) a0)). intro H. rewrite H.
    intro H0. split with a. rewrite (Neqb_complete _ _ H). reflexivity.
    intro H. rewrite H. intro H0. discriminate H0.
    intros. change
   (alist_semantics
      (aapp
         (MapFold1 alist anil aapp (fun (a0:ad) (y:A) => acons (a0, y) anil)
            (fun a0:ad => pf (Ndouble a0)) m0)
         (MapFold1 alist anil aapp (fun (a0:ad) (y:A) => acons (a0, y) anil)
            (fun a0:ad => pf (Ndouble_plus_one a0)) m1)) a = 
    Some y) in H.
    rewrite
     (alist_semantics_app
        (MapFold1 alist anil aapp (fun (a0:ad) (y0:A) => acons (a0, y0) anil)
           (fun a0:ad => pf (Ndouble a0)) m0)
        (MapFold1 alist anil aapp (fun (a0:ad) (y0:A) => acons (a0, y0) anil)
           (fun a0:ad => pf (Ndouble_plus_one a0)) m1) a)
      in H.
    elim
     (option_sum A
        (alist_semantics
           (MapFold1 alist anil aapp
              (fun (a0:ad) (y0:A) => acons (a0, y0) anil)
              (fun a0:ad => pf (Ndouble a0)) m0) a)).
    intro H2. elim H2. intros y0 H3. elim (X (fun a0:ad => pf (Ndouble a0)) a y0 H3). intros a0 H4.
    split with (Ndouble a0). assumption.
    intro H2. rewrite H2 in H. elim (X0 (fun a0:ad => pf (Ndouble_plus_one a0)) a y H).
    intros a0 H3. split with (Ndouble_plus_one a0). assumption.
  Qed.

  Definition ad_inj (pf:ad -> ad) :=
    forall a0 a1:ad, pf a0 = pf a1 -> a0 = a1.

  Lemma ad_comp_double_inj :
   forall pf:ad -> ad, ad_inj pf -> ad_inj (fun a0:ad => pf (Ndouble a0)).
  Proof.
    unfold ad_inj in |- *. intros. apply Ndouble_inj. exact (H _ _ H0).
  Qed.

  Lemma ad_comp_double_plus_un_inj :
   forall pf:ad -> ad,
     ad_inj pf -> ad_inj (fun a0:ad => pf (Ndouble_plus_one a0)).
  Proof.
    unfold ad_inj in |- *. intros. apply Ndouble_plus_one_inj. exact (H _ _ H0).
  Qed.

  Lemma alist_of_Map_semantics_1 :
   forall (m:Map A) (pf:ad -> ad),
     ad_inj pf ->
     forall a:ad,
       MapGet A m a =
       alist_semantics
         (MapFold1 alist anil aapp (fun (a0:ad) (y:A) => acons (a0, y) anil)
            pf m) (pf a).
  Proof.
    simple induction m. trivial.
    simpl in |- *. intros. elim (sumbool_of_bool (Neqb a a1)). intro H0. rewrite H0.
    rewrite (Neqb_complete _ _ H0). rewrite (Neqb_correct (pf a1)). reflexivity.
    intro H0. rewrite H0. elim (sumbool_of_bool (Neqb (pf a) (pf a1))). intro H1.
    rewrite (H a a1 (Neqb_complete _ _ H1)) in H0. rewrite (Neqb_correct a1) in H0.
    discriminate H0.
    intro H1. rewrite H1. reflexivity.
    intros. change
   (MapGet A (M2 A m0 m1) a =
    alist_semantics
      (aapp
         (MapFold1 alist anil aapp (fun (a0:ad) (y:A) => acons (a0, y) anil)
            (fun a0:ad => pf (Ndouble a0)) m0)
         (MapFold1 alist anil aapp (fun (a0:ad) (y:A) => acons (a0, y) anil)
            (fun a0:ad => pf (Ndouble_plus_one a0)) m1)) (
      pf a)) in |- *.
    rewrite alist_semantics_app. rewrite (MapGet_M2_bit_0_if A m0 m1 a).
    elim (Ndouble_or_double_plus_un a). intro H2. elim H2. intros a0 H3. rewrite H3.
    rewrite (Ndouble_bit0 a0).
    rewrite <-
     (H (fun a1:ad => pf (Ndouble a1)) (ad_comp_double_inj pf H1) a0)
     .
    rewrite Ndouble_div2. case (MapGet A m0 a0); trivial.
    elim
     (option_sum A
        (alist_semantics
           (MapFold1 alist anil aapp
              (fun (a1:ad) (y:A) => acons (a1, y) anil)
              (fun a1:ad => pf (Ndouble_plus_one a1)) m1)
           (pf (Ndouble a0)))).
    intro H4. elim H4. intros y H5.
    elim
     (alist_of_Map_semantics_1_1 m1 (fun a1:ad => pf (Ndouble_plus_one a1))
        (pf (Ndouble a0)) y H5).
    intros a1 H6. cut (Nbit0 (Ndouble a0) = Nbit0 (Ndouble_plus_one a1)).
    intro. rewrite (Ndouble_bit0 a0) in H7. rewrite (Ndouble_plus_one_bit0 a1) in H7.
    discriminate H7.
    rewrite (H1 (Ndouble a0) (Ndouble_plus_one a1) H6). reflexivity.
    intro H4. rewrite H4. reflexivity.
    intro H2. elim H2. intros a0 H3. rewrite H3. rewrite (Ndouble_plus_one_bit0 a0).
    rewrite <-
     (H0 (fun a1:ad => pf (Ndouble_plus_one a1))
        (ad_comp_double_plus_un_inj pf H1) a0).
    rewrite Ndouble_plus_one_div2.
    elim
     (option_sum A
        (alist_semantics
           (MapFold1 alist anil aapp
              (fun (a1:ad) (y:A) => acons (a1, y) anil)
              (fun a1:ad => pf (Ndouble a1)) m0)
           (pf (Ndouble_plus_one a0)))).
    intro H4. elim H4. intros y H5.
    elim
     (alist_of_Map_semantics_1_1 m0 (fun a1:ad => pf (Ndouble a1))
        (pf (Ndouble_plus_one a0)) y H5).
    intros a1 H6. cut (Nbit0 (Ndouble_plus_one a0) = Nbit0 (Ndouble a1)).
    intro H7. rewrite (Ndouble_plus_one_bit0 a0) in H7. rewrite (Ndouble_bit0 a1) in H7.
    discriminate H7.
    rewrite (H1 (Ndouble_plus_one a0) (Ndouble a1) H6). reflexivity.
    intro H4. rewrite H4. reflexivity.
  Qed.

  Lemma alist_of_Map_semantics :
   forall m:Map A, eqm A (MapGet A m) (alist_semantics (alist_of_Map m)).
  Proof.
    unfold eqm in |- *. intros. exact
  (alist_of_Map_semantics_1 m (fun a0:ad => a0)
     (fun (a0 a1:ad) (p:a0 = a1) => p) a).
  Qed.

  Fixpoint Map_of_alist (l:alist) : Map A :=
    match l with
    | nil => M0 A
    | (a, y) :: l' => MapPut A (Map_of_alist l') a y
    end.

  Lemma Map_of_alist_semantics :
   forall l:alist, eqm A (alist_semantics l) (MapGet A (Map_of_alist l)).
  Proof.
    unfold eqm in |- *. simple induction l. trivial.
    intros r l0 H a. elim r. intros a0 y0. simpl in |- *. elim (sumbool_of_bool (Neqb a0 a)).
    intro H0. rewrite H0. rewrite (Neqb_complete _ _ H0).
    rewrite (MapPut_semantics A (Map_of_alist l0) a y0 a). rewrite (Neqb_correct a).
    reflexivity.
    intro H0. rewrite H0. rewrite (MapPut_semantics A (Map_of_alist l0) a0 y0 a).
    rewrite H0. apply H.
  Qed.

  Lemma Map_of_alist_of_Map :
   forall m:Map A, eqmap A (Map_of_alist (alist_of_Map m)) m.
  Proof.
    unfold eqmap in |- *. intro. apply eqm_trans with (f' := alist_semantics (alist_of_Map m)).
    apply eqm_sym. apply Map_of_alist_semantics.
    apply eqm_sym. apply alist_of_Map_semantics.
  Qed.

  Lemma alist_of_Map_of_alist :
   forall l:alist,
     eqm A (alist_semantics (alist_of_Map (Map_of_alist l)))
       (alist_semantics l).
  Proof.
    intro. apply eqm_trans with (f' := MapGet A (Map_of_alist l)).
    apply eqm_sym. apply alist_of_Map_semantics.
    apply eqm_sym. apply Map_of_alist_semantics.
  Qed.

  Lemma fold_right_aapp :
   forall (M:Type) (neutral:M) (op:M -> M -> M),
     (forall a b c:M, op (op a b) c = op a (op b c)) ->
     (forall a:M, op neutral a = a) ->
     forall (f:ad -> A -> M) (l l':alist),
       fold_right (fun (r:ad * A) (m:M) => let (a, y) := r in op (f a y) m)
         neutral (aapp l l') =
       op
         (fold_right
            (fun (r:ad * A) (m:M) => let (a, y) := r in op (f a y) m) neutral
            l)
         (fold_right
            (fun (r:ad * A) (m:M) => let (a, y) := r in op (f a y) m) neutral
            l').
  Proof.
    simple induction l. simpl in |- *. intro. rewrite H0. reflexivity.
    intros r l0 H1 l'. elim r. intros a y. simpl in |- *. rewrite H. rewrite (H1 l'). reflexivity.
  Qed.

  Lemma MapFold_as_fold_1 :
   forall (M:Type) (neutral:M) (op:M -> M -> M),
     (forall a b c:M, op (op a b) c = op a (op b c)) ->
     (forall a:M, op neutral a = a) ->
     (forall a:M, op a neutral = a) ->
     forall (f:ad -> A -> M) (m:Map A) (pf:ad -> ad),
       MapFold1 M neutral op f pf m =
       fold_right (fun (r:ad * A) (m:M) => let (a, y) := r in op (f a y) m)
         neutral
         (MapFold1 alist anil aapp (fun (a:ad) (y:A) => acons (a, y) anil) pf
            m).
  Proof.
    simple induction m. trivial.
    intros. simpl in |- *. rewrite H1. reflexivity.
    intros. simpl in |- *. rewrite (fold_right_aapp M neutral op H H0 f).
    rewrite (H2 (fun a0:ad => pf (Ndouble a0))). rewrite (H3 (fun a0:ad => pf (Ndouble_plus_one a0))).
    reflexivity.
  Qed.

  Lemma MapFold_as_fold :
   forall (M:Type) (neutral:M) (op:M -> M -> M),
     (forall a b c:M, op (op a b) c = op a (op b c)) ->
     (forall a:M, op neutral a = a) ->
     (forall a:M, op a neutral = a) ->
     forall (f:ad -> A -> M) (m:Map A),
       MapFold M neutral op f m =
       fold_right (fun (r:ad * A) (m:M) => let (a, y) := r in op (f a y) m)
         neutral (alist_of_Map m).
  Proof.
    intros. exact (MapFold_as_fold_1 M neutral op H H0 H1 f m (fun a0:ad => a0)).
  Qed.

  Lemma alist_MapMerge_semantics :
   forall m m':Map A,
     eqm A (alist_semantics (aapp (alist_of_Map m') (alist_of_Map m)))
       (alist_semantics (alist_of_Map (MapMerge A m m'))).
  Proof.
    unfold eqm in |- *. intros. rewrite alist_semantics_app. rewrite <- (alist_of_Map_semantics m a).
    rewrite <- (alist_of_Map_semantics m' a).
    rewrite <- (alist_of_Map_semantics (MapMerge A m m') a).
    rewrite (MapMerge_semantics A m m' a). reflexivity.
  Qed.

  Lemma alist_MapMerge_semantics_disjoint :
   forall m m':Map A,
     eqmap A (MapDomRestrTo A A m m') (M0 A) ->
     eqm A (alist_semantics (aapp (alist_of_Map m) (alist_of_Map m')))
       (alist_semantics (alist_of_Map (MapMerge A m m'))).
  Proof.
    unfold eqm in |- *. intros. rewrite alist_semantics_app. rewrite <- (alist_of_Map_semantics m a).
    rewrite <- (alist_of_Map_semantics m' a).
    rewrite <- (alist_of_Map_semantics (MapMerge A m m') a). rewrite (MapMerge_semantics A m m' a).
    elim (option_sum _ (MapGet A m a)). intro H0. elim H0. intros y H1. rewrite H1.
    elim (option_sum _ (MapGet A m' a)). intro H2. elim H2. intros y' H3.
    cut (MapGet A (MapDomRestrTo A A m m') a = None).
    rewrite (MapDomRestrTo_semantics A A m m' a). rewrite H3. rewrite H1. intro. discriminate H4.
    exact (H a).
    intro H2. rewrite H2. reflexivity.
    intro H0. rewrite H0. case (MapGet A m' a); trivial.
  Qed.

  Lemma alist_semantics_disjoint_comm :
   forall l l':alist,
     eqmap A (MapDomRestrTo A A (Map_of_alist l) (Map_of_alist l')) (M0 A) ->
     eqm A (alist_semantics (aapp l l')) (alist_semantics (aapp l' l)).
  Proof.
    unfold eqm in |- *. intros. rewrite (alist_semantics_app l l' a). rewrite (alist_semantics_app l' l a).
    rewrite <- (alist_of_Map_of_alist l a). rewrite <- (alist_of_Map_of_alist l' a).
    rewrite <-
     (alist_semantics_app (alist_of_Map (Map_of_alist l))
        (alist_of_Map (Map_of_alist l')) a).
    rewrite <-
     (alist_semantics_app (alist_of_Map (Map_of_alist l'))
        (alist_of_Map (Map_of_alist l)) a).
    rewrite (alist_MapMerge_semantics (Map_of_alist l) (Map_of_alist l') a).
    rewrite
     (alist_MapMerge_semantics_disjoint (Map_of_alist l) (
        Map_of_alist l') H a).
    reflexivity.
  Qed.

End MapIter.
