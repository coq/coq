(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

Require Bool.
Require Sumbool.
Require ZArith.
Require Addr.
Require Adist.
Require Addec.
Require Map.
Require Mapaxioms.
Require Fset.
Require PolyList.

Section MapIter.

  Variable A : Set.

  Section MapSweepDef.

  Variable f:ad->A->bool.

  Definition MapSweep2 := [a0:ad; y:A] if (f a0 y) then (SOME ? (a0, y)) else (NONE ?).

  Fixpoint MapSweep1 [pf:ad->ad; m:(Map A)] : (option (ad * A)) :=
    Cases m of
        M0 => (NONE ?)
      | (M1 a y) => (MapSweep2 (pf a) y)
      | (M2 m m') => Cases (MapSweep1 ([a:ad] (pf (ad_double a))) m) of
                         (SOME r) => (SOME ? r)
		       | NONE => (MapSweep1 ([a:ad] (pf (ad_double_plus_un a))) m')
		     end
    end.

  Definition MapSweep := [m:(Map A)] (MapSweep1 ([a:ad] a) m).

  Lemma MapSweep_semantics_1_1 : (m:(Map A)) (pf:ad->ad) (a:ad) (y:A)
      (MapSweep1 pf m)=(SOME ? (a, y)) -> (f a y)=true.
  Proof.
    Induction m. Intros. Discriminate H.
    Simpl. Intros a y pf a0 y0. Elim (sumbool_of_bool (f (pf a) y)). Intro H. Unfold MapSweep2.
    Rewrite H. Intro H0. Inversion H0. Rewrite <- H3. Assumption.
    Intro H. Unfold MapSweep2. Rewrite H. Intro H0. Discriminate H0.
    Simpl. Intros. Elim (option_sum ad*A (MapSweep1 [a0:ad](pf (ad_double a0)) m0)).
    Intro H2. Elim H2. Intros r H3. Rewrite H3 in H1. Inversion H1. Rewrite H5 in H3.
    Exact (H [a0:ad](pf (ad_double a0)) a y H3).
    Intro H2. Rewrite H2 in H1. Exact (H0 [a0:ad](pf (ad_double_plus_un a0)) a y H1).
  Qed.

  Lemma MapSweep_semantics_1 : (m:(Map A)) (a:ad) (y:A)
      (MapSweep m)=(SOME ? (a, y)) -> (f a y)=true.
  Proof.
    Intros. Exact (MapSweep_semantics_1_1 m [a:ad]a a y H).
  Qed.

  Lemma MapSweep_semantics_2_1 : (m:(Map A)) (pf:ad->ad) (a:ad) (y:A)
      	(MapSweep1 pf m)=(SOME ? (a, y)) -> {a':ad | a=(pf a')}.
  Proof.
    Induction m. Intros. Discriminate H.
    Simpl. Unfold MapSweep2. Intros a y pf a0 y0. Case (f (pf a) y). Intros. Split with a.
    Inversion H. Reflexivity.
    Intro. Discriminate H.
    Intros m0 H m1 H0 pf a y. Simpl.
    Elim (option_sum ad*A (MapSweep1 [a0:ad](pf (ad_double a0)) m0)). Intro H1. Elim H1.
    Intros r H2. Rewrite H2. Intro H3. Inversion H3. Rewrite H5 in H2.
    Elim (H [a0:ad](pf (ad_double a0)) a y H2). Intros a0 H6. Split with (ad_double a0).
    Assumption.
    Intro H1. Rewrite H1. Intro H2. Elim (H0 [a0:ad](pf (ad_double_plus_un a0)) a y H2).
    Intros a0 H3. Split with (ad_double_plus_un a0). Assumption.
  Qed.

  Lemma MapSweep_semantics_2_2 : (m:(Map A))
      (pf,fp:ad->ad) ((a0:ad) (fp (pf a0))=a0) -> (a:ad) (y:A)
      	(MapSweep1 pf m)=(SOME ? (a, y)) -> (MapGet A m (fp a))=(SOME ? y).
  Proof.
    Induction m. Intros. Discriminate H0.
    Simpl. Intros a y pf fp H a0 y0. Unfold MapSweep2. Elim (sumbool_of_bool (f (pf a) y)).
    Intro H0. Rewrite H0. Intro H1. Inversion H1. Rewrite (H a). Rewrite (ad_eq_correct a).
    Reflexivity.
    Intro H0. Rewrite H0. Intro H1. Discriminate H1.
    Intros. Rewrite (MapGet_M2_bit_0_if A m0 m1 (fp a)). Elim (sumbool_of_bool (ad_bit_0 (fp a))).
    Intro H3. Rewrite H3. Elim (option_sum ad*A (MapSweep1 [a0:ad](pf (ad_double a0)) m0)).
    Intro H4. Simpl in H2. Apply (H0 [a0:ad](pf (ad_double_plus_un a0)) [a0:ad](ad_div_2 (fp a0))).
    Intro. Rewrite H1. Apply ad_double_plus_un_div_2.
    Elim (option_sum ad*A (MapSweep1 [a0:ad](pf (ad_double a0)) m0)). Intro H5. Elim H5.
    Intros r H6. Rewrite H6 in H2. Inversion H2. Rewrite H8 in H6.
    Elim (MapSweep_semantics_2_1 m0 [a0:ad](pf (ad_double a0)) a y H6). Intros a0 H9.
    Rewrite H9 in H3. Rewrite (H1 (ad_double a0)) in H3. Rewrite (ad_double_bit_0 a0) in H3.
    Discriminate H3.
    Intro H5. Rewrite H5 in H2. Assumption.
    Intro H4. Simpl in H2. Rewrite H4 in H2.
    Apply (H0 [a0:ad](pf (ad_double_plus_un a0)) [a0:ad](ad_div_2 (fp a0))). Intro.
    Rewrite H1. Apply ad_double_plus_un_div_2.
    Assumption.
    Intro H3. Rewrite H3. Simpl in H2.
    Elim (option_sum ad*A (MapSweep1 [a0:ad](pf (ad_double a0)) m0)). Intro H4. Elim H4.
    Intros r H5. Rewrite H5 in H2. Inversion H2. Rewrite H7 in H5.
    Apply (H [a0:ad](pf (ad_double a0)) [a0:ad](ad_div_2 (fp a0))). Intro. Rewrite H1.
    Apply ad_double_div_2.
    Assumption.
    Intro H4. Rewrite H4 in H2.
    Elim (MapSweep_semantics_2_1 m1 [a0:ad](pf (ad_double_plus_un a0)) a y H2).
    Intros a0 H5. Rewrite H5 in H3. Rewrite (H1 (ad_double_plus_un a0)) in H3.
    Rewrite (ad_double_plus_un_bit_0 a0) in H3. Discriminate H3.
  Qed.

  Lemma MapSweep_semantics_2 : (m:(Map A)) (a:ad) (y:A)
      (MapSweep m)=(SOME ? (a, y)) -> (MapGet A m a)=(SOME ? y).
  Proof.
    Intros.
    Exact (MapSweep_semantics_2_2 m [a0:ad]a0 [a0:ad]a0 [a0:ad](refl_equal ad a0) a y H).
  Qed.

  Lemma MapSweep_semantics_3_1 : (m:(Map A)) (pf:ad->ad)
      (MapSweep1 pf m)=(NONE ?) ->
        (a:ad) (y:A) (MapGet A m a)=(SOME ? y) -> (f (pf a) y)=false.
  Proof.
    Induction m. Intros. Discriminate H0.
    Simpl. Unfold MapSweep2. Intros a y pf. Elim (sumbool_of_bool (f (pf a) y)). Intro H.
    Rewrite H. Intro. Discriminate H0.
    Intro H. Rewrite H. Intros H0 a0 y0. Elim (sumbool_of_bool (ad_eq a a0)). Intro H1. Rewrite H1.
    Intro H2. Inversion H2. Rewrite <- H4. Rewrite <- (ad_eq_complete ? ? H1). Assumption.
    Intro H1. Rewrite H1. Intro. Discriminate H2.
    Intros. Simpl in H1. Elim (option_sum ad*A (MapSweep1 [a:ad](pf (ad_double a)) m0)).
    Intro H3. Elim H3. Intros r H4. Rewrite H4 in H1. Discriminate H1.
    Intro H3. Rewrite H3 in H1. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H4.
    Rewrite (MapGet_M2_bit_0_1 A a H4 m0 m1) in H2. Rewrite <- (ad_div_2_double_plus_un a H4).
    Exact (H0 [a:ad](pf (ad_double_plus_un a)) H1 (ad_div_2 a) y H2).
    Intro H4. Rewrite (MapGet_M2_bit_0_0 A a H4 m0 m1) in H2. Rewrite <- (ad_div_2_double a H4).
    Exact (H [a:ad](pf (ad_double a)) H3 (ad_div_2 a) y H2).
  Qed.

  Lemma MapSweep_semantics_3 : (m:(Map A))
      (MapSweep m)=(NONE ?) -> (a:ad) (y:A) (MapGet A m a)=(SOME ? y) -> 
        (f a y)=false.
  Proof.
    Intros.
    Exact (MapSweep_semantics_3_1 m [a0:ad]a0 H a y H0).
  Qed.

  Lemma MapSweep_semantics_4_1 : (m:(Map A)) (pf:ad->ad) (a:ad) (y:A)
      (MapGet A m a)=(SOME A y) -> (f (pf a) y)=true ->
      	{a':ad & {y':A | (MapSweep1 pf m)=(SOME ? (a', y'))}}.
  Proof.
    Induction m. Intros. Discriminate H.
    Intros. Elim (sumbool_of_bool (ad_eq a a1)). Intro H1. Split with (pf a1). Split with y.
    Rewrite (ad_eq_complete ? ? H1). Unfold MapSweep1 MapSweep2.
    Rewrite (ad_eq_complete ? ? H1) in H. Rewrite (M1_semantics_1 ? a1 a0) in H.
    Inversion H. Rewrite H0. Reflexivity.

    Intro H1. Rewrite (M1_semantics_2 ? a a1 a0 H1) in H. Discriminate H.

    Intros. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H3.
    Rewrite (MapGet_M2_bit_0_1 ? ? H3 m0 m1) in H1.
    Rewrite <- (ad_div_2_double_plus_un a H3) in H2.
    Elim (H0 [a0:ad](pf (ad_double_plus_un a0)) (ad_div_2 a) y H1 H2). Intros a'' H4. Elim H4.
    Intros y'' H5. Simpl. Elim (option_sum ? (MapSweep1 [a:ad](pf (ad_double a)) m0)).
    Intro H6. Elim H6. Intro r. Elim r. Intros a''' y''' H7. Rewrite H7. Split with a'''.
    Split with y'''. Reflexivity.
    Intro H6. Rewrite H6. Split with a''. Split with y''. Assumption.
    Intro H3. Rewrite (MapGet_M2_bit_0_0 ? ? H3 m0 m1) in H1.
    Rewrite <- (ad_div_2_double a H3) in H2.
    Elim (H [a0:ad](pf (ad_double a0)) (ad_div_2 a) y H1 H2). Intros a'' H4. Elim H4.
    Intros y'' H5. Split with a''. Split with y''. Simpl. Rewrite H5. Reflexivity.
  Qed.

  Lemma MapSweep_semantics_4 : (m:(Map A)) (a:ad) (y:A)
      (MapGet A m a)=(SOME A y) -> (f a y)=true ->
      	{a':ad & {y':A | (MapSweep m)=(SOME ? (a', y'))}}.
  Proof.
    Intros. Exact (MapSweep_semantics_4_1 m [a0:ad]a0 a y H H0).
  Qed.

  End MapSweepDef.

  Variable B : Set.

  Fixpoint MapCollect1 [f:ad->A->(Map B); pf:ad->ad; m:(Map A)] : (Map B) :=
    Cases m of
        M0 => (M0 B)
      | (M1 a y) => (f (pf a) y)
      | (M2 m1 m2) => (MapMerge B (MapCollect1 f [a0:ad] (pf (ad_double a0)) m1)
                                  (MapCollect1 f [a0:ad] (pf (ad_double_plus_un a0)) m2))
    end.

  Definition MapCollect := [f:ad->A->(Map B); m:(Map A)] (MapCollect1 f [a:ad]a m).

  Section MapFoldDef.

    Variable M : Set.
    Variable neutral : M.
    Variable op : M -> M -> M.

    Fixpoint MapFold1 [f:ad->A->M; pf:ad->ad; m:(Map A)] : M :=
      Cases m of
      	  M0 => neutral
        | (M1 a y) => (f (pf a) y)
        | (M2 m1 m2) => (op (MapFold1 f [a0:ad] (pf (ad_double a0)) m1)
                            (MapFold1 f [a0:ad] (pf (ad_double_plus_un a0)) m2))
      end.

    Definition MapFold := [f:ad->A->M; m:(Map A)] (MapFold1 f [a:ad]a m).

    Lemma MapFold_empty : (f:ad->A->M) (MapFold f (M0 A))=neutral.
    Proof.
      Trivial.
    Qed.

    Lemma MapFold_M1 : (f:ad->A->M) (a:ad) (y:A) (MapFold f (M1 A a y)) = (f a y).
    Proof.
      Trivial.
    Qed.

    Variable State : Set.
    Variable f:State -> ad -> A -> State * M.

    Fixpoint MapFold1_state [state:State; pf:ad->ad; m:(Map A)]
                            : State * M :=
      Cases m of
          M0 => (state, neutral)
	| (M1 a y) => (f state (pf a) y)
	| (M2 m1 m2) =>
          Cases (MapFold1_state state [a0:ad] (pf (ad_double a0)) m1) of
              (state1, x1) =>
	      Cases (MapFold1_state state1 [a0:ad] (pf (ad_double_plus_un a0)) m2) of
	          (state2, x2) => (state2, (op x1 x2))
	      end
          end
      end.

    Definition MapFold_state := [state:State] (MapFold1_state state [a:ad]a).

    Lemma pair_sp : (B,C:Set) (x:B*C) x=(Fst x, Snd x).
    Proof.
      Induction x. Trivial.
    Qed.

    Lemma MapFold_state_stateless_1 : (m:(Map A)) (g:ad->A->M) (pf:ad->ad)
        ((state:State) (a:ad) (y:A) (Snd (f state a y))=(g a y)) ->
      	  (state:State)
      	    (Snd (MapFold1_state state pf m))=(MapFold1 g pf m).
    Proof.
      Induction m. Trivial.
      Intros. Simpl. Apply H.
      Intros. Simpl. Rewrite (pair_sp ? ?
          (MapFold1_state state [a0:ad](pf (ad_double a0)) m0)).
      Rewrite (H g [a0:ad](pf (ad_double a0)) H1 state).
      Rewrite (pair_sp ? ?
          (MapFold1_state
            (Fst (MapFold1_state state [a0:ad](pf (ad_double a0)) m0))
            [a0:ad](pf (ad_double_plus_un a0)) m1)).
      Simpl.
      Rewrite (H0 g [a0:ad](pf (ad_double_plus_un a0)) H1
          (Fst (MapFold1_state state [a0:ad](pf (ad_double a0)) m0))).
      Reflexivity.
    Qed.

    Lemma MapFold_state_stateless : (g:ad->A->M)
        ((state:State) (a:ad) (y:A) (Snd (f state a y))=(g a y)) ->
      	  (state:State) (m:(Map A))
      	    (Snd (MapFold_state state m))=(MapFold g m).
    Proof.
      Intros. Exact (MapFold_state_stateless_1 m g [a0:ad]a0 H state).
    Qed.

  End MapFoldDef.

  Lemma MapCollect_as_Fold : (f:ad->A->(Map B)) (m:(Map A))
      (MapCollect f m)=(MapFold (Map B) (M0 B) (MapMerge B) f m).
  Proof.
    Induction m;Trivial.
  Qed.

  Definition alist := (list (ad*A)).
  Definition anil := (nil (ad*A)).
  Definition acons := (!cons (ad*A)).
  Definition aapp := (!app (ad*A)).

  Definition alist_of_Map := (MapFold alist anil aapp [a:ad;y:A] (acons (pair ? ? a y) anil)).

  Fixpoint alist_semantics [l:alist] : ad -> (option A) :=
    Cases l of
        nil => [_:ad] (NONE A)
      | (cons (a, y) l') => [a0:ad] if (ad_eq a a0) then (SOME A y) else (alist_semantics l' a0)
    end.

  Lemma alist_semantics_app : (l,l':alist) (a:ad)
      (alist_semantics (aapp l l') a)=
      (Cases (alist_semantics l a) of
           NONE => (alist_semantics l' a)
	 | (SOME y) => (SOME A y)
       end).
  Proof.
    Unfold aapp. Induction l. Trivial.
    Intros. Elim a. Intros a1 y1. Simpl. Case (ad_eq a1 a0). Reflexivity.
    Apply H.
  Qed.

  Lemma alist_of_Map_semantics_1_1 : (m:(Map A)) (pf:ad->ad) (a:ad) (y:A)
      (alist_semantics (MapFold1 alist anil aapp [a0:ad][y:A](acons (a0,y) anil) pf m) a)
      =(SOME A y) -> {a':ad | a=(pf a')}.
  Proof.
    Induction m. Simpl. Intros. Discriminate H.
    Simpl. Intros a y pf a0 y0. Elim (sumbool_of_bool (ad_eq (pf a) a0)). Intro H. Rewrite H.
    Intro H0. Split with a. Rewrite (ad_eq_complete ? ? H). Reflexivity.
    Intro H. Rewrite H. Intro H0. Discriminate H0.
    Intros. Change (alist_semantics
         (aapp
           (MapFold1 alist anil aapp [a0:ad][y:A](acons (a0,y) anil)
             [a0:ad](pf (ad_double a0)) m0)
           (MapFold1 alist anil aapp [a0:ad][y:A](acons (a0,y) anil)
             [a0:ad](pf (ad_double_plus_un a0)) m1)) a)=(SOME A y)  in H1.
    Rewrite (alist_semantics_app
          (MapFold1 alist anil aapp [a0:ad][y0:A](acons (a0,y0) anil)
            [a0:ad](pf (ad_double a0)) m0)
          (MapFold1 alist anil aapp [a0:ad][y0:A](acons (a0,y0) anil)
            [a0:ad](pf (ad_double_plus_un a0)) m1) a) in H1.
    Elim (option_sum A
       (alist_semantics
         (MapFold1 alist anil aapp [a0:ad][y0:A](acons (a0,y0) anil)
           [a0:ad](pf (ad_double a0)) m0) a)).
    Intro H2. Elim H2. Intros y0 H3. Elim (H [a0:ad](pf (ad_double a0)) a y0 H3). Intros a0 H4.
    Split with (ad_double a0). Assumption.
    Intro H2. Rewrite H2 in H1. Elim (H0 [a0:ad](pf (ad_double_plus_un a0)) a y H1).
    Intros a0 H3. Split with (ad_double_plus_un a0). Assumption.
  Qed.

  Definition ad_inj := [pf:ad->ad] (a0,a1:ad) (pf a0)=(pf a1) -> a0=a1.

  Lemma ad_comp_double_inj : 
      (pf:ad->ad) (ad_inj pf) -> (ad_inj [a0:ad] (pf (ad_double a0))).
  Proof.
    Unfold ad_inj. Intros. Apply ad_double_inj. Exact (H ? ? H0).
  Qed.

  Lemma ad_comp_double_plus_un_inj : (pf:ad->ad) (ad_inj pf) ->
      (ad_inj [a0:ad] (pf (ad_double_plus_un a0))).
  Proof.
    Unfold ad_inj. Intros. Apply ad_double_plus_un_inj. Exact (H ? ? H0).
  Qed.

  Lemma alist_of_Map_semantics_1 : (m:(Map A)) (pf:ad->ad) (ad_inj pf) ->
      (a:ad) (MapGet A m a)=(alist_semantics (MapFold1 alist anil aapp
                                                   [a0:ad;y:A] (acons (pair ? ? a0 y) anil) pf m)
                                      (pf a)).
  Proof.
    Induction m. Trivial.
    Simpl. Intros. Elim (sumbool_of_bool (ad_eq a a1)). Intro H0. Rewrite H0.
    Rewrite (ad_eq_complete ? ? H0). Rewrite (ad_eq_correct (pf a1)). Reflexivity.
    Intro H0. Rewrite H0. Elim (sumbool_of_bool (ad_eq (pf a) (pf a1))). Intro H1.
    Rewrite (H a a1 (ad_eq_complete ? ? H1)) in H0. Rewrite (ad_eq_correct a1) in H0.
    Discriminate H0.
    Intro H1. Rewrite H1. Reflexivity.
    Intros. Change (MapGet A (M2 A m0 m1) a)
        =(alist_semantics
           (aapp
             (MapFold1 alist anil aapp [a0:ad][y:A](acons (a0,y) anil)
               [a0:ad](pf (ad_double a0)) m0)
             (MapFold1 alist anil aapp [a0:ad][y:A](acons (a0,y) anil)
               [a0:ad](pf (ad_double_plus_un a0)) m1)) (pf a)).
    Rewrite alist_semantics_app. Rewrite (MapGet_M2_bit_0_if A m0 m1 a).
    Elim (ad_double_or_double_plus_un a). Intro H2. Elim H2. Intros a0 H3. Rewrite H3.
    Rewrite (ad_double_bit_0 a0).
    Rewrite <- (H [a1:ad](pf (ad_double a1)) (ad_comp_double_inj pf H1) a0).
    Rewrite ad_double_div_2. Case (MapGet A m0 a0).
    Elim (option_sum A
       (alist_semantics
         (MapFold1 alist anil aapp [a1:ad][y:A](acons (a1,y) anil)
           [a1:ad](pf (ad_double_plus_un a1)) m1) (pf (ad_double a0)))).
    Intro H4. Elim H4. Intros y H5.
    Elim (alist_of_Map_semantics_1_1 m1 [a1:ad](pf (ad_double_plus_un a1))
          (pf (ad_double a0)) y H5).
    Intros a1 H6. Cut (ad_bit_0 (ad_double a0))=(ad_bit_0 (ad_double_plus_un a1)).
    Intro. Rewrite (ad_double_bit_0 a0) in H7. Rewrite (ad_double_plus_un_bit_0 a1) in H7.
    Discriminate H7.
    Rewrite (H1 (ad_double a0) (ad_double_plus_un a1) H6). Reflexivity.
    Intro H4. Rewrite H4. Reflexivity.
    Trivial.
    Intro H2. Elim H2. Intros a0 H3. Rewrite H3. Rewrite (ad_double_plus_un_bit_0 a0).
    Rewrite <- (H0 [a1:ad](pf (ad_double_plus_un a1)) (ad_comp_double_plus_un_inj pf H1) a0).
    Rewrite ad_double_plus_un_div_2.
    Elim (option_sum A
       (alist_semantics
         (MapFold1 alist anil aapp [a1:ad][y:A](acons (a1,y) anil)
           [a1:ad](pf (ad_double a1)) m0) (pf (ad_double_plus_un a0)))).
    Intro H4. Elim H4. Intros y H5.
    Elim (alist_of_Map_semantics_1_1 m0 [a1:ad](pf (ad_double a1))
       (pf (ad_double_plus_un a0)) y H5).
    Intros a1 H6. Cut (ad_bit_0 (ad_double_plus_un a0))=(ad_bit_0 (ad_double a1)).
    Intro H7. Rewrite (ad_double_plus_un_bit_0 a0) in H7. Rewrite (ad_double_bit_0 a1) in H7.
    Discriminate H7.
    Rewrite (H1 (ad_double_plus_un a0) (ad_double a1) H6). Reflexivity.
    Intro H4. Rewrite H4. Reflexivity.
  Qed.

  Lemma alist_of_Map_semantics : (m:(Map A))
      (eqm A (MapGet A m) (alist_semantics (alist_of_Map m))).
  Proof.
    Unfold eqm. Intros. Exact (alist_of_Map_semantics_1 m [a0:ad]a0 [a0,a1:ad][p:a0=a1]p a).
  Qed.

  Fixpoint Map_of_alist [l:alist] : (Map A) :=
    Cases l of
        nil => (M0 A)
      | (cons (a, y) l') => (MapPut A (Map_of_alist l') a y)
    end.

  Lemma Map_of_alist_semantics : (l:alist)
      (eqm A (alist_semantics l) (MapGet A (Map_of_alist l))).
  Proof.
    Unfold eqm. Induction l. Trivial.
    Intros r l0 H a. Elim r. Intros a0 y0. Simpl. Elim (sumbool_of_bool (ad_eq a0 a)).
    Intro H0. Rewrite H0. Rewrite (ad_eq_complete ? ? H0).
    Rewrite (MapPut_semantics A (Map_of_alist l0) a y0 a). Rewrite (ad_eq_correct a).
    Reflexivity.
    Intro H0. Rewrite H0. Rewrite (MapPut_semantics A (Map_of_alist l0) a0 y0 a).
    Rewrite H0. Apply H.
  Qed.

  Lemma Map_of_alist_of_Map : (m:(Map A)) (eqmap A (Map_of_alist (alist_of_Map m)) m).
  Proof.
    Unfold eqmap. Intro. Apply eqm_trans with f':=(alist_semantics (alist_of_Map m)).
    Apply eqm_sym. Apply Map_of_alist_semantics.
    Apply eqm_sym. Apply alist_of_Map_semantics.
  Qed.

  Lemma alist_of_Map_of_alist : (l:alist)
      (eqm A (alist_semantics (alist_of_Map (Map_of_alist l))) (alist_semantics l)).
  Proof.
    Intro. Apply eqm_trans with f':=(MapGet A (Map_of_alist l)).
    Apply eqm_sym. Apply alist_of_Map_semantics.
    Apply eqm_sym. Apply Map_of_alist_semantics.
  Qed.

  Lemma fold_right_aapp : (M:Set) (neutral:M) (op:M->M->M)
      ((a,b,c:M) (op (op a b) c)=(op a (op b c))) ->
      ((a:M) (op neutral a)=a) ->
      (f:ad->A->M) (l,l':alist)
        (fold_right [r:ad*A][m:M] let (a,y)=r in (op (f a y) m) neutral
                    (aapp l l'))=
        (op (fold_right [r:ad*A][m:M] let (a,y)=r in (op (f a y) m) neutral l)
            (fold_right [r:ad*A][m:M] let (a,y)=r in (op (f a y) m) neutral l'))
.
  Proof.
    Induction l. Simpl. Intro. Rewrite H0. Reflexivity.
    Intros r l0 H1 l'. Elim r. Intros a y. Simpl. Rewrite H. Rewrite (H1 l'). Reflexivity.
  Qed.

  Lemma MapFold_as_fold_1 : (M:Set) (neutral:M) (op:M->M->M)
      ((a,b,c:M) (op (op a b) c)=(op a (op b c))) ->
      ((a:M) (op neutral a)=a) ->
      ((a:M) (op a neutral)=a) ->
        (f:ad->A->M) (m:(Map A)) (pf:ad->ad)
         (MapFold1 M neutral op f pf m)=
         (fold_right [r:(ad*A)][m:M] let (a,y)=r in (op (f a y) m) neutral
                    (MapFold1 alist anil aapp [a:ad;y:A] (acons (pair ? ? 
a y) anil) pf m)).
  Proof.
    Induction m. Trivial.
    Intros. Simpl. Rewrite H1. Reflexivity.
    Intros. Simpl. Rewrite (fold_right_aapp M neutral op H H0 f).
    Rewrite (H2 [a0:ad](pf (ad_double a0))). Rewrite (H3 [a0:ad](pf (ad_double_plus_un a0))).
    Reflexivity.
  Qed.

  Lemma MapFold_as_fold : (M:Set) (neutral:M) (op:M->M->M)
      ((a,b,c:M) (op (op a b) c)=(op a (op b c))) ->
      ((a:M) (op neutral a)=a) ->
      ((a:M) (op a neutral)=a) ->
        (f:ad->A->M) (m:(Map A))
         (MapFold M neutral op f m)=
         (fold_right [r:(ad*A)][m:M] let (a,y)=r in (op (f a y) m) neutral
  (alist_of_Map m)).
  Proof.
    Intros. Exact (MapFold_as_fold_1 M neutral op H H0 H1 f m [a0:ad]a0).
  Qed.

  Lemma alist_MapMerge_semantics : (m,m':(Map A))
      (eqm A (alist_semantics (aapp (alist_of_Map m') (alist_of_Map m)))
             (alist_semantics (alist_of_Map (MapMerge A m m')))).
  Proof.
    Unfold eqm. Intros. Rewrite alist_semantics_app. Rewrite <- (alist_of_Map_semantics m a).
    Rewrite <- (alist_of_Map_semantics m' a).
    Rewrite <- (alist_of_Map_semantics (MapMerge A m m') a).
    Rewrite (MapMerge_semantics A m m' a). Reflexivity.
  Qed.

  Lemma alist_MapMerge_semantics_disjoint : (m,m':(Map A))
        (eqmap A (MapDomRestrTo A A m m') (M0 A)) ->
	  (eqm A (alist_semantics (aapp (alist_of_Map m) (alist_of_Map m')))
	         (alist_semantics (alist_of_Map (MapMerge A m m')))).
  Proof.
    Unfold eqm. Intros. Rewrite alist_semantics_app. Rewrite <- (alist_of_Map_semantics m a).
    Rewrite <- (alist_of_Map_semantics m' a).
    Rewrite <- (alist_of_Map_semantics (MapMerge A m m') a). Rewrite (MapMerge_semantics A m m' a).
    Elim (option_sum ? (MapGet A m a)). Intro H0. Elim H0. Intros y H1. Rewrite H1.
    Elim (option_sum ? (MapGet A m' a)). Intro H2. Elim H2. Intros y' H3.
    Cut (MapGet A (MapDomRestrTo A A m m') a)=(NONE A).
    Rewrite (MapDomRestrTo_semantics A A m m' a). Rewrite H3. Rewrite H1. Intro. Discriminate H4.
    Exact (H a).
    Intro H2. Rewrite H2. Reflexivity.
    Intro H0. Rewrite H0. Case (MapGet A m' a); Trivial.
  Qed.

  Lemma alist_semantics_disjoint_comm : (l,l':alist)
      (eqmap A (MapDomRestrTo A A (Map_of_alist l) (Map_of_alist l')) (M0 A)) ->
      	(eqm A (alist_semantics (aapp l l')) (alist_semantics (aapp l' l))).
  Proof.
    Unfold eqm. Intros. Rewrite (alist_semantics_app l l' a). Rewrite (alist_semantics_app l' l a).
    Rewrite <- (alist_of_Map_of_alist l a). Rewrite <- (alist_of_Map_of_alist l' a).
    Rewrite <- (alist_semantics_app (alist_of_Map (Map_of_alist l))
                                    (alist_of_Map (Map_of_alist l')) a).
    Rewrite <- (alist_semantics_app (alist_of_Map (Map_of_alist l'))
                                    (alist_of_Map (Map_of_alist l)) a).
    Rewrite (alist_MapMerge_semantics (Map_of_alist l) (Map_of_alist l') a).
    Rewrite (alist_MapMerge_semantics_disjoint (Map_of_alist l) (Map_of_alist l') H a).
    Reflexivity.
  Qed.

End MapIter.

