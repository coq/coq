Require Import Uint63.
Require Export PrimString.
Require Export PrimStringAxioms.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.ZifyUint63.
Require Import Coq.micromega.Zify.
Require Import Coq.Numbers.Cyclic.Int63.Ring63.
Require Import ZArith.

#[local] Open Scope Z_scope.
#[local] Open Scope list_scope.
#[local] Arguments to_Z _/ : simpl nomatch.

#[local] Ltac case_if :=
  lazymatch goal with
  | |- context C [if ?b then _ else _] => destruct b eqn:?
  | H : context C [if ?b then _ else _] |- _ => destruct b eqn:?
  end.

(** Derived properties of to_list and of_list. *)

Lemma to_list_inj (s1 s2 : string) :
  to_list s1 = to_list s2 -> s1 = s2.
Proof.
  intros H. rewrite <-(of_to_list s1), <-(of_to_list s2), H.
  reflexivity.
Qed.

Lemma to_of_list (l : list char63) :
  List.Forall char63_valid l ->
  Z.of_nat (List.length l) <= to_Z max_length ->
  to_list (of_list l) = l.
Proof.
  induction l as [|c l IH]; simpl; intros Hvalid Hlen; [reflexivity|].
  apply List.Forall_cons_iff in Hvalid as [Hvalid1 Hvalid2].
  rewrite cat_spec, make_spec, Hvalid1, IH; [|assumption|simpl; lia].
  rewrite List.firstn_all2; [reflexivity|simpl; lia].
Qed.

(** Alternative specifications with explicit bounds. *)

Lemma get_spec_in_bounds (s : string) (i : int) :
  to_Z i < to_Z (length s) ->
  char63_valid (get s i) /\
  List.nth_error (to_list s) (to_nat i) = Some (get s i).
Proof.
  intros Hlt. rewrite get_spec. split.
  - pose proof to_list_char63_valid s as Hs.
    apply List.Forall_nth; [assumption|]. rewrite <-length_spec. lia.
  - apply List.nth_error_nth'. rewrite <-length_spec. lia.
Qed.

Lemma get_spec_not_in_bounds (s : string) (i : int) :
  to_Z (length s) <= to_Z i ->
  get s i = 0%uint63.
Proof.
  intros Hle. rewrite get_spec, List.nth_overflow; [reflexivity|].
  rewrite <-length_spec. lia.
Qed.

Lemma make_spec_valid_length (i : int) (c : char63) :
  to_Z i <= to_Z max_length ->
  to_list (make i c) = List.repeat (c land 255)%uint63 (to_nat i).
Proof.
  intros Hle. rewrite make_spec, Nat.min_l; [reflexivity | lia].
Qed.

Lemma make_spec_invalid_length (i : int) (c : char63) :
  to_Z max_length < to_Z i ->
  to_list (make i c) = List.repeat (c land 255)%uint63 (to_nat max_length).
Proof.
  intros Hle. rewrite make_spec, Nat.min_r; [reflexivity | lia].
Qed.

Lemma cat_spec_valid_length (s1 s2 : string) :
  to_Z (length s1) + to_Z (length s2) <= to_Z max_length ->
  to_list (cat s1 s2) = to_list s1 ++ to_list s2.
Proof.
  intros Hlen. rewrite cat_spec, List.firstn_all2; [reflexivity|].
  rewrite List.length_app, <-!length_spec. lia.
Qed.

(** * Properties of string length *)

Lemma valid_length (s : string) :
  to_Z (length s) <= to_Z max_length.
Proof.
  pose proof (to_list_length s) as Hvalid.
  rewrite <-(length_spec s) in Hvalid. lia.
Qed.

Lemma length_spec_int (s : string) :
  length s = of_Z (Z.of_nat (List.length (to_list s))).
Proof.
  apply to_Z_inj. rewrite <-length_spec.
  rewrite of_Z_spec, Z.mod_small, Z2Nat.id; lia.
Qed.

Lemma length_spec_Z (s : string) :
  to_Z (length s) = Z.of_nat (List.length (to_list s)).
Proof.
  rewrite <-length_spec. rewrite Z2Nat.id; lia.
Qed.

Lemma make_length_spec (i : int) (c : char63) :
  to_Z i <= to_Z max_length ->
  length (make i c) = i.
Proof.
  intros Hvalid.
  pose proof (length_spec (make i c)) as Hlen.
  rewrite (make_spec_valid_length i c Hvalid) in Hlen.
  rewrite List.repeat_length in Hlen. lia.
Qed.

Lemma sub_length_spec (s : string) (off len : int) :
  to_Z off <= to_Z (length s) ->
  to_Z len <= to_Z (length s) - to_Z off ->
  length (sub s off len) = len.
Proof.
  intros Hoff Hlen.
  pose proof (length_spec (sub s off len)) as Hs.
  rewrite sub_spec, List.firstn_length_le in Hs; [lia|].
  rewrite List.length_skipn, <-length_spec. lia.
Qed.

Lemma cat_length_spec (s1 s2 : string) :
  length (cat s1 s2) = Uint63.min max_length (length s1 + length s2)%uint63.
Proof.
  rewrite length_spec_int, cat_spec, List.length_firstn.
  rewrite Nat2Z.inj_min, Z2Nat.id; [|lia].
  rewrite List.length_app, <-!length_spec.
  rewrite <-Z2Nat.inj_add; [|lia|lia].
  rewrite Z2Nat.id; [|lia].
  assert (to_Z (length s1) + to_Z (length s2) =
            (to_Z (length s1) + to_Z (length s2)) mod wB) as ->.
  { rewrite Z.mod_small; [reflexivity|]. split; [lia|].
    pose proof valid_length s1 as Hs1.
    pose proof valid_length s2 as Hs2.
    simpl in *. lia. }
  rewrite <-add_spec, <-Uint63.min_spec, of_to_Z. reflexivity.
Qed.

Lemma cat_length_spec_no_overflow (s1 s2 : string) :
  to_Z (length s1) + to_Z (length s2) <= to_Z max_length ->
  length (cat s1 s2) = (length s1 + length s2)%uint63.
Proof.
  intros Hlen. rewrite cat_length_spec. unfold min.
  destruct (max_length ≤? length s1 + length s2)%uint63 eqn:Hle; [|reflexivity].
  rewrite leb_spec, add_spec, Z.mod_small in Hle; [|lia].
  apply to_Z_inj. rewrite add_spec, Z.mod_small; lia.
Qed.

(** * Properties of string get *)

Lemma get_char63_valid (s : string) (i : int) :
  char63_valid (get s i).
Proof.
  rewrite get_spec.
  destruct (to_nat i <? Datatypes.length (to_list s))%nat eqn:Hlt.
  - pose proof to_list_char63_valid s as Hvalid.
    apply List.Forall_nth; [assumption|lia].
  - rewrite List.nth_overflow; [reflexivity|lia].
Qed.

Lemma make_get_spec (i j : int) (c : char63) :
  to_Z j < to_Z max_length ->
  to_Z j < to_Z i ->
  get (make i c) j = (c land 255)%uint63.
Proof.
  intros Hmax Hj. rewrite get_spec, make_spec.
  rewrite List.nth_repeat_lt; [reflexivity|lia].
Qed.

Lemma make_get_spec_valid (i j : int) (c : char63) :
  to_Z j < to_Z max_length ->
  to_Z j < to_Z i ->
  char63_valid c ->
  get (make i c) j = c.
Proof.
  intros. rewrite make_get_spec; assumption.
Qed.

Lemma sub_get_spec (s : string) (off len i : int) :
  to_Z off + to_Z i < wB ->
  to_Z i < to_Z len ->
  get (sub s off len) i = get s (off + i).
Proof.
  intros Hno Hi.
  rewrite !get_spec, sub_spec.
  rewrite List.nth_firstn, List.nth_skipn. case_if; [|lia].
  f_equal. rewrite Uint63.add_spec, Z.mod_small; lia.
Qed.

Lemma cat_get_spec_l (s1 s2 : string) (i : int) :
  to_Z i < to_Z (length s1) ->
  get (cat s1 s2) i = get s1 i.
Proof.
  intros Hi.
  pose proof valid_length s1 as Hs1.
  rewrite !get_spec, cat_spec.
  rewrite List.nth_firstn. case_if; [|lia].
  rewrite List.app_nth1; [reflexivity|].
  rewrite <-length_spec. lia.
Qed.

Lemma cat_get_spec_r (s1 s2 : string) (i : int) :
  to_Z (length s1) <= to_Z i ->
  to_Z i < to_Z max_length ->
  get (cat s1 s2) i = get s2 (i - length s1).
Proof.
  intros H1 H2.
  rewrite !get_spec, cat_spec.
  rewrite List.nth_firstn. case_if; [|lia].
  rewrite List.app_nth2; [|rewrite <-length_spec; lia].
  rewrite <-length_spec, Uint63.sub_spec, Z.mod_small; [|lia].
  rewrite Z2Nat.inj_sub; [reflexivity|lia].
Qed.

(** * Properties of string comparison *)


Lemma char63_compare_refl (c1 c2 : char63) :
  char63_compare c1 c2 = Eq <-> c1 = c2.
Proof.
  rewrite Uint63.compare_spec, Z.compare_eq_iff.
  split; [apply to_Z_inj|intros <-; reflexivity].
Qed.

Lemma compare_eq_correct (s1 s2 : string) :
  compare s1 s2 = Eq -> s1 = s2.
Proof.
  rewrite compare_spec, (List.list_compare_refl _ char63_compare_refl).
  apply to_list_inj.
Qed.

Lemma string_eq_ext (s1 s2 : string) :
  (length s1 = length s2 /\
     forall i, to_Z i < to_Z (length s1) -> get s1 i = get s2 i) ->
  s1 = s2.
Proof.
  intros [Hlen Hget]. apply to_list_inj.
  apply (List.nth_ext _ _ 0%uint63 0%uint63).
  + rewrite <-!length_spec, Hlen. reflexivity.
  + intros n Hn. rewrite <-length_spec in Hn.
    assert (n = to_nat (of_nat n)) as ->.
    { rewrite of_Z_spec, Z.mod_small, Nat2Z.id; lia. }
    rewrite <-!get_spec. apply Hget.
    rewrite of_Z_spec, Z.mod_small; lia.
Qed.

Lemma compare_spec (s1 s2 : string) (c : comparison) :
  compare s1 s2 = c <->
  exists i,
    to_Z i <= to_Z (length s1) /\
    to_Z i <= to_Z (length s2) /\
    (forall j, to_Z j < to_Z i -> get s1 j = get s2 j) /\
    match (i =? length s1, i =? length s2)%uint63 with
    | (true , true ) => c = Eq
    | (true , false) => c = Lt
    | (false, true ) => c = Gt
    | (false, false) =>
        match Uint63.compare (get s1 i) (get s2 i) with
        | Eq => False
        | ci => c = ci
        end
    end.
Proof.
  rewrite compare_spec, (List.list_compare_prefix_spec _ char63_compare_refl).
  split.
  - intros (prefix & xs' & ys' & H1 & H2 & H).
    exists (of_Z (Z.of_nat (List.length prefix))).
    assert (Z.of_nat (Datatypes.length prefix) <= to_Z max_length) as Hltmax.
    { transitivity (Z.of_nat (List.length (to_list s1))).
      - rewrite H1, List.length_app. simpl. lia.
      - pose proof to_list_length s1; lia. }
    simpl in Hltmax.
    rewrite !length_spec_Z, H1, H2, !List.length_app.
    rewrite of_Z_spec, Z.mod_small; [|lia].
    repeat split.
    + lia.
    + lia.
    + intros j Hj. rewrite !get_spec.
      rewrite H1, H2, !List.app_nth1; [reflexivity | lia | lia].
    + pose proof length_spec s1 as Hlen1.
      pose proof length_spec s2 as Hlen2.
      rewrite !length_spec_int, H1, H2, !List.length_app, !eqb_eq.
      rewrite H1, List.length_app in Hlen1.
      rewrite H2, List.length_app in Hlen2.
      rewrite !of_Z_spec, !Z.mod_small; try (rewrite <-?Hlen1, <-?Hlen2; lia).
      destruct xs' as [|x xs']; simpl; case_if; try lia.
      { destruct ys' as [|y ys']; simpl.
        - rewrite Nat.add_0_r, Z.eqb_refl. assumption.
        - case_if; [exfalso; lia | assumption]. }
      destruct ys' as [|y ys']; simpl; case_if; try lia; try assumption.
      rewrite !get_spec, H1, H2.
      rewrite !of_Z_spec, !Z.mod_small, Nat2Z.id; [|lia].
      rewrite !List.nth_middle. assumption.
  - intros (i & Hs1 & Hs2 & Hget & H).
    exists (List.firstn (to_nat i) (to_list s1)).
    exists (List.skipn (to_nat i) (to_list s1)).
    exists (List.skipn (to_nat i) (to_list s2)).
    assert (List.firstn (to_nat i) (to_list s1) = List.firstn (to_nat i) (to_list s2)) as Heq.
    { apply (List.nth_ext _ _ 0%uint63 0%uint63).
      - rewrite !List.length_firstn. rewrite !Nat.min_l; [reflexivity| |].
        all: rewrite <-length_spec; lia.
      - rewrite List.length_firstn, Nat.min_l.
        2: rewrite <-length_spec; lia.
        intros n Hn.
        assert ((of_Z (Z.of_nat n) <? i)%uint63 = true) as Hi.
        { apply ltb_spec. rewrite of_Z_spec, Z.mod_small; lia. }
        pose proof Hget (of_Z (Z.of_nat n)) ltac:(lia) as Hget.
        rewrite !get_spec in Hget.
        rewrite of_Z_spec, Z.mod_small, Nat2Z.id in Hget; [|lia].
        rewrite !List.nth_firstn. repeat case_if; lia. }
    rewrite Heq at 2. rewrite !List.firstn_skipn. repeat split.
    destruct (i =? length s1)%uint63 eqn:His1.
    + rewrite (List.skipn_all2 (to_list s1)).
      2: rewrite <-length_spec; lia.
      destruct (i =? length s2)%uint63 eqn:His2.
      * rewrite (List.skipn_all2 (to_list s2)).
        2: rewrite <-length_spec; lia.
        assumption.
      * destruct (List.skipn (to_nat i) (to_list s2)) eqn:Hskip; [|assumption].
        exfalso. apply List.skipn_all_iff in Hskip.
        rewrite <-length_spec in Hskip. lia.
    + destruct (List.skipn (to_nat i) (to_list s1)) eqn:Hskip1.
      { exfalso. apply List.skipn_all_iff in Hskip1. rewrite <-length_spec in Hskip1. lia. }
      destruct (i =? length s2)%uint63 eqn:His2.
      { rewrite List.skipn_all2; [assumption|]. rewrite <-length_spec. lia. }
      destruct (List.skipn (to_nat i) (to_list s2)) eqn:Hskip2.
      { exfalso. apply List.skipn_all_iff in Hskip2. rewrite <-length_spec in Hskip2. lia. }
      assert (c0 = get s1 i) as ->.
      { assert (List.nth_error (List.skipn (to_nat i) (to_list s1)) 0 = Some c0) as Hc0.
        { rewrite Hskip1. reflexivity. }
        rewrite List.nth_error_skipn, Nat.add_0_r in Hc0.
        rewrite get_spec.
        eapply List.nth_error_nth in Hc0. rewrite Hc0. reflexivity. }
      assert (c1 = get s2 i) as ->.
      { assert (List.nth_error (List.skipn (to_nat i) (to_list s2)) 0 = Some c1) as Hc1.
        { rewrite Hskip2. reflexivity. }
        rewrite List.nth_error_skipn, Nat.add_0_r in Hc1.
        rewrite get_spec.
        eapply List.nth_error_nth in Hc1. rewrite Hc1. reflexivity. }
      assumption.
Qed.

Lemma compare_refl (s : string) : compare s s = Eq.
Proof.
  rewrite PrimStringAxioms.compare_spec.
  apply (List.list_compare_refl _ char63_compare_refl). reflexivity.
Qed.

Lemma compare_eq (s1 s2 : string) : compare s1 s2 = Eq <-> s1 = s2.
Proof. split; [apply compare_eq_correct|intros []; apply compare_refl]. Qed.

Lemma compare_antisym (s1 s2 : string) : compare s2 s1 = CompOpp (compare s1 s2).
Proof.
  pose proof (proj1 (compare_spec s1 s2 (compare s1 s2)) eq_refl) as Hcmp.
  destruct Hcmp as (i & Hs1 & Hs2 & Hget & H).
  rewrite compare_spec. exists i. repeat split.
  - assumption.
  - assumption.
  - intros j Hj. symmetry. apply Hget. assumption.
  - repeat case_if; try (rewrite H; reflexivity).
    revert H. rewrite !Uint63.compare_spec, Z.compare_antisym.
    destruct (to_Z (get s2 i) ?= to_Z (get s1 i)) eqn:Hcmp; simpl.
    + intros Hfalse. exact Hfalse.
    + intros ->. reflexivity.
    + intros ->. reflexivity.
Qed.

Lemma compare_lt_spec (s1 s2 : string) :
  compare s1 s2 = Lt <->
  exists i,
    to_Z i <= to_Z (length s1) /\
    to_Z i <= to_Z (length s2) /\
    (forall j, to_Z j < to_Z i -> get s1 j = get s2 j) /\
    ((i = length s1 /\ to_Z i < to_Z (length s2)) \/
     (to_Z i < to_Z (length s1) /\
      to_Z i < to_Z (length s2) /\
      char63_compare (get s1 i) (get s2 i) = Lt)).
Proof.
  rewrite compare_spec.
  setoid_rewrite Uint63.compare_def_spec; unfold compare_def.
  split.
  - intros [i (H1 & H2 & Hget & Heq)]; exists i.
    repeat split; [assumption..|].
    repeat case_if; try inversion Heq; try lia.
    right. repeat split; lia.
  - intros [i (H1 & H2 & Hget & H)]; exists i.
    repeat split; [assumption..|].
    destruct H as [(-> & Hi)|(Hi1 & Hi2 & H)].
    + repeat case_if; try reflexivity; lia.
    + repeat case_if; try reflexivity; try inversion H; lia.
Qed.

Lemma compare_trans (c : comparison) (s1 s2 s3 : string) :
  compare s1 s2 = c -> compare s2 s3 = c -> compare s1 s3 = c.
Proof.
  rewrite !compare_spec.
  setoid_rewrite Uint63.compare_def_spec; unfold compare_def.
  intros [i1 (Hi1s1&Hi1s2&Hi1&H1)] [i2 (Hi2s2&Hi2s3&Hi2&H2)].
  destruct (i1 <? i2)%uint63 eqn:Hlt; [exists i1 | exists i2]; repeat split; try lia.
  - intros j Hji1.
    assert ((j <? i2)%uint63 = true) as Hji2 by lia.
    pose proof (Hi1 j Hji1) as Hj1.
    pose proof (Hi2 j ltac:(lia)) as Hj2.
    revert Hj1 Hj2. intros -> <-. reflexivity.
  - clear H2; revert H1.
    assert (get s2 i1 = get s3 i1) as Hs2s3. { apply Hi2. lia. }
    repeat case_if; intros H1; try assumption; try lia; try subst c.
  - intros j Hji2.
    assert ((j <? i1)%uint63 = true) as Hji1 by lia.
    pose proof (Hi1 j ltac:(lia)) as Hj1.
    pose proof (Hi2 j Hji2) as Hj2.
    revert Hj1 Hj2. intros -> <-. reflexivity.
  - destruct (i1 =? i2)%uint63 eqn:Heqi1i2.
    + apply eqb_spec in Heqi1i2. subst i2. revert H1 H2.
      repeat case_if.
      all: intros H1; try rewrite H1; try inversion H1.
      all: intros H2; try rewrite H2; try inversion H2.
      all: try reflexivity; lia.
    + clear H1; revert H2.
      assert (get s1 i2 = get s2 i2) as Hs1s2. { apply Hi1. lia. }
      repeat case_if; intros H1; try assumption; try lia; try subst c.
Qed.

(** * Properties of make *)

Lemma make_0 (c : char63) : make 0 c = ""%pstring.
Proof.
  apply to_list_inj. rewrite make_spec. reflexivity.
Qed.

(** * Properties of cat *)

Lemma length_0_empty (s : string) : length s = 0%uint63 -> s = ""%pstring.
Proof.
  pose proof valid_length s as Hs. rewrite length_spec_Z in Hs.
  rewrite length_spec_int. intros H%eq_int_inj.
  rewrite of_Z_spec, Z.mod_small in H; [|lia].
  apply to_list_inj. destruct (to_list s); simpl in *; [reflexivity|lia].
Qed.

Lemma cat_empty_l (s : string) : cat ""%pstring s = s.
Proof.
  pose proof valid_length s as Hs.
  apply string_eq_ext. split.
  - rewrite cat_length_spec_no_overflow; simpl; [ring|assumption].
  - intros i Hi.
    rewrite cat_length_spec_no_overflow in Hi; [|simpl in * |- *; lia].
    simpl in Hi. ring_simplify (0 + length s)%uint63 in Hi.
    rewrite cat_get_spec_r; simpl in *; [|lia|lia].
    ring_simplify (i - 0)%uint63. reflexivity.
Qed.

Lemma cat_empty_r (s : string) : cat s ""%pstring = s.
Proof.
  pose proof valid_length s as Hs.
  apply string_eq_ext. split.
  - rewrite cat_length_spec_no_overflow; simpl in *; [ring|lia].
  - intros i Hi.
    rewrite cat_length_spec_no_overflow in Hi; [|simpl in * |- *; lia].
    simpl in Hi. ring_simplify (length s + 0)%uint63 in Hi.
    rewrite cat_get_spec_l; [reflexivity|assumption].
Qed.

Lemma cat_assoc (s1 s2 s3 : string) :
  cat (cat s1 s2) s3 = cat s1 (cat s2 s3).
Proof.
  apply string_eq_ext.
  rewrite !cat_length_spec.
  pose proof valid_length s1 as Hs1.
  pose proof valid_length s2 as Hs2.
  pose proof valid_length s3 as Hs3.
  simpl in *.
  rewrite !min_add_min_n_same; [|rewrite add_spec, Z.mod_small; lia].
  rewrite !min_add_n_min_same; [|rewrite add_spec, Z.mod_small; lia].
  split; [f_equal; ring|]. intros i Hi.
  rewrite !get_spec, !cat_spec.
  rewrite Uint63.min_spec, !add_spec, !Z.mod_small in Hi.
  2-3: repeat rewrite Z.mod_small; lia.
  rewrite !List.nth_firstn.
  case_if; [|reflexivity].
  destruct (to_Z i <? to_Z (length s1)) eqn:Hlen1.
  { rewrite !List.app_nth1.
    - rewrite List.nth_firstn. case_if; [|lia].
      rewrite List.app_nth1; [reflexivity|].
      rewrite <-length_spec. lia.
    - rewrite <-!length_spec. lia.
    - rewrite List.length_firstn, List.length_app, <-!length_spec. lia. }
  destruct (to_Z i <? to_Z (length s1) + to_Z (length s2)) eqn:Hlen2.
  { rewrite List.app_nth1, List.app_nth2.
    - rewrite List.nth_firstn. case_if; [|lia].
      rewrite List.nth_firstn. case_if; [|lia].
      rewrite List.app_nth2, List.app_nth1; [reflexivity| |].
      all: rewrite <-!length_spec; lia.
    - rewrite <-length_spec. lia.
    - rewrite List.length_firstn, List.length_app, <-!length_spec. lia. }
  rewrite !List.app_nth2.
  - rewrite List.nth_firstn. case_if; [|lia].
    rewrite List.app_nth2; [|rewrite <-!length_spec; lia].
    f_equal. rewrite List.length_firstn, List.length_app, <-!length_spec. lia.
  - rewrite <-length_spec. lia.
  - rewrite List.length_firstn, List.length_app, <-!length_spec. lia.
Qed.

(** * Properties of sub *)

Lemma sub_full (s : string) : sub s 0 (length s) = s.
Proof.
  apply to_list_inj. rewrite sub_spec, List.skipn_O.
  rewrite length_spec, List.firstn_all. reflexivity.
Qed.

Lemma sub_len_0 (off : int) (s : string) :
  sub s off 0 = ""%pstring.
Proof.
  apply to_list_inj. rewrite sub_spec. reflexivity.
Qed.

Lemma split_cat_sub (s : string) (len : int) :
  s = cat (sub s 0 len) (sub s len (length s - len)%uint63).
Proof.
  apply to_list_inj. rewrite cat_spec, !sub_spec, List.skipn_O.
  pose proof valid_length s.
  rewrite List.firstn_all2.
  2: rewrite List.length_app, !List.length_firstn, !List.length_skipn, <-length_spec; lia.
  rewrite <-(List.firstn_skipn (to_nat len) (to_list s)) at 1. f_equal.
  rewrite List.firstn_all2; [reflexivity|].
  rewrite List.length_skipn, <-length_spec.
  destruct (to_Z len <=? to_Z (length s)) eqn:Hle; [|lia].
  rewrite Uint63.sub_spec, Z.mod_small; lia.
Qed.

Lemma sub_sub (s : string) (off1 len1 off2 len2 : int) :
  to_Z off1 + to_Z off2 = to_Z (off1 + off2)%uint63 ->
  to_Z len2 <= to_Z len1 - to_Z off2 ->
  sub (sub s off1 len1) off2 len2 = sub s (off1 + off2)%uint63 len2.
Proof.
  intros H1 H2. apply to_list_inj. rewrite !sub_spec.
  rewrite <-H1, Z2Nat.inj_add; [|lia|lia]. clear H1.
  rewrite !List.skipn_firstn_comm.
  rewrite List.firstn_firstn, List.skipn_skipn.
  f_equal; [lia|f_equal; lia].
Qed.

(** Properties of to_list and of_list *)

Lemma of_list_length (l : list char63) :
  Z.of_nat (List.length l) <= to_Z max_length ->
  length (of_list l) = of_Z (Z.of_nat (List.length l)).
Proof.
  induction l as [|c l IH]; [reflexivity|].
  assert (List.length (c :: l) = S (List.length l)) as -> by reflexivity.
  rewrite Nat2Z.inj_succ. intros Hlen; simpl.
  pose proof (IH ltac:(lia)) as IH.
  rewrite cat_length_spec_no_overflow.
  2: rewrite IH, make_length_spec, of_Z_spec, Z.mod_small; lia.
  rewrite make_length_spec; [|lia].
  rewrite IH. apply to_Z_inj.
  rewrite of_Z_spec, Z.mod_small; [|lia].
  rewrite Uint63.add_spec, Z.mod_small.
  2: rewrite of_Z_spec, Z.mod_small; lia.
  rewrite of_Z_spec, Z.mod_small; lia.
Qed.

Lemma of_list_app (l1 l2 : list char63) :
  of_list (l1 ++ l2) = cat (of_list l1) (of_list l2).
Proof.
  revert l2; induction l1 as [|c l1 IH]; intros l2; simpl.
  - rewrite cat_empty_l. reflexivity.
  - rewrite IH. rewrite cat_assoc. reflexivity.
Qed.

Lemma to_list_cat (s1 s2 : string) :
  (to_Z (length s1) + to_Z (length s2) <= to_Z max_length)%Z ->
  to_list (cat s1 s2) = app (to_list s1) (to_list s2).
Proof.
  rewrite cat_spec. intros Hlen.
  rewrite List.firstn_all2; [reflexivity|].
  rewrite List.length_app, <-!length_spec. lia.
Qed.

(** * Ordered type *)

Require OrderedType.

Module OT <: OrderedType.OrderedType with Definition t := string.
  Definition t := string.

  Definition eq s1 s2 := compare s1 s2 = Eq.
  Definition lt s1 s2 := compare s1 s2 = Lt.

  Lemma eq_refl (s : t) : eq s s.
  Proof. apply compare_refl. Qed.

  Lemma eq_sym (s1 s2 : t) : eq s1 s2 -> eq s2 s1.
  Proof. unfold eq. intros Heq.  rewrite compare_antisym, Heq. reflexivity. Qed.

  Lemma eq_trans (s1 s2 s3 : t) : eq s1 s2 -> eq s2 s3 -> eq s1 s3.
  Proof. unfold eq. apply compare_trans. Qed.

  Lemma lt_trans (s1 s2 s3 : t) : lt s1 s2 -> lt s2 s3 -> lt s1 s3.
  Proof. unfold lt. apply compare_trans. Qed.

  Lemma lt_not_eq (s1 s2 : t) : lt s1 s2 -> not (eq s1 s2).
  Proof. unfold lt, eq. intros ->. discriminate. Qed.

  #[program]
  Definition compare (s1 s2 : t) : OrderedType.Compare lt eq s1 s2 :=
    match compare s1 s2 with
    | Eq => OrderedType.EQ _
    | Lt => OrderedType.LT _
    | Gt => OrderedType.GT _
    end.
  Next Obligation. symmetry. assumption. Defined.
  Next Obligation. symmetry. assumption. Defined.
  Next Obligation. unfold lt. rewrite compare_antisym, <-Heq_anonymous. reflexivity. Defined.

  Hint Immediate eq_sym : core.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans : core.

  Definition eq_dec (s1 s2 : t) : {eq s1 s2} + {~ eq s1 s2}.
  Proof.
    unfold eq.
    destruct (PrimString.compare s1 s2).
    - left. reflexivity.
    - right. discriminate.
    - right. discriminate.
  Qed.
End OT.
