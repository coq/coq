Require Import Coq.ZArith.ZArith Coq.micromega.Lia. Local Open Scope Z_scope.
Require Import Coq.Numbers.Zmod.Base. Import Coercions.
Require Import Coq.Lists.List. Import ListNotations.

Import TODO_MOVE.

Section WithM.
  Context (m : positive).
  Local Fixpoint decode (bs : list (Zmod m)) : N :=
    match bs with
    | [] => 0
    | b :: bs => N.undivmod m (decode bs) b
    end.
  (* TODO: should we duplicate [decode]s and lemmas for [Z]? *)
  Local Fixpoint encode_N (n : nat) (v : N) : list (Zmod m) :=
    match n with
    | O => []
    | S n => of_N m v :: encode_N n (v / m)
    end.
  Local Fixpoint encode (n : nat) (v : Z) : list (Zmod m) :=
    match n with
    | O => []
    | S n => of_Z m v :: encode n (v / m)
    end.
End WithM.
Arguments decode {_}.

Lemma encode_N_decode {m} bs n (H : length bs = n) : encode_N m n (@decode m bs) = bs.
Proof.
  subst n; induction bs; cbn [encode_N decode length]; trivial.
  rewrite <-of_N_mod, N.mod_undivmod, N.div_undivmod;
  auto using to_N_range, f_equal2, of_N_to_N with nocore.
Qed.

Lemma encode_of_N {m} n v : encode m n (Z.of_N v) = encode_N m n v.
Proof.
  revert v; induction n; cbn [encode encode_N]; intro; rewrite <-?IHn;
  f_equal; trivial using of_Z_of_N; f_equal; lia.
Qed.

Lemma encode_decode {m} bs n (H : length bs = n) : encode m n (@decode m bs) = bs.
Proof. rewrite encode_of_N, encode_N_decode; trivial. Qed.

Lemma of_N_decode_encode m n v : decode (encode m n v) = v mod m^Z.of_nat n :> Z.
Proof.
  revert v; induction n; cbn [encode decode]; intros;
    rewrite ?N.pow_0_r, ?Z.mod_1_r, ?Nat2Z.inj_succ, ?Z.pow_succ_r; try lia.
  specialize (IHn (v/m)); cbv [N.undivmod].
  zify; rewrite IHn, Z.rem_mul_r, Z.add_comm, fold_to_Z, to_Z_of_Z; lia.
Qed.

Lemma decode_encode m n v : decode (encode m n v) = Z.to_N (v mod (m^Z.of_nat n)).
Proof. pose proof of_N_decode_encode m n v. lia. Qed.

Lemma decode_encode_N {m} n v : decode (encode_N m n v) = N.modulo v (m^N.of_nat n).
Proof. rewrite <-encode_of_N; zify. rewrite of_N_decode_encode, Z.rem_mod_nonneg; lia. Qed.

Lemma decode_range {m} n bs (H : length bs = n) : (@decode m bs < m^N.of_nat n)%N.
Proof.
  erewrite <-(encode_N_decode bs), decode_encode_N;
    eauto using N.mod_upper_bound with zarith.
Qed.

Lemma decode_range_le {m} n bs (H : Nat.le (length bs) n) : (@decode m bs < m^N.of_nat n)%N.
Proof.
  eapply N.lt_le_trans; try apply decode_range, eq_refl; apply N.pow_le_mono_r; lia.
Qed.

Lemma length_encode m n v : length (encode m n v) = n.
Proof. revert v; induction n; cbn [length encode]; congruence. Qed.

Lemma decode_nil m : @decode m [] = 0%N. Proof. trivial. Qed.
Lemma decode_cons m b bs : @decode m (b::bs) = N.undivmod m (decode bs) b.
Proof. trivial. Qed.
Lemma encode_0 m v : encode m 0 v = []. Proof. trivial. Qed.
Lemma encode_S m n v : encode m (S n) v = of_Z m v :: encode m n (v / m).
Proof. trivial. Qed.

Lemma decode_inj {m} xs ys
  (Hl : length ys = length xs) (H : @decode m xs = @decode m ys) : xs = ys.
Proof. erewrite <-(encode_decode _), <-(encode_decode ys _ Hl), H; eauto. Qed.

Lemma decode_inj_iff {m} xs ys :
  (length xs = length ys /\ @decode m xs = decode ys) <-> xs = ys.
Proof. intuition eauto using decode_inj, f_equal. Qed.

Lemma decode_app {m} xs ys n (H : length xs = n) :
  @decode m (xs ++ ys) = (decode xs + m^N.of_nat n * decode ys)%N.
Proof.
  subst n; induction xs; cbn [length app decode]; try lia; rewrite ?IHxs.
  rewrite ?Z.mod_1_r, ?Nnat.Nat2N.inj_succ, ?N.pow_succ_r; cbv [N.undivmod]; lia.
Qed.

Lemma decode_firstn {m} xs n :
  @decode m (firstn n xs) = (decode xs mod m^N.of_nat n)%N.
Proof.
  destruct (Nat.leb_spec (length xs) n).
  { pose proof decode_range_le n xs; rewrite firstn_all2, N.mod_small; try lia. }
  symmetry; rewrite <-(firstn_skipn n xs), (decode_app _ _ _ eq_refl) at 1.
  rewrite firstn_length, Nat.min_l, N.mul_comm, N.Div0.mod_add by lia.
  rewrite N.mod_small; trivial. apply decode_range_le. rewrite firstn_length; lia.
Qed.

Lemma decode_skipn {m} xs n :
  @decode m (skipn n xs) = (decode xs / m^N.of_nat n)%N.
Proof.
  destruct (Nat.leb_spec (length xs) n).
  { pose proof decode_range_le n xs; rewrite skipn_all2, decode_nil, N.div_small; lia. }
  symmetry; rewrite <-(firstn_skipn n xs), (decode_app _ _ _ eq_refl) at 1.
  rewrite firstn_length, Nat.min_l, N.mul_comm, N.div_add by lia.
  rewrite N.div_small; trivial. apply decode_range_le. rewrite firstn_length; lia.
Qed.

Lemma firstn_encode i m n v : firstn i (encode m n v) = encode m (Nat.min i n) v.
Proof.
  destruct (Nat.leb_spec n i); rewrite ?Nat.min_l, ?Nat.min_r by lia.
  { rewrite firstn_all2; trivial. rewrite length_encode; lia. }
  apply decode_inj, N2Z.inj. { rewrite firstn_length, 2 length_encode; lia. }
  rewrite decode_firstn, N2Z.inj_mod, 2of_N_decode_encode, N2Z.inj_pow, Z.mod_mod_pow; lia.
Qed.

Lemma skipn_encode i m n v : skipn i (encode m n v) = encode m (n-i) (v / m^Z.of_nat i).
Proof.
  destruct (Nat.leb_spec n i); rewrite ?Nat.min_l, ?Nat.min_r by lia.
  { rewrite skipn_all2, (proj2 (Nat.sub_0_le _ _)), encode_0; trivial.
    rewrite length_encode; lia. }
  apply decode_inj, N2Z.inj. { rewrite skipn_length, 2 length_encode; lia. }
  rewrite decode_skipn, N2Z.inj_div, 2of_N_decode_encode, N2Z.inj_pow.
  rewrite ?N2Z.inj_pos, ?nat_N_Z, ?Nat2Z.inj_sub, Z.div_mod_l_pow2_r; lia.
Qed.

Lemma nth_error_encode m n v i (H : lt i n) :
  nth_error (encode m n v) i = Some (of_Z m (v / m^Z.of_nat i)).
Proof.
  rewrite <-List.hd_error_skipn, skipn_encode.
  destruct (n-i)%nat eqn:?; [lia|]; rewrite encode_S; trivial.
Qed.

Module Z. (* TODO: move? *)

(** Bits *)

Definition to_bits n (v : Z) := map to_bool (encode _ n v).
Definition of_bits bs := decode (map (of_bool 2) bs).

Lemma to_bits_of_bits n bs (H : length bs = n) : to_bits n (of_bits bs) = bs.
Proof.
  cbv [to_bits of_bits].
  rewrite encode_decode, map_map by (rewrite map_length; trivial).
  erewrite map_ext by apply to_bool_of_bool; apply map_id.
Qed.

Lemma of_bits_to_bits n v : of_bits (to_bits n v) = Z.to_N (v mod 2^(Z.of_nat n)).
Proof.
  cbv [of_bits to_bits].
  erewrite map_map, map_ext, map_id, decode_encode; trivial using of_bool_to_bool.
Qed.

Lemma of_bits_range_le bs n :
  Nat.le (length bs) n -> (of_bits bs < 2^(N.of_nat n))%N.
Proof.
  pose proof decode_range_le n (map (of_bool 2) bs) as H.
  rewrite map_length in *. exact H.
Qed.

Lemma of_bits_range n bs (H : length bs = n) : (of_bits bs < 2^(N.of_nat n))%N.
Proof. apply decode_range; rewrite map_length; trivial. Qed.

Lemma of_bits_nil: of_bits [] = 0%N. Proof. trivial. Qed.

Lemma of_bits_cons b bs : of_bits (b :: bs) = N.undivmod (2) (of_bits bs) (N.b2n b).
Proof. etransitivity. eapply decode_cons. f_equal. apply to_N_of_bool_small, N.b2n_range. Qed.

Lemma of_bits_firstn xs n :
  of_bits (firstn n xs) = (of_bits xs mod 2^(N.of_nat n))%N.
Proof.
  pose proof decode_firstn (map (of_bool 2) xs) n.
  cbv [of_bits]; rewrite ?firstn_map, ?N.pow_mul_r in *; exact H.
Qed.

Lemma of_bits_skipn xs n :
  of_bits (skipn n xs) = (of_bits xs / 2^(N.of_nat n))%N.
Proof.
  pose proof decode_skipn (map (of_bool 2) xs) n.
  cbv [of_bits]; rewrite ?skipn_map, ?N.pow_mul_r in *; exact H.
Qed.

Lemma of_bits_inj xs ys
  (Hl : length ys = length xs) (H : of_bits xs = of_bits ys) : xs = ys.
Proof.
  apply decode_inj, List.map_inj in H; rewrite ?map_length; trivial.
  intros ? ? ?% of_bool_inj; trivial; lia.
Qed.

Lemma of_bits_inj_iff xs ys :
  length xs = length ys /\ of_bits xs = of_bits ys <-> xs = ys.
Proof. intuition eauto using of_bits_inj, f_equal. Qed.

Lemma of_bits_app xs ys n (H : length xs = n) :
  of_bits (xs ++ ys) = (of_bits xs + 2^(N.of_nat n) * of_bits ys)%N.
Proof.
  cbv [of_bits].
  erewrite map_app, decode_app, ?N.pow_mul_r; rewrite ?map_length; trivial.
Qed.

Lemma length_to_bits n v : length (to_bits n v) = n.
Proof. cbv [to_bits]. rewrite map_length, length_encode; trivial. Qed.

Lemma to_bits_0 v : to_bits 0 v = []. Proof. trivial. Qed.

Lemma to_bits_S n v : to_bits (S n) v = Z.odd v :: to_bits n (v / 2).
Proof. cbv [to_bits]. rewrite encode_S, map_cons, to_bool_of_Z; trivial. Qed.

Lemma firstn_to_bits i n v : firstn i (to_bits n v) = to_bits (Nat.min i n) v.
Proof. cbv [to_bits]. rewrite firstn_map, firstn_encode; trivial. Qed.

Lemma skipn_to_bits i n v : skipn i (to_bits n v) = to_bits (n - i) (v / 2 ^ (Z.of_nat i)).
Proof.
  cbv [to_bits]. rewrite skipn_map, skipn_encode, ?Z.pow_mul_r, ?Pos2Z.inj_pow;
    trivial; try lia.
Qed.

Lemma nth_error_to_bits' n v i (H : lt i n) :
  nth_error (to_bits n v) i = Some (Z.odd (v / 2 ^ (Z.of_nat i))).
Proof.
  cbv [to_bits]. rewrite nth_error_map, nth_error_encode by lia.
  cbv [option_map]. rewrite to_bool_of_Z; trivial.
Qed.

Lemma nth_error_to_bits n v i (H : lt i n) :
  nth_error (to_bits n v) i = Some (Z.testbit v (Z.of_nat i)).
Proof.
  rewrite nth_error_to_bits', Z.testbit_odd, Z.shiftr_div_pow2; trivial; lia.
Qed.

(** Bytes *)

Definition to_bytes n (v : Z) := map to_byte (encode _ n v).
Definition of_bytes bs := decode (map (of_byte 256) bs).

Lemma to_bytes_of_bytes n bs (H : length bs = n) : to_bytes n (of_bytes bs) = bs.
Proof.
  cbv [to_bytes of_bytes].
  rewrite encode_decode, map_map by (rewrite map_length; trivial).
  erewrite map_ext by apply to_byte_of_byte; apply map_id.
Qed.

Lemma of_bytes_to_bytes n v : of_bytes (to_bytes n v) = Z.to_N (v mod 2^(8*Z.of_nat n)).
Proof.
  cbv [of_bytes to_bytes].
  erewrite map_map, map_ext, map_id, decode_encode; trivial using of_byte_to_byte.
  rewrite Pos2Z.inj_pow, <-Z.pow_mul_r; lia.
Qed.

Lemma of_bytes_nil: of_bytes [] = 0%N. Proof. trivial. Qed.

Lemma of_bytes_cons b bs : of_bytes (b :: bs) = N.undivmod (2^8) (of_bytes bs) (Byte.to_N b).
Proof. etransitivity. eapply decode_cons. f_equal. apply to_N_of_byte. lia. Qed.

Lemma of_bytes_range_le bs n :
  Nat.le (length bs) n -> (of_bytes bs < 2^(8*N.of_nat n))%N.
Proof.
  pose proof decode_range_le n (map (of_byte 256) bs) as H.
  rewrite map_length, N.pow_mul_r in *; exact H.
Qed.

Lemma of_bytes_range n bs (H : length bs = n) : (of_bytes bs < 2^(8*N.of_nat n))%N.
Proof.
  pose proof decode_range n (map (of_byte (2^8)) bs) ltac:(rewrite map_length; trivial).
  cbv [of_bytes]; rewrite N.pos_pow, <-N.pow_mul_r in *; eassumption.
Qed.

Lemma of_bytes_firstn xs n :
  of_bytes (firstn n xs) = (of_bytes xs mod 2^(8*N.of_nat n))%N.
Proof.
  pose proof decode_firstn (map (of_byte 256) xs) n.
  cbv [of_bytes]; rewrite ?firstn_map, ?N.pow_mul_r in *; exact H.
Qed.

Lemma of_bytes_skipn xs n :
  of_bytes (skipn n xs) = (of_bytes xs / 2^(8*N.of_nat n))%N.
Proof.
  pose proof decode_skipn (map (of_byte 256) xs) n.
  cbv [of_bytes]; rewrite ?skipn_map, ?N.pow_mul_r in *; exact H.
Qed.

Lemma of_bytes_inj xs ys
  (Hl : length ys = length xs) (H : of_bytes xs = of_bytes ys) : xs = ys.
Proof.
  eapply decode_inj, List.map_inj in H; rewrite ?map_length; trivial.
  intros ? ? ?% of_byte_inj; trivial; lia.
Qed.

Lemma of_bytes_inj_iff xs ys :
  length xs = length ys /\ of_bytes xs = of_bytes ys <-> xs = ys.
Proof. intuition eauto using of_bytes_inj, f_equal. Qed.

Lemma of_bytes_app xs ys n (H : length xs = n) :
  of_bytes (xs ++ ys) = (of_bytes xs + 2^(8*N.of_nat n) * of_bytes ys)%N.
Proof.
  cbv [of_bytes].
  erewrite map_app, decode_app, ?N.pow_mul_r; rewrite ?map_length; trivial.
Qed.

Lemma length_to_bytes n v : length (to_bytes n v) = n.
Proof. cbv [to_bytes]. rewrite map_length, length_encode; trivial. Qed.

Lemma to_bytes_0 v : to_bytes 0 v = []. Proof. trivial. Qed.

Lemma to_bytes_S n v : to_bytes (S n) v = Byte.truncate_Z v :: to_bytes n (v / 2^8).
Proof. cbv [to_bytes]. rewrite encode_S, map_cons, to_byte_of_Z; trivial. Qed.

Lemma firstn_to_bytes i n v : firstn i (to_bytes n v) = to_bytes (Nat.min i n) v.
Proof. cbv [to_bytes]. rewrite firstn_map, firstn_encode; trivial. Qed.

Lemma skipn_to_bytes i n v : skipn i (to_bytes n v) = to_bytes (n - i) (v / 2^(8*Z.of_nat i)).
Proof.
  cbv [to_bytes]. rewrite skipn_map, skipn_encode, ?Z.pow_mul_r, ?Pos2Z.inj_pow;
    trivial; try lia.
Qed.

Lemma nth_error_to_bytes n v i (H : lt i n) :
  nth_error (to_bytes n v) i = Some (Byte.truncate_Z (v / 2^(8*Z.of_nat i))).
Proof.
  cbv [to_bytes]. rewrite nth_error_map, nth_error_encode by lia.
  cbv [option_map]; rewrite to_byte_of_Z, ?Z.pow_mul_r, ?Pos2Z.inj_pow; trivial; lia.
Qed.

End Z.
