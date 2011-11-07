
(** Some tests of patterns containing matchs ending with joker branches.
    Cf. the new form of the [constr_pattern] constructor [PCase]
    in [pretyping/pattern.ml] *)

(* A universal match matcher *)

Ltac kill_match :=
 match goal with
   |- context [ match ?x with _ => _ end ] => destruct x
 end.

(* A match matcher restricted to a given type : nat *)

Ltac kill_match_nat :=
 match goal with
   |- context [ match ?x in nat with _ => _ end ] => destruct x
 end.

(* Another way to restrict to a given type : give a branch *)

Ltac kill_match_nat2 :=
 match goal with
   |- context [ match ?x with S _ => _ | _ => _ end ] => destruct x
 end.

(* This should act only on empty match *)

Ltac kill_match_empty :=
 match goal with
   |- context [ match ?x with end ] => destruct x
 end.

Lemma test1 (b:bool) : if b then True else O=O.
Proof.
 Fail kill_match_nat.
 Fail kill_match_nat2.
 Fail kill_match_empty.
 kill_match. exact I. exact eq_refl.
Qed.

Lemma test2a (n:nat) : match n with O => True | S n => (n = n) end.
Proof.
 Fail kill_match_empty.
 kill_match_nat. exact I. exact eq_refl.
Qed.

Lemma test2b (n:nat) : match n with O => True | S n => (n = n) end.
Proof.
 kill_match_nat2. exact I. exact eq_refl.
Qed.

Lemma test2c (n:nat) : match n with O => True | S n => (n = n) end.
Proof.
 kill_match. exact I. exact eq_refl.
Qed.

Lemma test3a (f:False) : match f return Prop with end.
Proof.
 kill_match_empty.
Qed.

Lemma test3b (f:False) : match f return Prop with end.
Proof.
 kill_match.
Qed.
