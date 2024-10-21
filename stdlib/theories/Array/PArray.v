From Stdlib Require Import Uint63.
From Stdlib Require Export PrimArray ArrayAxioms.

Local Open Scope uint63_scope.
Local Open Scope array_scope.

Notation array := PrimArray.array (only parsing).
Notation make := PrimArray.make (only parsing).
Notation get := PrimArray.get (only parsing).
Notation default := PrimArray.default (only parsing).
Notation set := PrimArray.set (only parsing).
Notation length := PrimArray.length (only parsing).
Notation copy := PrimArray.copy (only parsing).

Notation max_length := PrimArray.max_length (only parsing).

Notation get_out_of_bounds := ArrayAxioms.get_out_of_bounds (only parsing).
Notation get_set_same := ArrayAxioms.get_set_same (only parsing).
Notation get_set_other := ArrayAxioms.get_set_other (only parsing).
Notation default_set := ArrayAxioms.default_set (only parsing).
Notation get_make := ArrayAxioms.get_make (only parsing).
Notation leb_length := ArrayAxioms.leb_length (only parsing).
Notation length_make := ArrayAxioms.length_make (only parsing).
Notation length_set := ArrayAxioms.length_set (only parsing).
Notation get_copy := ArrayAxioms.get_copy (only parsing).
Notation length_copy := ArrayAxioms.length_copy (only parsing).
Notation array_ext := ArrayAxioms.array_ext (only parsing).

(* Lemmas *)

Lemma default_copy A (t:array A) : default (copy t) = default t.
Proof.
  assert (irr_lt : length t <? length t = false). {
    destruct (Uint63.ltbP (length t) (length t)); try reflexivity.
    exfalso; eapply BinInt.Z.lt_irrefl; eassumption.
  }
  assert (get_copy := get_copy A t (length t)).
  rewrite !get_out_of_bounds in get_copy; try assumption.
  rewrite length_copy; assumption.
Qed.

Lemma default_make A (a : A) size : default (make size a) = a.
Proof.
  assert (irr_lt : length (make size a) <? length (make size a) = false). {
    destruct (Uint63.ltbP (length (make size a)) (length (make size a))); try reflexivity.
    exfalso; eapply BinInt.Z.lt_irrefl; eassumption.
  }
  assert (get_make := get_make A a size (length (make size a))).
  rewrite !get_out_of_bounds in get_make; assumption.
Qed.

Lemma get_set_same_default A (t : array A) (i : int) :
  t.[i <- default t].[i] = default t.
Proof.
 case_eq (i <? length t); intros.
 - rewrite get_set_same; trivial.
 - rewrite get_out_of_bounds, default_set; trivial.
   rewrite length_set; trivial.
Qed.

Lemma get_not_default_lt A (t:array A) x :
 t.[x] <> default t -> (x <? length t) = true.
Proof.
 intros Hd.
 case_eq (x <? length t); intros Heq; [trivial | ].
 elim Hd; rewrite get_out_of_bounds; trivial.
Qed.
