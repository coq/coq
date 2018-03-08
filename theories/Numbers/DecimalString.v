(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Decimal Ascii String.

(** * Conversion between decimal numbers and Coq strings *)

(** Pretty straightforward, which is precisely the point of the
    [Decimal.int] datatype. The only catch is [Decimal.Nil] : we could
    choose to convert it as [""] or as ["0"]. In the first case, it is
    awkward to consider "" (or "-") as a number, while in the second case
    we don't have a perfect bijection. Since the second variant is implemented
    thanks to the first one, we provide both. *)

Local Open Scope string_scope.

(** Parsing one char *)

Definition uint_of_char (a:ascii)(d:option uint) :=
 match d with
 | None => None
 | Some d =>
   match a with
   | "0" => Some (D0 d)
   | "1" => Some (D1 d)
   | "2" => Some (D2 d)
   | "3" => Some (D3 d)
   | "4" => Some (D4 d)
   | "5" => Some (D5 d)
   | "6" => Some (D6 d)
   | "7" => Some (D7 d)
   | "8" => Some (D8 d)
   | "9" => Some (D9 d)
   | _ => None
   end
 end%char.

Lemma uint_of_char_spec c d d' :
  uint_of_char c (Some d) = Some d' ->
  (c = "0" /\ d' = D0 d \/
  c = "1" /\ d' = D1 d \/
  c = "2" /\ d' = D2 d \/
  c = "3" /\ d' = D3 d \/
  c = "4" /\ d' = D4 d \/
  c = "5" /\ d' = D5 d \/
  c = "6" /\ d' = D6 d \/
  c = "7" /\ d' = D7 d \/
  c = "8" /\ d' = D8 d \/
  c = "9" /\ d' = D9 d)%char.
Proof.
 destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]];
 intros [= <-]; intuition.
Qed.

(** Decimal/String conversion where [Nil] is [""] *)

Module NilEmpty.

Fixpoint string_of_uint (d:uint) :=
 match d with
 | Nil => EmptyString
 | D0 d => String "0" (string_of_uint d)
 | D1 d => String "1" (string_of_uint d)
 | D2 d => String "2" (string_of_uint d)
 | D3 d => String "3" (string_of_uint d)
 | D4 d => String "4" (string_of_uint d)
 | D5 d => String "5" (string_of_uint d)
 | D6 d => String "6" (string_of_uint d)
 | D7 d => String "7" (string_of_uint d)
 | D8 d => String "8" (string_of_uint d)
 | D9 d => String "9" (string_of_uint d)
 end.

Fixpoint uint_of_string s :=
 match s with
 | EmptyString => Some Nil
 | String a s => uint_of_char a (uint_of_string s)
 end.

Definition string_of_int (d:int) :=
 match d with
 | Pos d => string_of_uint d
 | Neg d => String "-" (string_of_uint d)
 end.

Definition int_of_string s :=
 match s with
 | EmptyString => Some (Pos Nil)
 | String a s' =>
   if Ascii.eqb a "-" then option_map Neg (uint_of_string s')
   else option_map Pos (uint_of_string s)
 end.

(* NB: For the moment whitespace between - and digits are not accepted.
   And in this variant [int_of_string "-" = Some (Neg Nil)].

Compute int_of_string "-123456890123456890123456890123456890".
Compute string_of_int (-123456890123456890123456890123456890).
*)

(** Corresponding proofs *)

Lemma usu d :
  uint_of_string (string_of_uint d) = Some d.
Proof.
 induction d; simpl; rewrite ?IHd; simpl; auto.
Qed.

Lemma sus s d :
  uint_of_string s = Some d -> string_of_uint d = s.
Proof.
 revert d.
 induction s; simpl.
 - now intros d [= <-].
 - intros d.
   destruct (uint_of_string s); [intros H | intros [=]].
   apply uint_of_char_spec in H.
   intuition subst; simpl; f_equal; auto.
Qed.

Lemma isi d : int_of_string (string_of_int d) = Some d.
Proof.
 destruct d; simpl.
 - unfold int_of_string.
   destruct (string_of_uint d) eqn:Hd.
   + now destruct d.
   + case Ascii.eqb_spec.
     * intros ->. now destruct d.
     * rewrite <- Hd, usu; auto.
 - rewrite usu; auto.
Qed.

Lemma sis s d :
 int_of_string s = Some d -> string_of_int d = s.
Proof.
 destruct s; [intros [= <-]| ]; simpl; trivial.
 case Ascii.eqb_spec.
 - intros ->. destruct (uint_of_string s) eqn:Hs; simpl; intros [= <-].
   simpl; f_equal. now apply sus.
 - destruct d; [ | now destruct uint_of_char].
   simpl string_of_int.
   intros. apply sus; simpl.
   destruct uint_of_char; simpl in *; congruence.
Qed.

End NilEmpty.

(** Decimal/String conversions where [Nil] is ["0"] *)

Module NilZero.

Definition string_of_uint (d:uint) :=
 match d with
 | Nil => "0"
 | _ => NilEmpty.string_of_uint d
 end.

Definition uint_of_string s :=
 match s with
 | EmptyString => None
 | _ => NilEmpty.uint_of_string s
 end.

Definition string_of_int (d:int) :=
 match d with
 | Pos d => string_of_uint d
 | Neg d => String "-" (string_of_uint d)
 end.

Definition int_of_string s :=
 match s with
 | EmptyString => None
 | String a s' =>
   if Ascii.eqb a "-" then option_map Neg (uint_of_string s')
   else option_map Pos (uint_of_string s)
 end.

(** Corresponding proofs *)

Lemma uint_of_string_nonnil s : uint_of_string s <> Some Nil.
Proof.
 destruct s; simpl.
 - easy.
 - destruct (NilEmpty.uint_of_string s); [intros H | intros [=]].
   apply uint_of_char_spec in H.
   now intuition subst.
Qed.

Lemma sus s d :
  uint_of_string s = Some d -> string_of_uint d = s.
Proof.
 destruct s; [intros [=] | intros H].
 apply NilEmpty.sus in H. now destruct d.
Qed.

Lemma usu d :
  d<>Nil -> uint_of_string (string_of_uint d) = Some d.
Proof.
 destruct d; (now destruct 1) || (intros _; apply NilEmpty.usu).
Qed.

Lemma usu_nil :
  uint_of_string (string_of_uint Nil) = Some Decimal.zero.
Proof.
 reflexivity.
Qed.

Lemma usu_gen d :
  uint_of_string (string_of_uint d) = Some d \/
  uint_of_string (string_of_uint d) = Some Decimal.zero.
Proof.
 destruct d; (now right) || (left; now apply usu).
Qed.

Lemma isi d :
  d<>Pos Nil -> d<>Neg Nil ->
  int_of_string (string_of_int d) = Some d.
Proof.
 destruct d; simpl.
 - intros H _.
   unfold int_of_string.
   destruct (string_of_uint d) eqn:Hd.
   + now destruct d.
   + case Ascii.eqb_spec.
     * intros ->. now destruct d.
     * rewrite <- Hd, usu; auto. now intros ->.
 - intros _ H.
   rewrite usu; auto. now intros ->.
Qed.

Lemma isi_posnil :
 int_of_string (string_of_int (Pos Nil)) = Some (Pos Decimal.zero).
Proof.
 reflexivity.
Qed.

(** Warning! (-0) won't parse (compatibility with the behavior of Z). *)

Lemma isi_negnil :
 int_of_string (string_of_int (Neg Nil)) = Some (Neg (D0 Nil)).
Proof.
 reflexivity.
Qed.

Lemma sis s d :
 int_of_string s = Some d -> string_of_int d = s.
Proof.
 destruct s; [intros [=]| ]; simpl.
 case Ascii.eqb_spec.
 - intros ->. destruct (uint_of_string s) eqn:Hs; simpl; intros [= <-].
   simpl; f_equal. now apply sus.
 - destruct d; [ | now destruct uint_of_char].
   simpl string_of_int.
   intros. apply sus; simpl.
   destruct uint_of_char; simpl in *; congruence.
Qed.

End NilZero.
