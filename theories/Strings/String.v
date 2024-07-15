(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Contributed by Laurent Théry (INRIA);
    Adapted to Coq V8 by the Coq Development Team *)

Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Stdlib.Strings.Byte.
Import IfNotations.

(** *** Definition of strings *)

(** Implementation of string as list of ascii characters *)

Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.

Declare Scope string_scope.
Delimit Scope string_scope with string.
Bind Scope string_scope with string.
Local Open Scope string_scope.

Register string as core.string.type.
Register EmptyString as core.string.empty.
Register String as core.string.string.

(** Equality is decidable *)

Definition string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
Proof.
 decide equality; apply ascii_dec.
Defined.

Local Open Scope lazy_bool_scope.

Fixpoint eqb s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => Ascii.eqb c1 c2 &&& eqb s1' s2'
 | _,_ => false
 end.

Infix "=?" := eqb : string_scope.

Lemma eqb_spec s1 s2 : Bool.reflect (s1 = s2) (s1 =? s2)%string.
Proof.
 revert s2. induction s1 as [|? s1 IHs1];
  intro s2; destruct s2; try (constructor; easy); simpl.
 case Ascii.eqb_spec; simpl; [intros -> | constructor; now intros [= ]].
 case IHs1; [intros ->; now constructor | constructor; now intros [= ]].
Qed.

Local Ltac t_eqb :=
  repeat first [ congruence
               | progress subst
               | apply conj
               | match goal with
                 | [ |- context[eqb ?x ?y] ] => destruct (eqb_spec x y)
                 end
               | intro ].
Lemma eqb_refl x : (x =? x)%string = true. Proof. t_eqb. Qed.
Lemma eqb_sym x y : (x =? y)%string = (y =? x)%string. Proof. t_eqb. Qed.
Lemma eqb_eq n m : (n =? m)%string = true <-> n = m. Proof. t_eqb. Qed.
Lemma eqb_neq x y : (x =? y)%string = false <-> x <> y. Proof. t_eqb. Qed.
Lemma eqb_compat: Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) eqb.
Proof. t_eqb. Qed.

(** *** Compare strings lexicographically *)

Fixpoint compare (s1 s2 : string) : comparison :=
  match s1, s2 with
  | EmptyString, EmptyString => Eq
  | EmptyString, String _ _  => Lt
  | String _ _ , EmptyString => Gt
  | String c1 s1', String c2 s2' =>
    match Ascii.compare c1 c2 with
    | Eq => compare s1' s2'
    | ne => ne
    end
  end.

Lemma compare_antisym : forall s1 s2 : string,
    compare s1 s2 = CompOpp (compare s2 s1).
Proof.
  induction s1, s2; intuition.
  simpl.
  rewrite Ascii.compare_antisym.
  destruct (Ascii.compare a0 a); simpl; intuition.
Qed.

Lemma compare_eq_iff : forall s1 s2 : string,
    compare s1 s2 = Eq -> s1 = s2.
Proof.
  induction s1, s2; intuition; inversion H.
  destruct (Ascii.compare a a0) eqn:Heq; try discriminate H1.
  apply Ascii.compare_eq_iff in Heq.
  apply IHs1 in H1.
  subst.
  reflexivity.
Qed.

Definition ltb (s1 s2 : string) : bool :=
  if compare s1 s2 is Lt then true else false.

Definition leb (s1 s2 : string) : bool :=
  if compare s1 s2 is Gt then false else true.

Lemma leb_antisym (s1 s2 : string) :
  leb s1 s2 = true -> leb s2 s1 = true -> s1 = s2.
Proof.
  unfold leb.
  rewrite compare_antisym.
  destruct (compare s2 s1) eqn:Hcmp; simpl in *; intuition.
  - apply compare_eq_iff in Hcmp. intuition.
  - discriminate H.
  - discriminate H0.
Qed.

Lemma leb_total (s1 s2 : string) : leb s1 s2 = true \/ leb s2 s1 = true.
Proof.
  unfold leb.
  rewrite compare_antisym.
  destruct (compare s2 s1); intuition.
Qed.

Infix "?="  := compare : string_scope.
Infix "<?"  := ltb     : string_scope.
Infix "<=?" := leb     : string_scope.

(** *** Concatenation of strings *)

Reserved Notation "x ++ y" (right associativity, at level 60).

Fixpoint append (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (s1' ++ s2)
  end
where "s1 ++ s2" := (append s1 s2) : string_scope.

(******************************)
(** Length                    *)
(******************************)

Fixpoint length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => S (length s')
  end.

(******************************)
(** Nth character of a string *)
(******************************)

Fixpoint get (n : nat) (s : string) {struct s} : option ascii :=
  match s with
  | EmptyString => None
  | String c s' => match n with
                   | O => Some c
                   | S n' => get n' s'
                   end
  end.

(** Two lists that are identical through get are syntactically equal *)

Theorem get_correct :
  forall s1 s2 : string, (forall n : nat, get n s1 = get n s2) <-> s1 = s2.
Proof.
intros s1; elim s1; simpl.
- intros s2; case s2; simpl; split; auto.
  + intros H; generalize (H O); intros H1; inversion H1.
  + intros; discriminate.
- intros a s1' Rec s2; case s2 as [|? s]; simpl; split; auto.
  + intros H; generalize (H O); intros H1; inversion H1.
  + intros; discriminate.
  + intros H; generalize (H O); simpl; intros H1; inversion H1.
    case (Rec s).
    intros H0; rewrite H0; auto.
    intros n; exact (H (S n)).
  + intros [= H1 H2].
    rewrite H2; trivial.
    rewrite H1; auto.
Qed.

(** The first elements of [s1 ++ s2] are the ones of [s1] *)

Theorem append_correct1 :
 forall (s1 s2 : string) (n : nat),
 n < length s1 -> get n s1 = get n (s1 ++ s2).
Proof.
intros s1; elim s1; simpl; auto.
- intros s2 n H; inversion H.
- intros a s1' Rec s2 n; case n; simpl; auto.
  intros n0 H; apply Rec; auto.
  apply Nat.succ_lt_mono; auto.
Qed.

(** The last elements of [s1 ++ s2] are the ones of [s2] *)

Theorem append_correct2 :
 forall (s1 s2 : string) (n : nat),
 get n s2 = get (n + length s1) (s1 ++ s2).
Proof.
intros s1; elim s1; simpl; auto.
- intros s2 n; rewrite Nat.add_comm; simpl; auto.
- intros a s1' Rec s2 n; case n; simpl; auto.
  intros.
  (replace (n0 + S (length s1'))
    with (S n0 + length s1') by now rewrite Nat.add_succ_r); auto.
Qed.

(** *** Substrings *)

(** [substring n m s] returns the substring of [s] that starts
    at position [n] and of length [m];
    if this does not make sense it returns [""] *)

Fixpoint substring (n m : nat) (s : string) : string :=
  match n, m, s with
  | O, O, _ => EmptyString
  | O, S m', EmptyString => s
  | O, S m', String c s' => String c (substring 0 m' s')
  | S n', _, EmptyString => s
  | S n', _, String c s' => substring n' m s'
  end.

(** The substring is included in the initial string *)

Theorem substring_correct1 :
 forall (s : string) (n m p : nat),
 p < m -> get p (substring n m s) = get (p + n) s.
Proof.
intros s; elim s; simpl; auto.
- intros n; case n; simpl; auto.
  intros m; case m; simpl; auto.
- intros a s' Rec; intros n; case n; simpl; auto.
  + intros m; case m; simpl; auto.
    * intros p H; inversion H.
    * intros m' p; case p; simpl; auto.
      intros n0 H; apply Rec; simpl; auto.
      apply <- Nat.succ_lt_mono; auto.
  + intros n' m p H; rewrite Nat.add_succ_r; auto.
Qed.

(** The substring has at most [m] elements *)

Theorem substring_correct2 :
 forall (s : string) (n m p : nat), m <= p -> get p (substring n m s) = None.
Proof.
intros s; elim s; simpl; auto.
- intros n; case n; simpl; auto.
  intros m; case m; simpl; auto.
- intros a s' Rec; intros n; case n; simpl; auto.
  intros m; case m; simpl; auto.
  intros m' p; case p; simpl; auto.
  + intros H; inversion H.
  + intros n0 H; apply Rec; simpl; auto.
    apply <- Nat.succ_le_mono; auto.
Qed.

(** *** Concatenating lists of strings *)

(** [concat sep sl] concatenates the list of strings [sl], inserting
    the separator string [sep] between each. *)

Fixpoint concat (sep : string) (ls : list string) :=
  match ls with
  | nil => EmptyString
  | cons x nil => x
  | cons x xs => x ++ sep ++ concat sep xs
  end.

(** *** Test functions *)

(** Test if [s1] is a prefix of [s2] *)

Fixpoint prefix (s1 s2 : string) {struct s2} : bool :=
  match s1 with
  | EmptyString => true
  | String a s1' =>
      match s2 with
      | EmptyString => false
      | String b s2' =>
          match ascii_dec a b with
          | left _ => prefix s1' s2'
          | right _ => false
          end
      end
  end.

(** If [s1] is a prefix of [s2], it is the [substring] of length
    [length s1] starting at position [O] of [s2] *)

Theorem prefix_correct :
 forall s1 s2 : string,
 prefix s1 s2 = true <-> substring 0 (length s1) s2 = s1.
Proof.
intros s1; elim s1; simpl; auto.
- intros s2; case s2; simpl; split; auto.
- intros a s1' Rec s2; case s2; simpl; auto.
  + split; intros; discriminate.
  + intros b s2'; case (ascii_dec a b); simpl; auto.
    * intros e; case (Rec s2'); intros H1 H2; split; intros H3; auto.
      -- rewrite e; rewrite H1; auto.
      -- apply H2; injection H3; auto.
    * intros n; split; intros H; try discriminate.
      case n; injection H; auto.
Qed.

(** Test if, starting at position [n], [s1] occurs in [s2]; if
    so it returns the position *)

Fixpoint index (n : nat) (s1 s2 : string) : option nat :=
  match s2, n with
  | EmptyString, O =>
      match s1 with
      | EmptyString => Some O
      | String a s1' => None
      end
  | EmptyString, S n' => None
  | String b s2', O =>
      if prefix s1 s2 then Some O
      else
        match index O s1 s2' with
        | Some n => Some (S n)
        | None => None
        end
   | String b s2', S n' =>
      match index n' s1 s2' with
      | Some n => Some (S n)
      | None => None
      end
  end.

(* Dirty trick to avoid locally that prefix reduces itself *)
Opaque prefix.

(** If the result of [index] is [Some m], [s1] in [s2] at position [m] *)

Theorem index_correct1 :
 forall (n m : nat) (s1 s2 : string),
 index n s1 s2 = Some m -> substring m (length s1) s2 = s1.
Proof.
intros n m s1 s2; generalize n m s1; clear n m s1; elim s2; simpl;
 auto.
- intros n; case n; simpl; auto.
  + intros m s1; case s1; simpl; auto.
    * intros [= <-]; auto.
    * intros; discriminate.
  + intros; discriminate.
- intros b s2' Rec n m s1.
  case n; simpl; auto.
  + generalize (prefix_correct s1 (String b s2'));
      case (prefix s1 (String b s2')).
    * intros H0 [= <-]; auto.
      case H0; simpl; auto.
    * case m; simpl; auto.
      -- case (index O s1 s2'); intros; discriminate.
      -- intros m'; generalize (Rec O m' s1); case (index O s1 s2'); auto.
         ++ intros x H H0 H1; apply H; injection H1; auto.
         ++ intros; discriminate.
  + intros n'; case m; simpl; auto.
    * case (index n' s1 s2'); intros; discriminate.
    * intros m'; generalize (Rec n' m' s1); case (index n' s1 s2'); auto.
      -- intros x H H1; apply H; injection H1; auto.
      -- intros; discriminate.
Qed.

(** If the result of [index] is [Some m],
    [s1] does not occur in [s2] before [m] *)

Theorem index_correct2 :
 forall (n m : nat) (s1 s2 : string),
 index n s1 s2 = Some m ->
 forall p : nat, n <= p -> p < m -> substring p (length s1) s2 <> s1.
Proof.
intros n m s1 s2; generalize n m s1; clear n m s1; elim s2; simpl;
 auto.
- intros n; case n; simpl; auto.
  + intros m s1; case s1; simpl; auto.
    * intros [= <-].
      intros p H0 H2; inversion H2.
    * intros; discriminate.
  + intros; discriminate.
- intros b s2' Rec n m s1.
  case n; simpl; auto.
  + generalize (prefix_correct s1 (String b s2'));
      case (prefix s1 (String b s2')).
    * intros H0 [= <-]; auto.
      intros p H2 H3; inversion H3.
    * case m; simpl; auto.
      -- case (index 0 s1 s2'); intros; discriminate.
      -- intros m'; generalize (Rec O m' s1); case (index 0 s1 s2'); auto.
         ++ intros x H H0 H1 p; try case p; simpl; auto.
            ** intros H2 H3; red; intros H4; case H0.
               intros H5 H6; absurd (false = true); auto with bool.
            ** { intros n0 H2 H3; apply H; auto.
               - injection H1; auto.
               - apply Nat.le_0_l.
               - apply <- Nat.succ_lt_mono; auto.
               }
         ++ intros; discriminate.
  + intros n'; case m; simpl; auto.
    * case (index n' s1 s2'); intros; discriminate.
    * intros m'; generalize (Rec n' m' s1); case (index n' s1 s2'); auto.
      -- intros x H H0 p; case p; simpl; auto.
         ++ intros H1; inversion H1; auto.
         ++ intros n0 H1 H2; apply H; auto.
            **  injection H0; auto.
            ** apply <- Nat.succ_le_mono; auto.
            ** apply <- Nat.succ_lt_mono; auto.
      -- intros; discriminate.
Qed.

(** If the result of [index] is [None], [s1] does not occur in [s2]
    after [n] *)

Theorem index_correct3 :
 forall (n m : nat) (s1 s2 : string),
 index n s1 s2 = None ->
 s1 <> EmptyString -> n <= m -> substring m (length s1) s2 <> s1.
Proof.
intros n m s1 s2; generalize n m s1; clear n m s1; elim s2; simpl;
 auto.
- intros n; case n; simpl; auto.
  + intros m s1; case s1; simpl; auto.
    case m; intros; red; intros; discriminate.
  + intros n' m; case m; auto.
    intros s1; case s1; simpl; auto.
- intros b s2' Rec n m s1.
  case n; simpl; auto.
  + generalize (prefix_correct s1 (String b s2'));
      case (prefix s1 (String b s2')).
    * intros; discriminate.
    * case m; simpl; auto with bool.
      -- case s1; simpl; auto.
         intros a s H H0 H1 H2; red; intros H3; case H.
         intros H4 H5; absurd (false = true); auto with bool.
      -- case s1; simpl; auto.
         intros a s n0 H H0 H1 H2;
           change (substring n0 (length (String a s)) s2' <> String a s);
           apply (Rec O); auto.
         ++ generalize H0; case (index 0 (String a s) s2'); simpl; auto; intros;
              discriminate.
         ++ apply Nat.le_0_l.
  + intros n'; case m; simpl; auto.
    * intros H H0 H1; inversion H1.
    * intros n0 H H0 H1; apply (Rec n'); auto.
      -- generalize H; case (index n' s1 s2'); simpl; auto; intros;
           discriminate.
      -- apply Nat.succ_le_mono; auto.
Qed.

(* Back to normal for prefix *)
Transparent prefix.

(** If we are searching for the [Empty] string and the answer is no
    this means that [n] is greater than the size of [s] *)

Theorem index_correct4 :
 forall (n : nat) (s : string),
 index n EmptyString s = None -> length s < n.
Proof.
intros n s; generalize n; clear n; elim s; simpl; auto.
- intros n; case n; simpl; auto.
  + intros; discriminate.
  + intros; apply Nat.lt_0_succ.
- intros a s' H n; case n; simpl; auto.
  + intros; discriminate.
  + intros n'; generalize (H n'); case (index n' EmptyString s'); simpl;
      auto.
    * intros; discriminate.
    * intros H0 H1. apply -> Nat.succ_lt_mono; auto.
Qed.

(** Same as [index] but with no optional type, we return [0] when it
    does not occur *)

Definition findex n s1 s2 :=
  match index n s1 s2 with
  | Some n => n
  | None => O
  end.

(** *** Conversion to/from [list ascii] and [list byte] *)

Fixpoint string_of_list_ascii (s : list ascii) : string
  := match s with
     | nil => EmptyString
     | cons ch s => String ch (string_of_list_ascii s)
     end.

Fixpoint list_ascii_of_string (s : string) : list ascii
  := match s with
     | EmptyString => nil
     | String ch s => cons ch (list_ascii_of_string s)
     end.

Lemma string_of_list_ascii_of_string s : string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  induction s as [|? ? IHs]; [ reflexivity | cbn; apply f_equal, IHs ].
Defined.

Lemma list_ascii_of_string_of_list_ascii s : list_ascii_of_string (string_of_list_ascii s) = s.
Proof.
  induction s as [|? ? IHs]; [ reflexivity | cbn; apply f_equal, IHs ].
Defined.

Definition string_of_list_byte (s : list byte) : string
  := string_of_list_ascii (List.map ascii_of_byte s).

Definition list_byte_of_string (s : string) : list byte
  := List.map byte_of_ascii (list_ascii_of_string s).

Lemma string_of_list_byte_of_string s : string_of_list_byte (list_byte_of_string s) = s.
Proof.
  cbv [string_of_list_byte list_byte_of_string].
  erewrite List.map_map, List.map_ext, List.map_id, string_of_list_ascii_of_string; [ reflexivity | intro ].
  apply ascii_of_byte_of_ascii.
Qed.

Lemma list_byte_of_string_of_list_byte s : list_byte_of_string (string_of_list_byte s) = s.
Proof.
  cbv [string_of_list_byte list_byte_of_string].
  erewrite list_ascii_of_string_of_list_ascii, List.map_map, List.map_ext, List.map_id; [ reflexivity | intro ].
  apply byte_of_ascii_of_byte.
Qed.

(** *** Concrete syntax *)

(**
  The concrete syntax for strings in scope string_scope follows the
  Coq convention for strings: all ascii characters of code less than
  128 are literals to the exception of the character `double quote'
  which must be doubled.

  Strings that involve ascii characters of code >= 128 which are not
  part of a valid utf8 sequence of characters are not representable
  using the Coq string notation (use explicitly the String constructor
  with the ascii codes of the characters).
 *)

Module Export StringSyntax.
  String Notation string string_of_list_byte list_byte_of_string : string_scope.
End StringSyntax.

Example HelloWorld := "	""Hello world!""
".
