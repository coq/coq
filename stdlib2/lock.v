(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ssreflect prelude prop datatypes equality.

(**  Ssreflect converse rewrite rule rule idiom.  **)
Definition ssr_converse R (r : R) := (True_intro, r).
Notation "=^~ r" := (ssr_converse r) (at level 100) : form_scope.

(* Term tagging (user-level).                                                 *)
(* The ssreflect library uses four strengths of term tagging to restrict      *)
(* convertibility during type checking:                                       *)
(*  nosimpl t simplifies to t EXCEPT in a definition; more precisely, given   *)
(*    Definition foo := nosimpl bar, foo (or foo t') will NOT be expanded by  *)
(*    the /= and //= switches unless it is in a forcing context (e.g., in     *)
(*    match foo t' with ... end, foo t' will be reduced if this allows the    *)
(*    match to be reduced). Note that nosimpl bar is simply notation for a    *)
(*    a term that beta-iota reduces to bar; hence rewrite /foo will replace   *)
(*    foo by bar, and rewrite -/foo will replace bar by foo.                  *)
(*    CAVEAT: nosimpl should not be used inside a Section, because the end of *)
(*    section "cooking" removes the iota redex.                               *)
(*  locked t is provably equal to t, but is not convertible to t; 'locked'    *)
(*    provides support for selective rewriting, via the lock t : t = locked t *)
(*    Lemma, and the ssreflect unlock tactic.                                 *)
(*  locked_with k t is equal but not convertible to t, much like locked t,    *)
(*    but supports explicit tagging with a value k : unit. This is used to    *)
(*    mitigate a flaw in the term comparison heuristic of the Coq kernel,     *)
(*    which treats all terms of the form locked t as equal and conpares their *)
(*    arguments recursively, leading to an exponential blowup of comparison.  *)
(*    For this reason locked_with should be used rather than locked when      *)
(*    defining ADT operations. The unlock tactic does not support locked_with *)
(*    but the unlock rewrite rule does, via the unlockable interface.         *)
(*  we also use Module Type ascription to create truly opaque constants,      *)
(*    because simple expansion of constants to reveal an unreducible term     *)
(*    doubles the time complexity of a negative comparison. Such opaque       *)
(*    constants can be expanded generically with the unlock rewrite rule.     *)
(*    See the definition of card and subset in fintype for examples of this.  *)

Notation nosimpl t := (let: tt := tt in t).

Lemma master_key : unit. Proof. exact tt. Qed.
Definition locked A := let: tt := master_key in fun x : A => x.

Register master_key as plugins.ssreflect.master_key.
Register locked as plugins.ssreflect.locked.

Lemma lock A x : x = locked x :> A. Proof. unlock; reflexivity. Qed.

(* To unlock opaque constants. *)
Structure unlockable T v := Unlockable { unlocked : T; unlocked_prop : unlocked = v }.
Lemma unlock T x C : @unlocked T x C = x. Proof. by case: C. Qed.

Notation "[ 'unlockable' 'of' C ]" := (@Unlockable _ _ C (unlock _))
  (at level 0, format "[ 'unlockable'  'of'  C ]") : form_scope.

Notation "[ 'unlockable' 'fun' C ]" := (@Unlockable _ (fun _ => _) C (unlock _))
  (at level 0, format "[ 'unlockable'  'fun'  C ]") : form_scope.

(* Generic keyed constant locking. *)

(* The argument order ensures that k is always compared before T. *)
Definition locked_with k := let: tt := k in fun T x => x : T.

(* This can be used as a cheap alternative to cloning the unlockable instance *)
(* below, but with caution as unkeyed matching can be expensive.              *)
Lemma locked_withE T k x : unkeyed (locked_with k x) = x :> T.
Proof. by case: k. Qed.

(* Intensionaly, this instance will not apply to locked u. *)
Canonical locked_with_unlockable T k x :=
  @Unlockable T x (locked_with k x) (locked_withE k x).

(* More accurate variant of unlock, and safer alternative to locked_withE. *)
Lemma unlock_with T k x : unlocked (locked_with_unlockable k x) = x :> T.
Proof. exact: unlock. Qed.
