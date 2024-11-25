From Corelib Require Extraction.

(** Testing extraction of stdlib Empty_set *)

Recursive Extraction Empty_set.
Extraction TestCompile Empty_set.

(** Testing extraction of a type level not *)

Definition not : Type -> Type := fun X => X -> Empty_set.

Recursive Extraction not.
Extraction TestCompile not.

(** Testing extraction of a simple proof using not but no elimination. *)

Definition foo : forall X, not (not (not X)) -> not X.
Proof.
  intros X.
  intros p q.
  apply p.
  intros r.
  apply r.
  exact q.
Defined.

Recursive Extraction foo.
Extraction TestCompile foo.

(** Testing extraction of a user defined Empty *)

Inductive Empty : Set := .

Recursive Extraction Empty.
Extraction TestCompile Empty.

(** Testing extraction of Empty eliminator *)

Recursive Extraction Empty_rect.
Extraction TestCompile Empty_rect.

(** Testing extraction of an slightly different eliminator *)

Definition bar : Empty -> forall A, A := fun x => Empty_rect _ x.

Recursive Extraction bar.
Extraction TestCompile bar.
