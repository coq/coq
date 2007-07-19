Require Export Coq.subtac.SubtacTactics.

Set Implicit Arguments.

(** Wrap a proposition inside a subset. *)

Notation " {{ x }} " := (tt : { y : unit | x }).

(** A simpler notation for subsets defined on a cartesian product. *)

Notation "{ ( x , y )  :  A  |  P }" := 
  (sig (fun anonymous : A => let (x,y) := anonymous in P))
  (x ident, y ident) : type_scope.

(** Generates an obligation to prove False. *)

Notation " ! " := (False_rect _ _).

(** Abbreviation for first projection and hiding of proofs of subset objects. *)

Notation " ` t " := (proj1_sig t) (at level 10) : core_scope.
Notation "( x & ? )" := (@exist _ _ x _) : core_scope.

(** Coerces objects to their support before comparing them. *)

Notation " x '`=' y " := ((x :>) = (y :>)) (at level 70).

(** Quantifying over subsets. *)

Notation "'fun' { x : A | P } => Q" :=
  (fun x:{x:A|P} => Q)
  (at level 200, x ident, right associativity).

Notation "'forall' { x : A | P } , Q" :=
  (forall x:{x:A|P}, Q)
  (at level 200, x ident, right associativity).

Require Import Coq.Bool.Sumbool.

(** Construct a dependent disjunction from a boolean. *)

Notation "'dec'" := (sumbool_of_bool) (at level 0). 

(** The notations [in_right] and [in_left] construct objects of a dependent disjunction. *)

Notation in_right := (@right _ _ _).
Notation in_left := (@left _ _ _).

(** Default simplification tactic. *)

Ltac subtac_simpl := simpl ; intros ; destruct_conjs ; simpl in * ; try subst ; 
  try (solve [ red ; intros ; discriminate ]) ; auto with *.  

(** Extraction directives *)
Extraction Inline proj1_sig.
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
(* Extract Inductive prod "'a" "'b" => " 'a * 'b " [ "(,)" ]. *)
(* Extract Inductive sigT => "prod" [ "" ]. *)

Require Export ProofIrrelevance.
Require Export Coq.subtac.Heq.

Delimit Scope program_scope with program.
