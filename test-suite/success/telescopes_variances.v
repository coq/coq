(* Example by Janno Kaiser, trying to get telescopes in a small universe still enjoying cumulativity *)
Universes a b. Constraint a < b. (* only used for testing cumulativity. *)

Section Test.
#[local] Set Printing Universes.
#[local] Set Universe Polymorphism.
#[local] Set Polymorphic Inductive Cumulativity.
#[local] Unset Auto Template Polymorphism.
#[local] Unset Universe Minimization ToSet.

(* The following example illustrates an existing problem with the inductive
encoding of telescope arguments (i.e., the type is too big) and shows the
well-known workaround (using a fixpoint). It tries (and fails) to make use of
cumulativity in definitions to get the same cumulativity of telescope arguments
that the inductive formulation supports. *)

(* Inductive telescopes are necessarily one universe above all the types
   contained within. This makes sense. *)
Inductive tele@{+u|} : Type@{u+1} :=
| tO : tele
| tS {X:Type@{u}} (F : X -> tele) : tele.
About tele.
(* [tele_arg t] is again one universe above that of [t] despite the fact that
   the actual data contained within is a glorified product. *)
Inductive tele_arg@{u|} : tele@{u} -> Type@{u+1} :=
| taO : tele_arg tO@{u}
| taS {X:Type@{u}} {F} (x : X) (args : tele_arg (F x)) : tele_arg (tS@{u} F).
(* The annotation [+u] is not accepted because [u] is invariant in "term".
   However, Rocq correctly infers that [u] is covariant in "type" *)
Print tele_arg.
Succeed Check fun (t : tele@{a}) (arg : tele_arg@{a} t) => arg : tele_arg@{b} t.

(* There is a workaround for the size of [tele_arg] using a [Fixpoint] and an
   auxilliary record. ([sigT] might do but I'd like to keep this self-contained). *)
Record tele_arg_S@{u|} {A : Type@{u}} {P : A -> Type@{u}} := {
    tele_arg_head : A;
    tele_arg_tail : P tele_arg_head
  }.
Arguments tele_arg_S {_} P.
(* Again, the annotation [+u] is not accepted because [u] is invariant in "term".
   However, Rocq correctly infers that [u] is covariant in "type" *)
Print tele_arg_S.
Print tele_arg_head.
Succeed Check fun (A : Type@{a}) (P : A -> Type@{a}) (arg : tele_arg_S@{a} P) => arg : tele_arg_S@{b} P.
End Test.
#[universes(polymorphic, cumulative)] Symbol tele_arg_fix_rw@{u} : forall (t : tele@{u}), Type@{u}.
Rewrite Rule tele_arg_fix_rw_def :=
| tele_arg_fix_rw tO => unit
| @{u} |- tele_arg_fix_rw (@tS@{u} ?X ?f) => @tele_arg_S@{u} _ (fun x => tele_arg_fix_rw (?f x)).
Arguments tele_arg_S {_} P.
#[universes(polymorphic, cumulative)] Fixpoint tele_arg_fix@{u} (t : tele@{u}) : Type@{u} :=
  match t with
  | tO => unit
  | tS F => tele_arg_S (fun x => tele_arg_fix (F x))
  end.
(* [tele_arg_fix t] solves the universe problem. However, the universe [u] is
   inferred to be invariant in both "term" and "type" and thus the following [Check] fails. *)
(* Set Printing Universes. Set Printing All. Print tele_arg_fix. About tele_arg_fix. *)
Unset Strict Universe Declaration.

Check fun (t : tele@{a}) (arg : tele_arg_fix_rw@{c} t) => arg : tele_arg_fix_rw@{d} t.
Eval compute in (tele_arg_fix_rw (tS (fun X : nat => tO))).
(* Irrelevant here *)
