(* Printing Reversible Up To Unification / Conversion Modulo Sorts And
   Universes / Conversion Modulo Universes / Conversion Modulo Universe
   Unification / Conversion: printing options get progressively turned
   on until the printed form re-parses and re-elaborates to an equal
   term. *)

(* Baseline: no check, hidden arguments are not re-inferable from the
   printed form alone. *)
Check @eq_refl nat 0.

(* Unification is enough to re-infer the hidden arguments from the
   original term, so nothing needs to be made explicit. *)
Set Printing Reversible Up To Unification.
Check @eq_refl nat 0.

(* Standalone re-elaboration of [eq_refl] leaves unresolved holes, so
   implicit arguments get printed. *)
Set Printing Reversible Up To Conversion.
Check @eq_refl nat 0.

(* The five flags behave like a radio button. *)
Test Printing Reversible Up To Unification.
Test Printing Reversible Up To Conversion Modulo Sorts And Universes.
Test Printing Reversible Up To Conversion Modulo Universe Unification.
Test Printing Reversible Up To Conversion.

(* Universe instances: re-elaboration introduces a fresh flexible
   universe. Unifying it with the original instance is fine up to
   conversion modulo universes, but not up to strict conversion, which
   requires the instance to be printed. *)
Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) := a.
Universe u.
Check pid@{u}.
Set Printing Reversible Up To Conversion Modulo Universes.
Check pid@{u}.
(* [Check Type] prints its type as [Type@{u+1}] (an algebraic universe);
   re-elaborating the plain [Type] yields a fresh level. Up to conversion
   modulo universes these are equal, so [Type] prints with no annotation
   and no warning (contrast with the strict conversion case below). *)
Check Type.

(* Conversion Modulo Universe Unification: universes introduced by the
   reparse may be unified against the original ones, but a level cannot
   be unified with an algebraic universe. So [pid@{u}] still prints
   plainly (fresh level unifies with [u])... *)
Set Printing Reversible Up To Conversion Modulo Universe Unification.
Check pid@{u}.
(* ...but [Check Type] does not check (fresh level vs algebraic [u+1]),
   so it warns and escalates, unlike modulo universes above. *)
Check Type.

Set Printing Reversible Up To Unification.
Check pid@{u}.

(* Sort qualities must elaborate the same under modulo universes, even
   though universe levels need not. [idT] is polymorphic over a sort
   quality [s]; used at [Prop], its printed form must keep the sort
   instance, because dropping it re-elaborates [idT] at a fresh quality
   (defaulting to [Type], quality [QType]) which differs from [Prop]. *)
Set Universe Polymorphism.
Definition idT@{s;u} (A : Type@{s;u}) (a : A) := a.
Set Printing Reversible Up To Conversion Modulo Universes.
Check idT@{Prop;Set}.
(* Modulo universe unification is laxer on sorts: the fresh sort quality
   is unified with [Prop], so the instance drops to plain [idT]. *)
Set Printing Reversible Up To Conversion Modulo Universe Unification.
Check idT@{Prop;Set}.
(* Modulo sorts and universes ignores sort qualities as well as
   universe levels, so the instance also drops, even though the
   re-elaboration of plain [idT] lives at quality Type rather than
   Prop... *)
Set Printing Reversible Up To Conversion Modulo Sorts And Universes.
Check idT@{Prop;Set}.
(* ...and [Check Type] prints plainly, as with modulo universes... *)
Check Type.
(* ...but re-elaboration is still standalone, so hidden arguments that
   cannot be re-inferred from the printed form alone get printed. *)
Check @eq_refl nat 0.
Unset Universe Polymorphism.

(* Unsetting the active flag turns the check off entirely (unsetting a
   flag other than the active one would be a no-op). *)
Unset Printing Reversible Up To Conversion Modulo Sorts And Universes.
Check @eq_refl nat 0.

(* A printing-only notation that does not print what it parses is
   detected and bypassed by turning notations off. *)
Set Printing Reversible Up To Unification.
Module LyingNotation.
  Notation "x ** y" := (Nat.mul x y) (at level 40).
  Set Warnings "-notation-overridden".
  Notation "x ** y" := (Nat.add x y) (at level 40, only printing).
  Check 2 * 3.
  Check 2 + 3.
End LyingNotation.

(* Goal display is checked too. *)
Set Printing Reversible Up To Conversion.
Goal @eq_refl nat 0 = eq_refl.
Show.
Abort.

(* Sort universes of [Check Type] cannot be re-parsed at all (their
   names are not declared), so a warning is emitted and the most
   explicit form is printed. *)
Check Type.
