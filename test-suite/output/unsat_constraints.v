Require Import Ltac2.Ltac2.

Import Constr.
Import Unsafe.

Polymorphic Axiom foo@{u v w | u < v, u <= w, v < w} : Prop.

Polymorphic Axiom bar@{u v w | } : Prop.

Universes u v w.

Constraint u < v.

Lemma baz : Prop.
Proof.
  (* easiest way to get unsatisfied constraints *)
  match kind 'bar@{u v w}, kind 'foo  with
  | Constant _ u, Constant c _ => Std.exact_no_check (make (Constant c u))
  | _ => Control.throw Assertion_failure
  end.
  (* should mention u <= w and v < w but not u < v *)
  Fail Defined.
Abort.
