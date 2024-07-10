From Stdlib Require Import Program.

Axiom I : Type.

Inductive S : Type := NT : I -> S.

Axiom F : S -> Type.

Axiom G : forall (s : S), F s -> Type.

Section S.

Variable init : I.
Variable my_s : F (NT init).

Inductive foo : forall (s: S) (hole_sem: F s), Type :=
| Foo : foo (NT init) my_s.

Goal forall
  (n : I) (s : F (NT n)) (ptz : foo (NT n) s) (pt : G (NT n) s) (x : unit),
match
  match x with tt => tt end
with
| tt =>
    match
      match ptz in foo x s return (forall _ : G x s, unit) with
      | Foo => fun _ : G (NT init) my_s => tt
      end pt
    with
    | tt => False
    end
end.
Proof.
dependent destruction ptz.
(* Check well-typedness of goal *)
match goal with [ |- ?P ] => let t := type of P in idtac end.
Abort.

End S.
