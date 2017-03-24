(* This used to fail in Coq version 8.1 beta due to a non variable
   universe (issued by template polymorphism) being sent by
   pretyping to the kernel (bug #1182) *)

Variable T : Type.
Variable x : nat*nat.

Check let (_, _) := x in sigT (fun _ : T => nat).

(* This used to raise an anomaly in V8.4, up to pl2 *)

Goal {x: nat & x=x}.
Fail exists (fun x =>
        match
          projT2 (projT2 x) as e in (_ = y)
          return _ = existT _ (projT1 x) (existT _ y e)
        with
        | eq_refl => eq_refl
        end).
Abort.

(* Some tests with ltac matching on building "if" and "let" *)

Goal forall b c d, (if negb b then c else d) = 0.
intros.
match goal with
|- (if ?b then ?c else ?d) = 0 => transitivity (if b then d else c)
end.
Abort.

Definition swap {A} {B} '((x,y):A*B) := (y,x).

Goal forall p, (let '(x,y) := swap p in x + y) = 0.
intros.
match goal with
|- (let '(x,y) := ?p in x + y) = 0 => transitivity (let (x,y) := p in x+y)
end.
Abort.
