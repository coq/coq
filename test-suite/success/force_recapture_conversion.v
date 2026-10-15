From Corelib Require Import Force.
From Ltac2 Require Import Ltac2.
Set Universe Polymorphism.
Set Default Proof Mode "Classic".

Definition force_type@{u u1} (X : Blocked@{Type;u1} Type@{u}) : Type@{u} :=
  __run Type@{u} Type@{u} X (fun T => T).
Definition sensitive_type := 1 + 1 = 2.
Definition guarded (X : Blocked Type) : Blocked Prop :=
  __block Prop (forall x : force_type (__block Type (__unblock X)), True).
Lemma guarded_run (X : Blocked Type) :
  __run Prop Prop
    (__block Prop (__unblock (guarded X) -> __unblock (guarded X)))
    (fun P => P).
Proof. intro H. exact H. Qed.

(* Quoting an inert projection must not disable the structural identity
   computation needed to expand an explicit block-local re-capture. *)
Goal forall x : sensitive_type, True.
Proof.
  refine (guarded_run (__block Type sensitive_type) _).
  ltac2:(
    match Constr.Unsafe.kind (Control.goal ()) with
    | Constr.Unsafe.Prod binder _ =>
        match Constr.Unsafe.kind (Constr.Binder.type binder) with
        | Constr.Unsafe.App _ args =>
            match Constr.Unsafe.kind (Array.get args 0) with
            | Constr.Unsafe.PBlock _ _ entries body =>
                Control.assert_true (Int.equal (Array.length entries) 0);
                Control.assert_true (Constr.equal body constr:(sensitive_type))
            | _ => Control.throw_invalid_argument "Expected a blocked domain"
            end
        | _ => Control.throw_invalid_argument "Expected force_type"
        end
    | _ => Control.throw_invalid_argument "Expected a dependent product"
    end).
  intros; exact I.
Qed.
