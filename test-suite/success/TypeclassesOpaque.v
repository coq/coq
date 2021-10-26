
(** Testing the Typeclasses Opaque hints. We create two identical typeclasses [P] and [Q] and compare the behaviour of Typeclasses Opaque and Hint Opaque. They should be the same. *)

Axiom A : Type.
Axiom P : A -> Type.
Axiom Q : A -> Type.

Existing Class P.
Existing Class Q.

Axiom a : A.
Axiom pa : P a.
Axiom qa : Q a.
#[local] Existing Instance pa.
#[local] Existing Instance qa.

Definition b := a.
Definition c := a.

(** b is transparent so typeclass search should find it. *)

Goal P b.
Proof.
  Succeed typeclasses eauto.
Abort.

(** c is transparent so typeclass search should find it. *)

Goal Q c.
Proof.
  Succeed typeclasses eauto.
Abort.

(** Creating a local hint in a module or a section *)
Section Foo.
  #[local] Hint Opaque b : typeclass_instances.
  #[local] Typeclasses Opaque c.
End Foo.

(** Closing the module/section should get rid of the hint, so we expect the same behaviour as before. *)

(** b is transparent so typeclass search should find it. *)

Goal P b.
Proof.
  Succeed typeclasses eauto.
Abort.

(** c is transparent so typeclass search should find it. *)

Goal Q c.
Proof.
  Succeed typeclasses eauto.
Abort.

(** Now setting the locality as export *)
Module Foo.
  #[export] Hint Opaque b : typeclass_instances.
  #[export] Typeclasses Opaque c.
  (** Things should fail inside *)

  Goal P b.
  Proof.
    Fail typeclasses eauto.
  Abort.
  Goal Q c.
  Proof.
    Fail typeclasses eauto.
  Abort.
End Foo.

(** But succeed outside *)

Goal P b.
Proof.
  Succeed typeclasses eauto.
Abort.
Goal Q c.
Proof.
  Succeed typeclasses eauto.
Abort.

(** Until of course we export the module *)
Export Foo.

Goal P b.
Proof.
  Fail typeclasses eauto.
Abort.
Goal Q c.
Proof.
  Fail typeclasses eauto.
Abort.

(** Finally we test the localities for this alias *)

Succeed #[local] Typeclasses Opaque b.
Succeed #[global] Typeclasses Opaque b.
Succeed #[export] Typeclasses Opaque b.
Succeed #[local] Typeclasses Transparent b.
Succeed #[global] Typeclasses Transparent b.
Succeed #[export] Typeclasses Transparent b.

Notation bar := (0 + 0).
Fail Local Typeclasses Transparent bar.

Notation baz := b.
Succeed Local Typeclasses Transparent baz.
