Inductive eqT {A} (x : A) : A -> Type :=
  reflT : eqT x x.
Definition Bi_inv (A B : Type) (f : (A -> B)) :=
  sigT (fun (g : B -> A) =>
          sigT (fun (h : B -> A) =>
                  sigT (fun (α : forall b : B, eqT (f (g b)) b) =>
                          forall a : A, eqT (h (f a)) a))).
Definition TEquiv (A B : Type) := sigT (fun (f : A -> B) => Bi_inv _ _ f).

Axiom UA : forall (A B : Type), TEquiv (TEquiv A B) (eqT A B).
Definition idtoeqv {A B} (e : eqT A B) : TEquiv A B :=
  sigT_rect (fun _ => TEquiv A B)
            (fun (f : TEquiv A B -> eqT A B) H =>
               sigT_rect (fun _ => TEquiv A B)
                         (fun g _ => g e)
                         H)
            (UA A B).
