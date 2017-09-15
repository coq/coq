Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 6343 lines to 2362 lines, then from 2115 lines to 303 lines, then from 321 lines to 90 lines, then from 95 lines to 41 lines *)
(* coqc version trunk (August 2014) compiled on Aug 31 2014 10:12:32 with OCaml 4.01.0
   coqtop version cagnode17:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (437b91a3ffd7327975a129b95b24d3f66ad7f3e4) *)
Set Primitive Projections.
Set Implicit Arguments.
Record prod (A B : Type) := pair { fst : A ; snd : B }.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Axiom transport : forall {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x), P y.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).
Lemma ap_transport {A} {P Q : A -> Type} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = (p # (f x z)).
Proof. admit.
Defined.
Lemma foo A B (f : A * B -> A) : f = f.
Admitted.
Goal forall (H0 H2 : Type) x p,
       @transport (prod H0 H2)
                  (fun GO : prod H0 H2 => x (fst GO)) = p.
  intros. 
  match goal with
    | [ |- context[x (?f _)] ] => set(foo':=f)
  end.
