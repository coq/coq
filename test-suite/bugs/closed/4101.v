(* File reduced by coq-bug-finder from original input, then from 10940 lines to 152 lines, then from 509 lines to 163 lines, then from 178 lines to 66 lines *)
(* coqc version 8.5beta1 (March 2015) compiled on Mar 2 2015 18:53:10 with OCaml 4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-8.5,v8.5 (e77f178e60918f14eacd1ec0364a491d4cfd0f3f) *)

Global Set Primitive Projections.
Set Implicit Arguments.
Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
Axiom path_forall : forall {A : Type} {P : A -> Type} (f g : forall x : A, P x),
                      (forall x, f x = g x) -> f = g.
Lemma sigT_obj_eq
: forall (T : Type) (T0 : T -> Type)
         (s s0 : forall s : sigT T0,
                   sigT (fun _ : T0 (projT1 s) => unit) ->
                   sigT (fun _ : T0 (projT1 s) => unit)),
   s0 = s.
Proof.
  intros.
  Set Debug Tactic Unification.
  apply path_forall. 
