(* -*- coq-prog-args: ("-nois" "-R" "../theories" "Coq") -*- *)
(* File reduced by coq-bug-finder from original input, then from 2236 lines to 1877 lines, then from 1652 lines to 160 lines, then from 102 lines to 34 lines *)
(* coqc version trunk (December 2014) compiled on Dec 23 2014 22:6:43 with OCaml 4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (90ed6636dea41486ddf2cc0daead83f9f0788163) *)
Generalizable All Variables.
Require Import Coq.Init.Notations.
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Axiom admit : forall {T}, T.
Notation "g 'o' f" := (fun x => g (f x)) (at level 40, left associativity).
Notation "g 'o' f" := ltac:(let g' := g in let f' := f in exact (fun x => g' (f' x))) (at level 40, left associativity). (* Ensure that x is not captured in [g] or [f] in case they contain holes *)
Inductive eq {A} (x:A) : A -> Prop := eq_refl : x = x where "x = y" := (@eq _ x y) : type_scope.
Arguments eq_refl {_ _}.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y := match p with eq_refl => eq_refl end.
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A ; eisretr : forall x, f (equiv_inv x) = x }.
Arguments eisretr {A B} f {_} _.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'").
Global Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g} : IsEquiv (g o f) | 1000 := admit.
Definition isequiv_homotopic {A B} (f : A -> B) (g : A -> B) `{IsEquiv A B f} (h : forall x, f x = g x) : IsEquiv g := admit.
Global Instance isequiv_inverse {A B} (f : A -> B) {feq : IsEquiv f} : IsEquiv f^-1 | 10000 := admit.
Definition cancelR_isequiv {A B C} (f : A -> B) {g : B -> C} `{IsEquiv A B f} `{IsEquiv A C (g o f)} : IsEquiv g.
Proof.
  pose (fun H => @isequiv_homotopic _ _ ((g o f) o f^-1) _ H
                                    (fun b => ap g (eisretr f b))) as k.
  revert k.
  let x := match goal with |- let k := ?x in _ => constr:(x) end in
  intro k; clear k;
  pose (x _).
  pose (@isequiv_homotopic _ _ ((g o f) o f^-1) g _
                           (fun b => ap g (eisretr f b))).
  Undo. 
  apply (@isequiv_homotopic _ _ ((g o f) o f^-1) g _
                           (fun b => ap g (eisretr f b))).
Qed.
  
