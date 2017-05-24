(* -*- mode: coq; coq-prog-args: ("-R" "." "Top" "-top" "bug_bad_induction_01") -*- *)
(* File reduced by coq-bug-finder from original input, then from 1889 lines to 144 lines, then from 158 lines to 144 lines *)
(* coqc version 8.5pl1 (April 2016) compiled on Apr 18 2016 14:48:5 with OCaml 4.02.3
   coqtop version 8.5pl1 (April 2016) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition relation (A : Type) := A -> A -> Type.
Class Transitive {A} (R : relation A) := transitivity : forall x y z, R x y -> R y z -> R x z.
Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  refine (@transitivity _ R _ x y z _ _).
Tactic Notation "etransitivity" := etransitivity _.
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.
Notation pr1 := projT1.
Notation pr2 := projT2.
Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Notation "x .2" := (projT2 x) (at level 3) : fibration_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Arguments idpath {A a} , [A] a.
Arguments paths_rect [A] a P f y p.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Delimit Scope path_scope with path.
Local Open Scope path_scope.
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.
Instance transitive_paths {A} : Transitive (@paths A) | 0 := @concat A.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.
Notation "1" := idpath : path_scope.
Notation "p @ q" := (concat p q) (at level 20) : path_scope.
Notation "p ^" := (inverse p) (at level 3) : path_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.
Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  := match p with idpath => idpath end.
Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : x = y) (z : P (f x))
  : transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
admit.
Defined.
Local Open Scope path_scope.
Generalizable Variables X A B C f g n.
Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
  (pq : {p : u.1 = v.1 &  p # u.2 = v.2})
  : u = v
  := match pq with
       | existT p q =>
         match u, v return (forall p0 : (u.1 = v.1), (p0 # u.2 = v.2) -> (u=v)) with
           | (x;y), (x';y') => fun p1 q1 =>
             match p1 in (_ = x'') return (forall y'', (p1 # y = y'') -> (x;y)=(x'';y'')) with
               | idpath => fun y' q2 =>
                 match q2 in (_ = y'') return (x;y) = (x;y'') with
                   | idpath => 1
                 end
             end y' q1
         end p q
     end.
Definition path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
  (p : u.1 = v.1) (q : p # u.2 = v.2)
  : u = v
  := path_sigma_uncurried P u v (p;q).
Definition projT1_path `{P : A -> Type} {u v : sigT P} (p : u = v)
  : u.1 = v.1
  :=
  ap (@projT1 _ _) p.
Notation "p ..1" := (projT1_path p) (at level 3) : fibration_scope.
Definition projT2_path `{P : A -> Type} {u v : sigT P} (p : u = v)
  : p..1 # u.2 = v.2
  := (transport_compose P (@projT1 _ _) p u.2)^
     @ (@apD {x:A & P x} _ (@projT2 _ _) _ _ p).
Notation "p ..2" := (projT2_path p) (at level 3) : fibration_scope.
Definition eta_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
  (p : u = v)
  : path_sigma_uncurried _ _ _ (p..1; p..2) = p.
admit.
Defined.
Definition eta_path_sigma `{P : A -> Type} {u v : sigT P} (p : u = v)
  : path_sigma _ _ _ (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Definition path_path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
  (p q : u = v)
  (rs : {r : p..1 = q..1 & transport (fun x => transport P x u.2 = v.2) r p..2 = q..2})
  : p = q.
Proof.
  destruct rs, p, u.
  etransitivity; [ | apply eta_path_sigma ].
  simpl in *.
  induction p0.
  admit.
Defined.

