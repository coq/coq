

Open Scope type_scope.

Notation idmap := (fun x => x).
Notation compose := (fun g f x => g (f x)).
Notation " g 'o' f " := (compose g f) (at level 40, left associativity) : core_scope.
(* Notation " g 'o' f " := (fun x => g (f x)) (at level 40, left associativity) : core_scope. *)

(* sigma { & } *)
(* Notation "{ x & P }" := (sigT (fun x => P)) (only parsing) : type_scope. *)
(* Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) (only parsing) : type_scope. *)
Notation "( x ; y )" := (existT _ x y) : core_scope.
Notation "( x ; y ; z )" := (x ; (y ; z)) : core_scope.
Notation pr1 := (@projT1 _ _).
Notation pr2 := (@projT2 _ _).
Notation "x .1" := (@projT1 _ _ x) : core_scope.
Notation "x .2" := (@projT2 _ _ x) : core_scope.
Notation "'exists' x .. y , P"
  := (sigT (fun x => .. (sigT (fun y => P)) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "∃ x .. y , P"
  := (sigT (fun x => .. (sigT (fun y => P)) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.

Definition prod A B := sigT (fun _ : A => B).
Notation "A * B" := (prod A B) (at level 40, left associativity) : type_scope.
Notation "A × B" := (sigT (fun _ : A => B)) (at level 90, right associativity) : type_scope.
Notation "A × B" := (prod A B) (at level 90, right associativity) : type_scope.
Definition pair {A B} : A -> B -> A × B := fun x y => (x; y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Definition fst {A B} : A × B -> A := @projT1 _ _.
Definition snd {A B} : A × B -> B := @projT2 _ _.

(* Notation " ( a | b ) " := (exist _ a b). (* subtype { | } *) *)
(* Notation "x ..1" := (@proj1_sig _ _ x) (at level 3, format "x '..1'"). *)
(* Notation "x ..2" := (@proj2_sig _ _ x) (at level 3, format "x '..2'"). *)

(* Notation " ( a , b ) " := (conj a b). *)

Definition iff (A B : Type) := (A -> B) × (B -> A).
Notation "A <-> B" := (iff A B)%type : type_scope.

Definition transitive_iff {A B C}
  : A <-> B -> B <-> C -> A <-> C.
Proof.
  intros H1 H2. split; firstorder.
Defined.

(* ********* Strict Eq ********* *)
Delimit Scope eq_scope with eq.
Open Scope eq_scope.
Bind Scope eq_scope with eq.

Definition Einverse {A : Type} {x y : A} (p : x = y) : y = x.
  symmetry; assumption.
Defined.
Arguments Einverse {A x y} p : simpl nomatch.

Definition Econcat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with eq_refl, eq_refl => eq_refl end.
Arguments Econcat {A x y z} p q : simpl nomatch.

Notation "'E1'" := eq_refl : eq_scope.
Notation "p E@ q" := (Econcat p%eq q%eq) (at level 20) : eq_scope.
Notation "p ^E" := (Einverse p%eq) (at level 3, format "p '^E'") : eq_scope.

Definition Etransport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with eq_refl => u end.
Arguments Etransport {A}%_type_scope P {x y} p%_eq_scope u : simpl nomatch.

Notation "p E# x"
  := (Etransport _ p x) (right associativity, at level 65, only parsing) : eq_scope.

Notation coe := (Etransport idmap).

Notation "f == g" := (forall x, f x = g x) (at level 70, no associativity) : type_scope.

Definition Eap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with eq_refl => eq_refl end.
Global Arguments Eap {A B}%_type_scope f {x y} p%_eq_scope.


Definition Econcat_Vp {A} {x y : A} (p : x = y)
  : p^E E@ p = E1.
Proof.
  now destruct p.
Defined.


(* subtypes ?  *)

Axiom I : Type.
Axiom inf sup : I -> I -> I.
Axiom not : I -> I.
Axiom zero one : I.
Notation "0" := zero.
Notation "1" := one.

Axiom (zero_inf : forall {i}, inf 0 i = 0)
      (inf_zero : forall {i}, inf i 0 = 0)
      (one_inf : forall {i}, inf 1 i = i)
      (inf_one : forall {i}, inf i 1 = i)
      (not_not : forall {i}, not (not i) = i)
      (not_zero : not 0 = 1).

Axiom Face : Type.
Axiom El : Face -> Type.
Axiom is0 is1 : I -> Face.
Axiom bot top : Face.
Axiom and or : Face -> Face -> Face.
Axiom (El_bot : El bot = False)
      (El_top : El top = True)
      (El_and : forall {φ φ'}, El (and φ φ') = @sigT (El φ) (fun _ => El φ'))
      (El_or : forall {φ φ'}, El (or φ φ') = (El φ) + (El φ'))
      (El_is0 : forall {i}, El (is0 i) = (i = 0))
      (El_is1 : forall {i}, El (is1 i) = (i = 1))
      (is1_zero : is1 0 = bot)
      (is0_one : is0 1 = bot)
      (is0_zero : is0 0 = top)
      (is1_one : is1 1 = top)
      (and_bot : forall {φ}, and φ bot = bot)
      (and_top : forall {φ}, and φ top = φ)
.



Definition paths A (a b : A) := { p : I -> A & p 0 = a × p 1 = b }.

Notation " a ~ b " := (paths _ a b) (at level 30).

Tactic Notation "path" := simple refine (fun i => _; _; _).
Tactic Notation "path" ident(i) := simple refine (fun i => _; _; _).

Definition Contr A := { x : A & forall y, x ~ y }.

Definition partial A := { φ : Face & El φ -> A }.

Definition empty {A} : partial A.
Admitted.

Definition Etransport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p E@ q E# u = q E# p E# u.
Admitted.

Definition extends {A} (u : partial A) (a : A)
  := forall x, u.2 x = a.

Definition Contr' A
  := forall u : partial A, exists a, extends u a.

Definition Contr'_Contr A : Contr' A -> Contr A.
  intro H. pose (x := (H empty).1). exists x.
  intro y. path i.
  - refine (H (or (is0 i) (is1 i); _)).1.
    refine (_ o coe El_or). apply sum_rect; intros _. exact x. exact y.
  - cbn. match goal with
         | |- (H ?X).1 = _ => set X
         end.
    etransitivity. symmetry; unshelve eapply (H s).2.
    + unfold s; cbn. refine (coe El_or^E _). left.
      refine (coe _ Logic.I). exact (Eap El is0_zero E@ El_top)^E.
    + subst s; cbn. rewrite <- Etransport_pp.
      rewrite Econcat_Vp. reflexivity.
  - cbn. match goal with
         | |- (H ?X).1 = _ => set X
         end.
    etransitivity. symmetry; unshelve eapply (H s).2.
    + unfold s; cbn. refine (coe El_or^E _). right.
      refine (coe _ Logic.I). exact (Eap El is1_one E@ El_top)^E.
    + subst s; cbn. rewrite <- Etransport_pp.
      rewrite Econcat_Vp. reflexivity.
Defined. (* stack overflow *)
