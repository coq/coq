(* Inductive paths {A} (x : A) : A -> Type := idpath : paths x x where "x = y" := (@paths _ x y) : type_scope. *)
(* Goal forall A B : Set, @paths Type A B -> @paths Set A B. *)
(*   intros A B H. *)
(* Fail  exact H. *)
(* Section . *)

Unset Strict Universe Declaration.

Section lift_strict.
Polymorphic Definition liftlt := 
  let t := Type@{i} : Type@{k} in
  fun A : Type@{i} => A : Type@{k}.

Polymorphic Definition liftle := 
  fun A : Type@{i} => A : Type@{k}.
End lift_strict.


Set Universe Polymorphism.

(* Inductive option (A : Type) : Type := *)
(*   | None : option A *)
(*   | Some : A -> option A. *)

Inductive option (A : Type@{i}) : Type@{i} :=
  | None : option A
  | Some : A -> option A.

Definition foo' {A : Type@{i}} (o : option@{i} A) : option@{i} A :=
  o.

Definition foo'' {A : Type@{i}} (o : option@{j} A) : option@{k} A :=
  o.


Definition testm (A : Type@{i}) : Type@{max(i,j)} := A.

(* Inductive prod (A : Type@{i}) (B : Type@{j}) := *)
(*   | pair : A -> B -> prod A B. *)

(* Definition snd {A : Type@{i}} (B : Type@{j}) (p : prod A B) : B := *)
(*   match p with *)
(*     | pair _ _ a b => b *)
(*   end. *)

(* Definition snd' {A : Type@{i}} (B : Type@{i}) (p : prod A B) : B := *)
(*   match p with *)
(*     | pair _ _ a b => b *)
(*   end. *)

(* Inductive paths {A : Type} : A -> A -> Type := *)
(* | idpath (a : A) : paths a a. *)

Inductive paths {A : Type@{i}} : A -> A -> Type@{i} :=
| idpath (a : A) : paths a a.

Definition Funext := 
  forall (A : Type) (B : A -> Type),
  forall f g : (forall a, B a), (forall x : A, paths (f x) (g x)) -> paths f g.

Definition paths_lift_closed (A : Type@{i}) (x y : A) :
  paths x y -> @paths (liftle@{j Type} A) x y.
Proof. 
  intros. destruct X. exact (idpath _).
Defined.

Definition paths_lift (A : Type@{i}) (x y : A) :
  paths x y -> paths@{j} x y.
Proof. 
  intros. destruct X. exact (idpath _).
Defined.

Definition paths_lift_closed_strict (A : Type@{i}) (x y : A) :
  paths x y -> @paths (liftlt@{j Type} A) x y.
Proof. 
  intros. destruct X. exact (idpath _).
Defined.

Definition paths_downward_closed_le (A : Type@{i}) (x y : A) :
  paths@{j} (A:=liftle@{i j} A) x y -> paths@{i} x y.
Proof. 
  intros. destruct X. exact (idpath _).
Defined.

Definition paths_downward_closed_lt (A : Type@{i}) (x y : A) :
  @paths (liftlt@{j i} A) x y -> paths x y.
Proof. 
  intros. destruct X. exact (idpath _).
Defined.

Definition paths_downward_closed_lt_nolift (A : Type@{i}) (x y : A) :
  paths@{j} x y -> paths x y.
Proof. 
  intros. destruct X. exact (idpath _).
Defined.

Definition funext_downward_closed (F : Funext@{i' j' k'}) :
  Funext@{i j k}. 
Proof.
  intros A B f g H. red in F.
  pose (F A B f g (fun x => paths_lift _ _ _ (H x))).
  apply paths_downward_closed_lt_nolift. apply p.
Defined.

