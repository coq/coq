Unset Strict Universe Declaration.
(* File reduced by coq-bug-finder from original input, then from 8657 lines to
4731 lines, then from 4174 lines to 192 lines, then from 161 lines to 55 lines,
then from 51 lines to 37 lines, then from 43 lines to 30 lines *)
(* coqc version trunk (August 2014) compiled on Aug 31 2014 10:12:32 with OCaml
4.01.0
  coqtop version cagnode17:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk
(437b91a3ffd7327975a129b95b24d3f66ad7f3e4) *)
Require Import Coq.Init.Notations.
Set Universe Polymorphism.
Generalizable All Variables.
Record prod A B := pair { fst : A ; snd : B }.
Arguments pair {_ _} _ _.
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Open Scope type_scope.

Definition iff A B := prod (A -> B) (B -> A).
Infix "<->" := iff : type_scope.
Inductive paths {A : Type@{i}} (a : A) : A -> Type@{i} := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Class Contr_internal (A : Type) := { center : A ; contr : (forall y : A, center
= y) }.
Inductive trunc_index : Type := minus_two | trunc_S (_ : trunc_index).
Fixpoint IsTrunc_internal (n : trunc_index) (A : Type@{i}) : Type@{i} :=
 match n with
   | minus_two => Contr_internal A
   | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
 end.
Notation minus_one:=(trunc_S minus_two).
Class IsTrunc (n : trunc_index) (A : Type) : Type := Trunc_is_trunc :
IsTrunc_internal n A.
Instance istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A) :
IsTrunc n (x = y) := H x y.

Axiom cheat : forall {A}, A.

Lemma paths_lift (A : Type@{i}) (x y : A) (p : x = y) : paths@{j} x y.
Proof.
  destruct p. apply idpath.
Defined.

Lemma paths_change (A : Type@{i}) (x y : A) : paths@{j} x y = paths@{i} x y.
Proof. (* require Univalence *)
  apply cheat.
Defined.
  
Lemma IsTrunc_lift (n : trunc_index) :
  forall (A : Type@{i}), IsTrunc_internal@{i} n A -> IsTrunc_internal@{j} n A.
Proof.
  induction n; simpl; intros. 
  destruct X. exists center0. intros. apply (paths_lift _ _ _  (contr0 y)).

  rewrite paths_change. 
  apply IHn, X. 
Defined.

Notation IsHProp := (IsTrunc minus_one).
(* Record hProp := hp { hproptype :> Type ; isp : IsTrunc minus_one hproptype}. *)
(* Make the truncation proof polymorphic, i.e., available at any level greater or equal 
   to the carrier type level j *)
Record hProp := hp { hproptype :> Type@{j} ; isp : IsTrunc minus_one hproptype}.
Axiom path_iff_hprop_uncurried : forall `{IsHProp A, IsHProp B}, (A <-> B) -> A
= B.
Inductive V : Type@{U'} := | set {A : Type@{U}} (f : A -> V) : V.
Axiom is0trunc_V : IsTrunc (trunc_S (trunc_S minus_two)) V.
Existing Instance is0trunc_V.
Axiom bisimulation : V@{U' U} -> V@{U' U} -> hProp@{U'}.
Axiom bisimulation_refl : forall (v : V), bisimulation v v.
Axiom bisimulation_eq : forall (u v : V), bisimulation u v -> u = v.
Notation "u ~~ v" := (bisimulation u v) (at level 30).
Lemma bisimulation_equals_id : forall u v : V@{i j}, (u = v) = (u ~~ v).
Proof.
 intros u v.
 refine (@path_iff_hprop_uncurried _ _ _ _ _).
(* path_iff_hprop_uncurried : *)
(* forall A : Type@{Top.74}, *)
(* IsHProp A -> forall B : Type@{Top.74}, IsHProp B -> A <-> B -> A = B *)
(* (* Top.74 *)
(*    Top.78 |= Top.74 < Top.78 *)
(*                *) *)

 Show Universes. 
 exact (isp _).
 split; intros. destruct X. apply bisimulation_refl.
 apply bisimulation_eq, X.
Defined.
