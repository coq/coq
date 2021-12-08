Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 9593 lines to 104 lines, then from 187 lines to 103 lines, then from 113 lines to 90 lines *)
(* coqc version trunk (October 2014) compiled on Oct 1 2014 18:13:54 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (68846802a7be637ec805a5e374655a426b5723a5) *)
Axiom transport : forall {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x), P y.
Inductive trunc_index := minus_two | trunc_S (_ : trunc_index).
Axiom IsTrunc : trunc_index -> Type -> Type.
Existing Class IsTrunc.
Axiom Contr : Type -> Type.
Inductive Trunc (n : trunc_index) (A :Type) : Type := tr : A -> Trunc n A.
Module NonPrim.
  Unset Primitive Projections.
  Set Implicit Arguments.
  Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
  Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
  Unset Implicit Arguments.
  Notation "( x ; y )" := (existT _ x y) : fibration_scope.
  Open Scope fibration_scope.
  Notation pr1 := projT1.
  Notation pr2 := projT2.
  Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
  Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.
  Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.
  Class IsConnected (n : trunc_index) (A : Type) := isconnected_contr_trunc :> Contr (Trunc n A).
  Axiom isconnected_elim : forall {n} {A} `{IsConnected n A}
                                  (C : Type) `{IsTrunc n C} (f : A -> C),
                             { c:C & forall a:A, f a = c }.
  Class IsConnMap (n : trunc_index) {A B : Type} (f : A -> B)
    := isconnected_hfiber_conn_map :> forall b:B, IsConnected n (hfiber f b).
  Definition conn_map_elim {n : trunc_index}
             {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
             (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
             (d : forall a:A, P (f a))
  : forall b:B, P b.
  Proof.
    intros b.
    unshelve (refine (pr1 (isconnected_elim (A:=hfiber f b) _ _))).
    intro x.
    exact (transport P x.2 (d x.1)).
  Defined.

  Definition conn_map_elim' {n : trunc_index}
             {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
             (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
             (d : forall a:A, P (f a))
  : forall b:B, P b.
  Proof.
    intros b.
    unshelve (refine (pr1 (isconnected_elim (A:=hfiber f b) _ _))).
    intros [a p].
    exact (transport P p (d a)).
  Defined.

  Definition conn_map_comp {n : trunc_index}
             {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
             (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
             (d : forall a:A, P (f a))
  : forall a:A, conn_map_elim f P d (f a) = d a /\ conn_map_elim' f P d (f a) = d a.
  Proof.
    intros a.
    unfold conn_map_elim, conn_map_elim'.
    Set Printing Coercions.
    set (fibermap := fun a0p : hfiber f (f a)
                     => let (a0, p) := a0p in transport P p (d a0)).
    Set Printing Implicit.
    let G := match goal with |- ?G => constr:(G) end in
    first [ match goal with
              | [ |- (@isconnected_elim n (@hfiber A B f (f a))
                                        (@isconnected_hfiber_conn_map n A B f H (f a))
                                        (P (f a)) (HP (f a))
                                        (fun x : @hfiber A B f (f a) =>
                                           @transport B P (f x.1) (f a) x.2 (d x.1))).1 =
                     d a /\ _ ] => idtac
            end
          | fail 1 "projection names should be folded, [let] should generate unfolded projections, goal:" G ];
      first [ match goal with
                | [ |- _ /\ (@isconnected_elim n (@hfiber A B f (f a))
                                               (@isconnected_hfiber_conn_map n A B f H (f a))
                                               (P (f a)) (HP (f a)) fibermap).1 = d a ] => idtac
              end
            | fail 1 "destruct should generate unfolded projections, as should [let], goal:" G ].
    admit.
  Defined.
End NonPrim.

Module Prim.
  Set Primitive Projections.
  Set Implicit Arguments.
  Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
  Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
  Unset Implicit Arguments.
  Notation "( x ; y )" := (existT _ x y) : fibration_scope.
  Open Scope fibration_scope.
  Notation pr1 := projT1.
  Notation pr2 := projT2.
  Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
  Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.
  Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.
  Class IsConnected (n : trunc_index) (A : Type) := isconnected_contr_trunc :> Contr (Trunc n A).
  Axiom isconnected_elim : forall {n} {A} `{IsConnected n A}
                                  (C : Type) `{IsTrunc n C} (f : A -> C),
                             { c:C & forall a:A, f a = c }.
  Class IsConnMap (n : trunc_index) {A B : Type} (f : A -> B)
    := isconnected_hfiber_conn_map :> forall b:B, IsConnected n (hfiber f b).
  Definition conn_map_elim {n : trunc_index}
             {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
             (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
             (d : forall a:A, P (f a))
  : forall b:B, P b.
  Proof.
    intros b.
    unshelve (refine (pr1 (isconnected_elim (A:=hfiber f b) _ _))).
    intro x.
    exact (transport P x.2 (d x.1)).
  Defined.

  Definition conn_map_elim' {n : trunc_index}
             {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
             (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
             (d : forall a:A, P (f a))
  : forall b:B, P b.
  Proof.
    intros b.
    unshelve (refine (pr1 (isconnected_elim (A:=hfiber f b) _ _))).
    intros [a p].
    exact (transport P p (d a)).
  Defined.

  Definition conn_map_comp {n : trunc_index}
             {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
             (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
             (d : forall a:A, P (f a))
  : forall a:A, conn_map_elim f P d (f a) = d a /\ conn_map_elim' f P d (f a) = d a.
  Proof.
    intros a.
    unfold conn_map_elim, conn_map_elim'.
    Set Printing Coercions.
    set (fibermap := fun a0p : hfiber f (f a)
                     => let (a0, p) := a0p in transport P p (d a0)).
    Set Printing Implicit.
    let G := match goal with |- ?G => constr:(G) end in
    first [ match goal with
              | [ |- (@isconnected_elim n (@hfiber A B f (f a))
                                        (@isconnected_hfiber_conn_map n A B f H (f a))
                                        (P (f a)) (HP (f a))
                                        (fun x : @hfiber A B f (f a) =>
                                           @transport B P (f x.1) (f a) x.2 (d x.1))).1 =
                     d a /\ _ ] => idtac
            end
          | fail 1 "projection names should be folded, [let] should generate unfolded projections, goal:" G ];
      first [ match goal with
                | [ |- _ /\ (@isconnected_elim n (@hfiber A B f (f a))
                                               (@isconnected_hfiber_conn_map n A B f H (f a))
                                               (P (f a)) (HP (f a)) fibermap).1 = d a ] => idtac
              end
            | fail 1 "destruct should generate unfolded projections, as should [let], goal:" G ].
    admit.
  Defined.
End Prim.
