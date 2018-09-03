(* -*- mode: coq; coq-prog-args: ("-nois" "-indices-matter" "-R" "." "Top" "-top" "bug_oog_looping_rewrite_01") -*- *)
(* File reduced by coq-bug-finder from original input, then from 2553 lines to 1932 lines, then from 1946 lines to 1932 lines, then from 2467 lines to 1002 lines, then from 1016 lines to 1002 lines *)
(* coqc version 8.5 (January 2016) compiled on Jan 23 2016 16:15:22 with OCaml 4.01.0
   coqtop version 8.5 (January 2016) *)
Declare ML Module "ltac_plugin".
Inductive False := .
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
Require Coq.Init.Datatypes.

Import Coq.Init.Notations.

Global Set Universe Polymorphism.

Notation "A -> B" := (forall (_ : A), B) : type_scope.
Global Set Primitive Projections.

Inductive sum (A B : Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.
Notation nat := Coq.Init.Datatypes.nat.
Notation O := Coq.Init.Datatypes.O.
Notation S := Coq.Init.Datatypes.S.
Notation "x + y" := (sum x y) : type_scope.

Record prod (A B : Type) := pair { fst : A ; snd : B }.

Notation "x * y" := (prod x y) : type_scope.
Module Export Specif.

Set Implicit Arguments.

Record sig {A} (P : A -> Type) := exist { proj1_sig : A ; proj2_sig : P proj1_sig }.
Arguments proj1_sig {A P} _ / .

Notation sigT := sig (only parsing).
Notation existT := exist (only parsing).

Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.

Notation projT1 := proj1_sig (only parsing).
Notation projT2 := proj2_sig (only parsing).

End Specif.
Module Export HoTT_DOT_Basics_DOT_Overture.
Module Export HoTT.
Module Export Basics.
Module Export Overture.

Global Set Keyed Unification.

Global Unset Strict Universe Declaration.

Notation Type0 := Set.

Definition Type1@{i} := Eval hnf in let gt := (Set : Type@{i}) in Type@{i}.

Definition Type2@{i j} := Eval hnf in let gt := (Type1@{j} : Type@{i}) in Type@{i}.

Definition Type2le@{i j} := Eval hnf in let gt := (Set : Type@{i}) in
                                        let ge := ((fun x => x) : Type1@{j} -> Type@{i}) in Type@{i}.

Notation idmap := (fun x => x).
Delimit Scope function_scope with function.
Delimit Scope path_scope with path.
Delimit Scope fibration_scope with fibration.
Delimit Scope trunc_scope with trunc.

Open Scope trunc_scope.
Open Scope path_scope.
Open Scope fibration_scope.
Open Scope nat_scope.
Open Scope function_scope.

Notation "( x ; y )" := (existT _ x y) : fibration_scope.

Notation pr1 := projT1.
Notation pr2 := projT2.

Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.

Notation compose := (fun g f x => g (f x)).

Notation "g 'o' f" := (compose g%function f%function) (at level 40, left associativity) : function_scope.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

Notation "1" := idpath : path_scope.

Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.

Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B}%type_scope f%function_scope {_} _.

Record Equiv A B := BuildEquiv {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Notation "A <~> B" := (Equiv A B) (at level 85) : type_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : function_scope.

Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Arguments center A {_}.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Notation "n .+1" := (trunc_S n) (at level 2, left associativity, format "n .+1") : trunc_scope.
Notation "-2" := minus_two (at level 0) : trunc_scope.
Notation "-1" := (-2.+1) (at level 0) : trunc_scope.
Notation "0" := (-1.+1) : trunc_scope.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | -2 => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

Global Instance istrunc_paths (A : Type) n `{H : IsTrunc n.+1 A} (x y : A)
: IsTrunc n (x = y)
  := H x y.

Notation Contr := (IsTrunc -2).
Notation IsHProp := (IsTrunc -1).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.

Monomorphic Axiom dummy_funext_type : Type0.
Monomorphic Class Funext := { dummy_funext_value : dummy_funext_type }.

Inductive Unit : Type1 :=
    tt : Unit.

Class IsPointed (A : Type) := point : A.

Arguments point A {_}.

Record pType :=
  { pointed_type : Type ;
    ispointed_type : IsPointed pointed_type }.

Coercion pointed_type : pType >-> Sortclass.

Global Existing Instance ispointed_type.

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

Ltac revert_opaque x :=
  revert x;
  match goal with
    | [ |- forall _, _ ] => idtac
    | _ => fail 1 "Reverted constant is not an opaque variable"
  end.

End Overture.

End Basics.

End HoTT.

End HoTT_DOT_Basics_DOT_Overture.
Module Export HoTT_DOT_Basics_DOT_PathGroupoids.
Module Export HoTT.
Module Export Basics.
Module Export PathGroupoids.

Local Open Scope path_scope.

Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = p
  :=
  match p with idpath => 1 end.

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p
  :=
  match p with idpath => 1 end.

Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

Definition concat_pp_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r) :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

Definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p @ p^ = 1
  :=
  match p with idpath => 1 end.

Definition moveR_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  p = r @ q -> r^ @ p = q.
admit.
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> q = r^ @ p.
admit.
Defined.

Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
admit.
Defined.

Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q)
  :=
  match q with
    idpath =>
    match p with idpath => 1 end
  end.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^
  :=
  match p with idpath => 1 end.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g o f) p = ap g (ap f p)
  :=
  match p with idpath => 1 end.

Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y)
  :=
  match q as i in (_ = y) return (p x @ ap f i = i @ p y) with
    | idpath => concat_p1 _ @ (concat_1p _)^
  end.

End PathGroupoids.

End Basics.

End HoTT.

End HoTT_DOT_Basics_DOT_PathGroupoids.
Module Export HoTT_DOT_Basics_DOT_Equivalences.
Module Export HoTT.
Module Export Basics.
Module Export Equivalences.

Definition isequiv_commsq {A B C D}
           (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D)
           (p : k o f == g o h)
           `{IsEquiv _ _ f} `{IsEquiv _ _ h} `{IsEquiv _ _ k}
: IsEquiv g.
admit.
Defined.

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : Sect g f) (issect : Sect f g).

  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
  Proof.
    unfold issect'.
    apply moveR_M1.
    repeat rewrite ap_pp, concat_p_pp; rewrite <- ap_compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (ap f (issect a)^)).
    repeat rewrite concat_pp_p; rewrite ap_V; apply moveL_Vp; rewrite concat_p1.
    rewrite concat_p_pp, <- ap_compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
    rewrite concat_pV, concat_1p; reflexivity.
  Qed.

  Definition isequiv_adjointify : IsEquiv f
    := BuildIsEquiv A B f g isretr issect' is_adjoint'.

End Adjointify.

End Equivalences.

End Basics.

End HoTT.

End HoTT_DOT_Basics_DOT_Equivalences.
Module Export HoTT_DOT_Basics_DOT_Trunc.
Module Export HoTT.
Module Export Basics.
Module Export Trunc.
Generalizable Variables A B m n f.

Definition trunc_equiv A {B} (f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
admit.
Defined.

Record TruncType (n : trunc_index) := BuildTruncType {
  trunctype_type : Type ;
  istrunc_trunctype_type : IsTrunc n trunctype_type
}.

Arguments BuildTruncType _ _ {_}.

Coercion trunctype_type : TruncType >-> Sortclass.

Notation "n -Type" := (TruncType n) (at level 1) : type_scope.
Notation hProp := (-1)-Type.

Notation BuildhProp := (BuildTruncType -1).

End Trunc.

End Basics.

End HoTT.

End HoTT_DOT_Basics_DOT_Trunc.
Module Export HoTT_DOT_Types_DOT_Unit.
Module Export HoTT.
Module Export Types.
Module Export Unit.

Notation unit_name x := (fun (_ : Unit) => x).

End Unit.

End Types.

End HoTT.

End HoTT_DOT_Types_DOT_Unit.
Module Export HoTT_DOT_Types_DOT_Sigma.
Module Export HoTT.
Module Export Types.
Module Export Sigma.
Local Open Scope path_scope.

Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & p # u.2 = v.2})
: u = v
  := match pq.2 in (_ = v2) return u = (v.1; v2) with
       | 1 => match pq.1 as p in (_ = v1) return u = (v1; p # u.2) with
                | 1 => 1
              end
     end.

Definition path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v
  := path_sigma_uncurried P u v (p;q).

Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x = x') (q : p # y = y')
: (x;y) = (x';y')
  := path_sigma P (x;y) (x';y') p q.

Global Instance isequiv_pr1_contr {A} {P : A -> Type}
         `{forall a, Contr (P a)}
: IsEquiv (@pr1 A P) | 100.
Proof.
  refine (isequiv_adjointify (@pr1 A P)
                             (fun a => (a ; center (P a))) _ _).
  -
 intros a; reflexivity.
  -
 intros [a p].
    refine (path_sigma' P 1 (contr _)).
Defined.

Definition path_sigma_hprop {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)}
           (u v : sigT P)
: u.1 = v.1 -> u = v
  := path_sigma_uncurried P u v o pr1^-1.

End Sigma.

End Types.

End HoTT.

End HoTT_DOT_Types_DOT_Sigma.
Module Export HoTT_DOT_Extensions.
Module Export HoTT.
Module Export Extensions.

Section Extensions.

  Definition ExtensionAlong {A B : Type} (f : A -> B)
             (P : B -> Type) (d : forall x:A, P (f x))
    := { s : forall y:B, P y & forall x:A, s (f x) = d x }.

  Fixpoint ExtendableAlong@{i j k l}
           (n : nat) {A : Type@{i}} {B : Type@{j}}
           (f : A -> B) (C : B -> Type@{k}) : Type@{l}
    := match n with
         | O => Unit@{l}
         | S n => (forall (g : forall a, C (f a)),
                     ExtensionAlong@{i j k l l} f C g) *
                  forall (h k : forall b, C b),
                    ExtendableAlong n f (fun b => h b = k b)
       end.

  Definition ooExtendableAlong@{i j k l}
             {A : Type@{i}} {B : Type@{j}}
             (f : A -> B) (C : B -> Type@{k}) : Type@{l}
    := forall n, ExtendableAlong@{i j k l} n f C.

End Extensions.

End Extensions.

End HoTT.

End HoTT_DOT_Extensions.
Module Export HoTT.
Module Export Modalities.
Module Export ReflectiveSubuniverse.

Module Type ReflectiveSubuniverses.

  Parameter ReflectiveSubuniverse@{u a} : Type2@{u a}.

  Parameter O_reflector@{u a i} : forall (O : ReflectiveSubuniverse@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.

  Parameter In@{u a i} : forall (O : ReflectiveSubuniverse@{u a}),
                   Type2le@{i a} -> Type2le@{i a}.

  Parameter O_inO@{u a i} : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                               In@{u a i} O (O_reflector@{u a i} O T).

  Parameter to@{u a i} : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.

  Parameter inO_equiv_inO@{u a i j k} :
      forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),

        let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
        let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
        In@{u a j} O U.

  Parameter hprop_inO@{u a i}
  : Funext -> forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T).

  Parameter extendable_to_O@{u a i j k}
  : forall (O : ReflectiveSubuniverse@{u a}) {P : Type2le@{i a}} {Q : Type2le@{j a}} {Q_inO : In@{u a j} O Q},
      ooExtendableAlong@{i i j k} (to O P) (fun _ => Q).

End ReflectiveSubuniverses.

Module ReflectiveSubuniverses_Theory (Os : ReflectiveSubuniverses).
Export Os.

Module Export Coercions.

  Coercion O_reflector : ReflectiveSubuniverse >-> Funclass.

End Coercions.

End ReflectiveSubuniverses_Theory.

Module Type ReflectiveSubuniverses_Restriction_Data (Os : ReflectiveSubuniverses).

  Parameter New_ReflectiveSubuniverse@{u a} : Type2@{u a}.

  Parameter ReflectiveSubuniverses_restriction@{u a}
  : New_ReflectiveSubuniverse@{u a} -> Os.ReflectiveSubuniverse@{u a}.

End ReflectiveSubuniverses_Restriction_Data.

Module ReflectiveSubuniverses_Restriction
       (Os : ReflectiveSubuniverses)
       (Res : ReflectiveSubuniverses_Restriction_Data Os)
<: ReflectiveSubuniverses.

  Definition ReflectiveSubuniverse := Res.New_ReflectiveSubuniverse.

  Definition O_reflector@{u a i} (O : ReflectiveSubuniverse@{u a})
    := Os.O_reflector@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  Definition In@{u a i} (O : ReflectiveSubuniverse@{u a})
    := Os.In@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  Definition O_inO@{u a i} (O : ReflectiveSubuniverse@{u a})
    := Os.O_inO@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  Definition to@{u a i} (O : ReflectiveSubuniverse@{u a})
    := Os.to@{u a i} (Res.ReflectiveSubuniverses_restriction O).
  Definition inO_equiv_inO@{u a i j k} (O : ReflectiveSubuniverse@{u a})
    := Os.inO_equiv_inO@{u a i j k} (Res.ReflectiveSubuniverses_restriction O).
  Definition hprop_inO@{u a i} (H : Funext) (O : ReflectiveSubuniverse@{u a})
    := Os.hprop_inO@{u a i} H (Res.ReflectiveSubuniverses_restriction O).
  Definition extendable_to_O@{u a i j k} (O : ReflectiveSubuniverse@{u a})
    := @Os.extendable_to_O@{u a i j k} (Res.ReflectiveSubuniverses_restriction@{u a} O).

End ReflectiveSubuniverses_Restriction.

Module ReflectiveSubuniverses_FamUnion
       (Os1 Os2 : ReflectiveSubuniverses)
<: ReflectiveSubuniverses.

  Definition ReflectiveSubuniverse@{u a} : Type2@{u a}
    := Os1.ReflectiveSubuniverse@{u a} + Os2.ReflectiveSubuniverse@{u a}.

  Definition O_reflector@{u a i} : forall (O : ReflectiveSubuniverse@{u a}),
                             Type2le@{i a} -> Type2le@{i a}.
admit.
Defined.

  Definition In@{u a i} : forall (O : ReflectiveSubuniverse@{u a}),
                             Type2le@{i a} -> Type2le@{i a}.
  Proof.
    intros [O|O]; [ exact (Os1.In@{u a i} O)
                  | exact (Os2.In@{u a i} O) ].
  Defined.

  Definition O_inO@{u a i}
  : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
      In@{u a i} O (O_reflector@{u a i} O T).
admit.
Defined.

  Definition to@{u a i} : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.
admit.
Defined.

  Definition inO_equiv_inO@{u a i j k} :
      forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),
        In@{u a j} O U.
  Proof.
    intros [O|O]; [ exact (Os1.inO_equiv_inO@{u a i j k} O)
                  | exact (Os2.inO_equiv_inO@{u a i j k} O) ].
  Defined.

  Definition hprop_inO@{u a i}
  : Funext -> forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T).
admit.
Defined.

  Definition extendable_to_O@{u a i j k}
  : forall (O : ReflectiveSubuniverse@{u a}) {P : Type2le@{i a}} {Q : Type2le@{j a}} {Q_inO : In@{u a j} O Q},
      ooExtendableAlong@{i i j k} (to O P) (fun _ => Q).
admit.
Defined.

End ReflectiveSubuniverses_FamUnion.

End ReflectiveSubuniverse.

End Modalities.

End HoTT.

Module Type Modalities.

  Parameter Modality@{u a} : Type2@{u a}.

  Parameter O_reflector@{u a i} : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.

  Parameter In@{u a i} : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.

  Parameter O_inO@{u a i} : forall (O : Modality@{u a}) (T : Type@{i}),
                               In@{u a i} O (O_reflector@{u a i} O T).

  Parameter to@{u a i} : forall (O : Modality@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.

  Parameter inO_equiv_inO@{u a i j k} :
      forall (O : Modality@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),

        let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
        let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
        In@{u a j} O U.

  Parameter hprop_inO@{u a i}
  : Funext -> forall (O : Modality@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T).

End Modalities.

Module Modalities_to_ReflectiveSubuniverses
       (Os : Modalities) <: ReflectiveSubuniverses.

  Import Os.

  Fixpoint O_extendable@{u a i j k} (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector O A -> Type@{j})
           (B_inO : forall a, In@{u a j} O (B a)) (n : nat)
  : ExtendableAlong@{i i j k} n (to O A) B.
admit.
Defined.

  Definition ReflectiveSubuniverse := Modality.

  Definition O_reflector@{u a i} := O_reflector@{u a i}.

  Definition In@{u a i} : forall (O : ReflectiveSubuniverse@{u a}),
                   Type2le@{i a} -> Type2le@{i a}
    := In@{u a i}.
  Definition O_inO@{u a i} : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                               In@{u a i} O (O_reflector@{u a i} O T)
    := O_inO@{u a i}.
  Definition to@{u a i} := to@{u a i}.
  Definition inO_equiv_inO@{u a i j k} :
      forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),
        In@{u a j} O U
    := inO_equiv_inO@{u a i j k}.
  Definition hprop_inO@{u a i}
  : Funext -> forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T)
    := hprop_inO@{u a i}.

  Definition extendable_to_O@{u a i j k} (O : ReflectiveSubuniverse@{u a})
             {P : Type2le@{i a}} {Q : Type2le@{j a}} {Q_inO : In@{u a j} O Q}
  : ooExtendableAlong@{i i j k} (to O P) (fun _ => Q)
    := fun n => O_extendable O P (fun _ => Q) (fun _ => Q_inO) n.

End Modalities_to_ReflectiveSubuniverses.

Module Type EasyModalities.

  Parameter Modality@{u a} : Type2@{u a}.

  Parameter O_reflector@{u a i} : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.

  Parameter to@{u a i} : forall (O : Modality@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.

  Parameter minO_pathsO@{u a i}
  : forall (O : Modality@{u a}) (A : Type@{i})
           (z z' : O_reflector@{u a i} O A),
      IsEquiv (to@{u a i} O (z = z')).

End EasyModalities.

Module EasyModalities_to_Modalities (Os : EasyModalities)
<: Modalities.

  Import Os.

  Definition Modality := Modality.

  Definition O_reflector@{u a i} := O_reflector@{u a i}.
  Definition to@{u a i} := to@{u a i}.

  Definition In@{u a i}
  : forall (O : Modality@{u a}), Type@{i} -> Type@{i}
  := fun O A => IsEquiv@{i i} (to O A).

  Definition hprop_inO@{u a i} `{Funext} (O : Modality@{u a})
             (T : Type@{i})
  : IsHProp (In@{u a i} O T).
admit.
Defined.

  Definition O_ind_internal@{u a i j k} (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, In@{u a j} O (B oa))
  : let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
    let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
    (forall a, B (to O A a)) -> forall oa, B oa.
admit.
Defined.

  Definition O_ind_beta_internal@{u a i j k} (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, In@{u a j} O (B oa))
             (f : forall a : A, B (to O A a)) (a:A)
  : O_ind_internal@{u a i j k} O A B B_inO f (to O A a) = f a.
admit.
Defined.

  Definition O_inO@{u a i} (O : Modality@{u a}) (A : Type@{i})
  : In@{u a i} O (O_reflector@{u a i} O A).
admit.
Defined.

  Definition inO_equiv_inO@{u a i j k} (O : Modality@{u a}) (A : Type@{i}) (B : Type@{j})
    (A_inO : In@{u a i} O A) (f : A -> B) (feq : IsEquiv f)
  : In@{u a j} O B.
  Proof.
    simple refine (isequiv_commsq (to O A) (to O B) f
             (O_ind_internal O A (fun _ => O_reflector O B) _ (fun a => to O B (f a))) _).
    -
 intros; apply O_inO.
    -
 intros a; refine (O_ind_beta_internal@{u a i j k} O A (fun _ => O_reflector O B) _ _ a).
    -
 apply A_inO.
    -
 simple refine (isequiv_adjointify _
               (O_ind_internal O B (fun _ => O_reflector O A) _ (fun b => to O A (f^-1 b))) _ _);
        intros x.
      +
 apply O_inO.
      +
 pattern x; refine (O_ind_internal O B _ _ _ x); intros.
        *
 apply minO_pathsO.
        *
 simpl; admit.
      +
 pattern x; refine (O_ind_internal O A _ _ _ x); intros.
        *
 apply minO_pathsO.
        *
 simpl; admit.
  Defined.

End EasyModalities_to_Modalities.

Module Modalities_Theory (Os : Modalities).

Export Os.
Module Export Os_ReflectiveSubuniverses
  := Modalities_to_ReflectiveSubuniverses Os.
Module Export RSU
  := ReflectiveSubuniverses_Theory Os_ReflectiveSubuniverses.

Module Export Coercions.
  Coercion modality_to_reflective_subuniverse
    := idmap : Modality -> ReflectiveSubuniverse.
End Coercions.

Class IsConnected (O : Modality@{u a}) (A : Type@{i})

  := isconnected_contr_O : IsTrunc@{i} -2 (O A).

Class IsConnMap (O : Modality@{u a})
      {A : Type@{i}} {B : Type@{j}} (f : A -> B)
  := isconnected_hfiber_conn_map

     : forall b:B, IsConnected@{u a k} O (hfiber@{i j} f b).

End Modalities_Theory.

Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
  tr : A -> Trunc n A.
Arguments tr {n A} a.

Global Instance istrunc_truncation (n : trunc_index) (A : Type@{i})
: IsTrunc@{j} n (Trunc@{i} n A).
Admitted.

Definition Trunc_ind {n A}
  (P : Trunc n A -> Type) {Pt : forall aa, IsTrunc n (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa)
:= (fun f aa => match aa with tr a => fun _ => f a end Pt).

Definition Truncation_Modality := trunc_index.

Module Truncation_Modalities <: Modalities.

  Definition Modality : Type2@{u a} := Truncation_Modality.

  Definition O_reflector (n : Modality@{u u'}) A := Trunc n A.

  Definition In (n : Modality@{u u'}) A := IsTrunc n A.

  Definition O_inO (n : Modality@{u u'}) A : In n (O_reflector n A).
admit.
Defined.

  Definition to (n : Modality@{u u'}) A := @tr n A.

  Definition inO_equiv_inO (n : Modality@{u u'})
             (A : Type@{i}) (B : Type@{j}) Atr f feq
  : let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
    let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
    In n B
  := @trunc_equiv A B f n Atr feq.

  Definition hprop_inO `{Funext} (n : Modality@{u u'}) A
  : IsHProp (In n A).
admit.
Defined.

End Truncation_Modalities.

Module Import TrM := Modalities_Theory Truncation_Modalities.

Definition merely (A : Type@{i}) : hProp := BuildhProp (Trunc -1 A).

Notation IsSurjection := (IsConnMap -1).

Definition BuildIsSurjection {A B} (f : A -> B) :
  (forall b, merely (hfiber f b)) -> IsSurjection f.
admit.
Defined.

Ltac strip_truncations :=

  progress repeat match goal with
                    | [ T : _ |- _ ]
                      => revert_opaque T;
                        refine (@Trunc_ind _ _ _ _ _);

                        [];
                        intro T
                  end.
Local Open Scope trunc_scope.

Global Instance conn_pointed_type {n : trunc_index} {A : Type} (a0:A)
 `{IsConnMap n _ _ (unit_name a0)} : IsConnected n.+1 A | 1000.
admit.
Defined.

Definition loops (A : pType) : pType :=
  Build_pType (point A = point A) idpath.

Record pMap (A B : pType) :=
  { pointed_fun : A -> B ;
    point_eq : pointed_fun (point A) = point B }.

Arguments point_eq {A B} f : rename.
Coercion pointed_fun : pMap >-> Funclass.

Infix "->*" := pMap (at level 99) : pointed_scope.
Local Open Scope pointed_scope.

Definition pmap_compose {A B C : pType}
           (g : B ->* C) (f : A ->* B)
: A ->* C
  := Build_pMap A C (g o f)
                (ap g (point_eq f) @ point_eq g).

Record pHomotopy {A B : pType} (f g : pMap A B) :=
  { pointed_htpy : f == g ;
    point_htpy : pointed_htpy (point A) @ point_eq g = point_eq f }.
Arguments pointed_htpy {A B f g} p x.

Infix "==*" := pHomotopy (at level 70, no associativity) : pointed_scope.

Definition loops_functor {A B : pType} (f : A ->* B)
: (loops A) ->* (loops B).
Proof.
  refine (Build_pMap (loops A) (loops B)
            (fun p => (point_eq f)^ @ (ap f p @ point_eq f)) _).
  apply moveR_Vp; simpl.
  refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Definition loops_functor_compose {A B C : pType}
           (g : B ->* C) (f : A ->* B)
: (loops_functor (pmap_compose g f))
   ==* (pmap_compose (loops_functor g) (loops_functor f)).
admit.
Defined.

Local Open Scope path_scope.

Record ooGroup :=
  { classifying_space : pType@{i} ;
    isconn_classifying_space : IsConnected@{u a i} 0 classifying_space
  }.

Local Notation B := classifying_space.

Definition group_type (G : ooGroup) : Type
  := point (B G) = point (B G).

Coercion group_type : ooGroup >-> Sortclass.

Definition group_loops (X : pType)
: ooGroup.
Proof.

  pose (x0 := point X);
  pose (BG := (Build_pType
               { x:X & merely (x = point X) }
               (existT (fun x:X => merely (x = point X)) x0 (tr 1)))).

  cut (IsConnected 0 BG).
  {
 exact (Build_ooGroup BG).
}
  cut (IsSurjection (unit_name (point BG))).
  {
 intros; refine (conn_pointed_type (point _)).
}
  apply BuildIsSurjection; simpl; intros [x p].
  strip_truncations; apply tr; exists tt.
  apply path_sigma_hprop; simpl.
  exact (p^).
Defined.

Definition loops_group (X : pType)
: loops X <~> group_loops X.
admit.
Defined.

Definition ooGroupHom (G H : ooGroup)
  := pMap (B G) (B H).

Definition grouphom_fun {G H} (phi : ooGroupHom G H) : G -> H
  := loops_functor phi.

Coercion grouphom_fun : ooGroupHom >-> Funclass.

Definition group_loops_functor
           {X Y : pType} (f : pMap X Y)
: ooGroupHom (group_loops X) (group_loops Y).
Proof.
  simple refine (Build_pMap _ _ _ _); simpl.
  -
 intros [x p].
    exists (f x).
    strip_truncations; apply tr.
    exact (ap f p @ point_eq f).
  -
 apply path_sigma_hprop; simpl.
    apply point_eq.
Defined.

Definition loops_functor_group
           {X Y : pType} (f : pMap X Y)
: loops_functor (group_loops_functor f) o loops_group X
  == loops_group Y o loops_functor f.
admit.
Defined.

Definition grouphom_compose {G H K : ooGroup}
           (psi : ooGroupHom H K) (phi : ooGroupHom G H)
: ooGroupHom G K
  := pmap_compose psi phi.

Definition group_loops_functor_compose
           {X Y Z : pType}
           (psi : pMap Y Z) (phi : pMap X Y)
: grouphom_compose (group_loops_functor psi) (group_loops_functor phi)
  == group_loops_functor (pmap_compose psi phi).
Proof.
  intros g.
  unfold grouphom_fun, grouphom_compose.
  refine (pointed_htpy (loops_functor_compose _ _) g @ _).
  pose (p := eisretr (loops_group X) g).
  change (loops_functor (group_loops_functor psi)
            (loops_functor (group_loops_functor phi) g)
          = loops_functor (group_loops_functor
                                 (pmap_compose psi phi)) g).
  rewrite <- p.
  Fail Timeout 1 Time rewrite !loops_functor_group.
  (* 0.004 s in 8.5rc1, 8.677 s in 8.5 *)
  Timeout 1 do 3 rewrite loops_functor_group.
Abort.
