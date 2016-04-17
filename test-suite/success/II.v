Unset Elimination Schemes.
(*
Inductive nat : Set :=
| zero : nat
| succ : forall x : nat, x <> zero -> nat
with iseven : nat -> Prop :=
| iseven_zero : iseven zero
| iseven_succ_isodd x
  : isodd x -> iseven (succ x)
with isodd : nat -> Prop :=
| isodd_succ_iseven x
  : iseven x -> isodd (succ x)
. *)

(* Scheme foo := Induction for nat Sort Prop
  with foo' := Induction for iseven Sort Prop
  with foo'' := Induction for isodd Sort Prop.
 *)

Definition foo :=
  fix foo (A : Type) (a : A) (n : nat) : Type :=
  match n with
  | 0   => False
  | S k => ({x : foo A a k & bar A a k x = a})%type
  end
with bar (A : Type) (x : A) (n : nat) : foo A x n -> A :=
  match n return foo A x n -> A with
  | 0   => fun _ => x
  | S k => fun t => bar A x k (projT1 t)
  end for foo.

Definition bar :=
  fix foo (A : Type) (a : A) (n : nat) : Type :=
  match n with
  | 0   => False
  | S k => ({x : foo A a k & bar A a k x = a})%type
  end
with bar (A : Type) (x : A) (n : nat) : foo A x n -> A :=
  match n return foo A x n -> A with
  | 0   => fun _ => x
  | S k => fun t => bar A x k (projT1 t)
  end for bar.

Check foo.
Check (bar : forall (A : Type) (x : A) (n : nat), foo A x n -> A).

Module TyElim.
Unset Elimination Schemes.
Inductive Con : Set :=
| empty : Con
| ext (Γ : Con) : Ty Γ -> Con

with Ty : Con -> Set :=
| Uunit Γ : Ty Γ
| Upi Γ A (B : Ty (ext Γ A)) : Ty Γ.
Print Ty.
(** Unification issue, difference between named and rel_context,
    putting these variables in the rel_context results in unification
    failure *)
Module WithNamed.
Section elim.
    Variables
      (ConM : Con -> Set)
      (TyM : forall Γ, ConM Γ -> Ty Γ -> Set)
      (f : ConM empty)
      (f1 : forall (x : Con) (x0 : ConM x) (x1 : Ty x) (x2 : TyM x x0 x1), ConM (ext x x1))
      (f2 : forall x (x0 : ConM x), TyM x x0 (Uunit x))
      (f3 : forall Γ A B pΓ pa, TyM _ (f1 _ pΓ _ pa) B -> TyM Γ pΓ (Upi _ A B)).

  Definition con_elim :=
      fix F (c : Con) : ConM c :=
        match c return (ConM c) with
        | empty => f
        | ext g t => f1 g (F g) t (F0 g t)
        end
        with F0 (a : Con) (t : Ty a) {struct t} : TyM a (F a) t :=
          match t as t0 in Ty g return TyM g (F g) t0 with
          | Uunit g => f2 _ (F g)
          | Upi g a b => f3 g a b (F g) (F0 g a) (F0 (ext g a) b)
          end
            for F.

    Definition ty_elim : forall Γ (t : Ty Γ), TyM Γ (con_elim Γ) t :=
      fix F (c : Con) : ConM c :=
        match c return (ConM c) with
        | empty => f
        | ext g t => f1 g (F g) t (F0 g t)
        end
        with F0 (a : Con) (t : Ty a) {struct t} : TyM a (F a) t :=
          match t in Ty g return TyM g (F g) t with
          | Uunit g => f2 _ (F g)
          | Upi g a b => f3 g a b (F g) (F0 g a) (F0 (ext g a) b)
          end
        for F0.
  End elim.
End WithNamed.

Module WithRel.
Section elim.
    Variables
      (ConM : Con -> Set)
      (TyM : forall Γ, ConM Γ -> Ty Γ -> Set).

    Definition con_elim
           (f : ConM empty)
               (f1 : forall (x : Con) (x0 : ConM x) (x1 : Ty x) (x2 : TyM x x0 x1), ConM (ext x x1))
               (f2 : forall x (x0 : ConM x), TyM x x0 (Uunit x))
               (f3 : forall Γ A B pΓ pa, TyM _ (f1 _ pΓ _ pa) B -> TyM Γ pΓ (Upi _ A B))
  :=
      fix F (c : Con) : ConM c :=
        match c return (ConM c) with
        | empty => f
        | ext g t =>
          (* Interresting unification issue here, there should be
           a single solution *)
          f1 g (F g) t (F0 g t)
          (* let x := F g in f1 g x t (F0 g t : TyM g x t) *)
        end
        with F0 (a : Con) (t : Ty a) {struct t} : TyM a (F a) t :=
          match t in Ty g return TyM g (F g) t with
          | Uunit g => f2 _ (F g)
          | Upi g a b => f3 g a b (F g) (F0 g a)
                           (F0 (ext g a) b : TyM (ext g a) (F (ext g a)) b)
          end
            for F.

  End elim.
End WithRel.

(* Wrong schemes, not dependent enough *)
Scheme con_elim := Induction for Con Sort Type
with ty_elim := Induction for Ty Sort Type.

Print con_elim.
Print WithNamed.con_elim.
End TyElim.

(*
Module FirstCircle.
  Inductive circle : Set :=
  | base : circle
  with eq : circle -> circle -> Set :=
  | loop : eq base base.

Definition circle_elim_1 :=
  fun (P : circle -> Set) (P0 : forall a b : circle, P a -> P b -> eq a b -> Set)
    (f : P base)
    (floop : P0 base base f f loop) =>
    fix F (a : circle) : P a :=
    match a as a0 return (P a0) with
    | base => f
    end
    with F0 (a b : circle) (e : eq a b) {struct b} : P0 a b (F a) (F b) e :=
      match e as e0 in (eq a' b') return P0 a' b' (F a') (F b') e0 with
      | loop => floop
      end
        for F.

Definition circle_elim :  forall (P : circle -> Set)
         (P0 : forall a b : circle, P a -> P b -> eq a b -> Set)
         (f : P base) (floop : P0 base base f f loop)
         (a b : circle) (e : eq a b),
    P0 a b (circle_elim_1 P P0 f floop a) (circle_elim_1 P P0 f floop b) e
  :=
  fun (P : circle -> Set) (P0 : forall a b : circle, P a -> P b -> eq a b -> Set)
    (f : P base)
    (floop : P0 base base f f loop) =>
    fix F (a : circle) : P a :=
    match a as a0 return (P a0) with
    | base => f
    end
    with F0 (a b : circle) (e : eq a b) {struct b} : P0 a b _ _ e :=
      match e as e0 in (eq a' b') return P0 a' b' (F a') (F b') e0 with
      | loop => floop
      end
        for F0.

Definition circle_elim_nat (* : forall a, eq a base := *) :=
  circle_elim (fun x => eq x base)
              (fun a b az bz e => eq a b)
              loop loop.

Definition circle_elim_nat' : forall a b, eq a b -> eq a b :=
  circle_elim (fun x => eq x base)
              (fun a b az bz e => eq a b)
              loop loop.
End FirstCircle.

Module FullCircle.
  Inductive circle : Set :=
  | base : circle
  with eq : circle -> circle -> Set :=
  | eqrefl c : eq c c
  | loop : eq base base.

Definition circle_elim_1 :=
  fun (P : circle -> Set) (P0 : forall a b : circle, P a -> P b -> eq a b -> Set)
    (f : P base)
    (frefl : forall c (pc : P c), P0 c c pc pc (eqrefl c))
    (floop : P0 base base f f loop) =>
    fix F (a : circle) : P a :=
    match a as a0 return (P a0) with
    | base => f
    end
    with F0 (a b : circle) (e : eq a b) {struct e} : P0 a b _ _ e :=
      match e as e0 in (eq a' b') return P0 a' b' (F a') (F b') e0 with
      | eqrefl c => frefl c (F c)
      | loop => floop
      end
        for F.

Definition circle_elim :  forall (P : circle -> Set)
         (P0 : forall a b : circle, P a -> P b -> eq a b -> Set)
         (f : P base)
         (frefl : forall c (pc : P c), P0 c c pc pc (eqrefl c))
         (floop : P0 base base f f loop)
         (a b : circle) (e : eq a b),
    P0 a b (circle_elim_1 P P0 f frefl floop a) (circle_elim_1 P P0 f frefl floop b) e
  :=
  fun (P : circle -> Set) (P0 : forall a b : circle, P a -> P b -> eq a b -> Set)
    (f : P base)
    (frefl : forall c (pc : P c), P0 c c pc pc (eqrefl c))
    (floop : P0 base base f f loop) =>
    fix F (a : circle) : P a :=
    match a as a0 return (P a0) with
    | base => f
    end
    with F0 (a b : circle) (e : eq a b) {struct e} : P0 a b _ _ e :=
      match e as e0 in (eq a' b') return P0 a' b' (F a') (F b') e0 with
      | eqrefl c => frefl c (F c)
      | loop => floop
      end
        for F0.

Definition eqtransport (a b : circle) (P : circle -> Set) (p : P a) (e : eq a b) : P b.
Proof.
  revert p. revert a b e.
  pose (circle_elim (fun c => unit) (fun a b pa pb eq => P a -> P b) tt
                    (fun c pc x => x) (fun x => x)).
  apply p.
Defined.

Definition circle_ind1 (P : circle -> Set)
           (f : P base) (H : eqtransport _ _ P f loop = f) : forall c, P c.
Proof.
  refine (circle_elim_1 P (fun a b pa pb e => eqtransport a b P pa e = pb)  _ _ _).
  intros.
  unfold eqtransport. reflexivity.
  simpl in H.
  apply H.
Defined.

Definition apDc {B:circle->Set} (f:forall a:circle, B a) {x y:circle} (p:eq x y):
  eqtransport x y B (f x) p = f y.
Proof.
  pose(circle_elim (fun a => B a) (fun a b pa pb e => eqtransport a b B pa e = pb)
                   (f base) (fun c bc => eq_refl) eq_refl x y p).
  simpl in *.
  destruct p. destruct c. apply e.
  apply e.
Defined.

Definition circle_ind1_comp (P : circle -> Set)
           (f : P base) (l : eqtransport _ _ P f loop = f) :
  apDc (circle_ind1 P f l) loop = l.
Proof.
  simpl.
  unfold eqtransport in l.
  simpl in l.
  unfold circle_elim in l.
  unfold circle_elim.
Admitted.

Lemma circleeq_to_Z (a b : circle) (e : eq a b) : Z.
Proof.
  refine (circle_elim (fun x => Z) (fun a b az bz e => Z) 0%Z _ _ a b e).
  intros c cz. exact cz%Z. exact 1%Z.
Defined.

Eval compute in circleeq_to_Z base base (eqrefl base).
Eval compute in circleeq_to_Z base base loop.

Lemma eqtrans (a b c : circle) (e : eq a b) (e' : eq b c) : eq a c.
  revert a b e c e'.
  refine (circle_elim (fun x => circle) (fun a b az bz e => forall c, eq b c -> eq a c)
                      base _ _).
  intros. exact H.
  intros. exact H.
Defined.

Eval compute in circleeq_to_Z base base (eqtrans _ _ _ loop loop).
End FullCircle.

Module FullCircle2.
  Inductive circle : Set :=
  | base : circle
  with eq : circle -> circle -> Set :=
  | eqsym c c' : eq c c' -> eq c' c
  (* | eqtrans c c' c'' : eq c c' -> eq c' c'' -> eq c c'' *)
  | loop : eq base base.

Definition circle_elim_1 :=
  fun (P : circle -> Set) (P0 : forall a b : circle, P a -> P b -> eq a b -> Set)
    (f : P base)
    (fsym : forall c c' (pc : P c) (pc' : P c') (e : eq c c'), P0 _ _ pc' pc (eqsym c c' e))
    (floop : P0 base base f f loop) =>
    fix F (a : circle) : P a :=
    match a as a0 return (P a0) with
    | base => f
    end
    with F0 (a b : circle) (e : eq a b) {struct e} : P0 a b _ _ e :=
      match e as e0 in (eq a' b') return P0 a' b' (F a') (F b') e0 with
      | eqsym c c' e => fsym c c' (F c) (F c') e
      | loop => floop
      end
        for F.

Definition circle_elim :  forall (P : circle -> Set)
         (P0 : forall a b : circle, P a -> P b -> eq a b -> Set)
         (f : P base)
    (fsym : forall c c' (pc : P c) (pc' : P c') (e : eq c c'), P0 _ _ pc' pc (eqsym c c' e))
         (floop : P0 base base f f loop)
         (a b : circle) (e : eq a b),
    P0 a b (circle_elim_1 P P0 f fsym floop a) (circle_elim_1 P P0 f fsym floop b) e
  :=
  fun (P : circle -> Set) (P0 : forall a b : circle, P a -> P b -> eq a b -> Set)
    (f : P base)
    (fsym : forall c c' (pc : P c) (pc' : P c') (e : eq c c'), P0 _ _ pc' pc (eqsym c c' e))
    (floop : P0 base base f f loop) =>
    fix F (a : circle) : P a :=
    match a as a0 return (P a0) with
    | base => f
    end
    with F0 (a b : circle) (e : eq a b) {struct e} : P0 a b _ _ e :=
      match e as e0 in (eq a' b') return P0 a' b' (F a') (F b') e0 with
      | eqsym c c' e => fsym c c' (F c) (F c') e
      | loop => floop
      end
        for F0.
*)
(* Definition eqtransport (a b : circle) (P : circle -> Set) (p : P a) (e : eq a b) : P b. *)
(* Proof. *)
(*   revert p. revert a b e. *)
(*   refine (circle_elim (fun c => circle) (fun a b pa pb eq => P a -> P b) base *)
(*                       (fun c c' pc pc' x => _) (fun x => x)). *)
(*   destruct x. *)
(*   apply p. *)
(* Defined. *)

(* Definition circle_ind1 (P : circle -> Set) *)
(*            (f : P base) (H : eqtransport _ _ P f loop = f) : forall c, P c. *)
(* Proof. *)
(*   refine (circle_elim_1 P (fun a b pa pb e => eqtransport a b P pa e = pb)  _ _ _). *)
(*   intros. *)
(*   unfold eqtransport. reflexivity. *)
(*   simpl in H. *)
(*   apply H. *)
(* Defined. *)

(* Definition apDc {B:circle->Set} (f:forall a:circle, B a) {x y:circle} (p:eq x y): *)
(*   eqtransport x y B (f x) p = f y. *)
(* Proof. *)
(*   pose(circle_elim (fun a => B a) (fun a b pa pb e => eqtransport a b B pa e = pb) *)
(*                    (f base) (fun c bc => eq_refl) eq_refl x y p). *)
(*   simpl in *. *)
(*   destruct p. destruct c. apply e. *)
(*   apply e. *)
(* Defined. *)

(* Definition circle_ind1_comp (P : circle -> Set) *)
(*            (f : P base) (l : eqtransport _ _ P f loop = f) : *)
(*   apDc (circle_ind1 P f l) loop = l. *)
(* Proof. *)
(*   simpl. *)
(*   unfold eqtransport in l. *)
(*   simpl in l. *)
(*   unfold circle_elim in l. *)
(*   unfold circle_elim. *)
(* Admitted. *)

(* Lemma circleeq_to_Z (a b : circle) (e : eq a b) : Z. *)
(* Proof. *)
(*   refine (circle_elim (fun x => Z) (fun a b az bz e => Z) 0%Z _ _ a b e). *)
(*   intros c cz. exact cz%Z. exact 1%Z. *)
(* Defined. *)

(* Eval compute in circleeq_to_Z base base (eqrefl base). *)
(* Eval compute in circleeq_to_Z base base loop. *)

(* Lemma eqtrans (a b c : circle) (e : eq a b) (e' : eq b c) : eq a c. *)
(*   revert a b e c e'. *)
(*   refine (circle_elim (fun x => circle) (fun a b az bz e => forall c, eq b c -> eq a c) *)
(*                       base _ _). *)
(*   intros. exact H. *)
(*   intros. exact H. *)
(* Defined. *)

(* Eval compute in circleeq_to_Z base base (eqtrans _ _ _ loop loop). *)
(* End FullCircle2. *)



(* Unset Elimination Schemes. *)
Inductive A : Set :=
  ca : nat -> A
| ca' (a : A) : B a -> A
|ca'' : A
with B : A -> Set :=
     | cba (a : A) : B a
     | cb (n : nat) : B (ca n).

Definition belim :=
  fun (P : A -> Prop) (P0 : forall a : A, P a -> B a -> Prop)
  (f : forall n : nat, P (ca n))
  (f0 : forall (a : A) (pa : P a), forall b : B a, P0 a pa b -> P (ca' a b))
  (f1 : P ca'') (f2 : forall (a : A) (ba : P a), P0 a ba (cba a))
  (f3 : forall n : nat, P0 (ca n) (f n) (cb n)) =>
fix F (a : A) : P a :=
  match a as a0 return (P a0) with
  | ca n => f n
  | ca' a0 b => f0 a0 (F a0) b (F0 a0 b)
  | ca'' => f1
  end
with F0 (a : A) (b : B a) {struct b} : P0 a _ b :=
  match b as b0 in (B a0) return P0 a0 (F a0) b0 with
  | cba a0 => f2 a0 (F a0)
  | cb n => f3 n
  end
    for F0.

Module TyElim2.

Inductive Con : Set :=
| empty : Con
| ext (Γ : Con) : Ty Γ -> Con

with Ty : Con -> Set :=
| Uunit Γ :  Ty Γ
| Upi Γ A (B : Ty (ext Γ A)) : Ty Γ.

  Section elim.
    Variables
      (ConM : Con -> Set)
      (TyM : forall Γ, ConM Γ -> Ty Γ -> Set).

    Record methods :=
      { emptym : ConM empty ;
        extm Γ p (t : Ty Γ) : TyM Γ p t -> ConM (ext _ t);

        Uunitm Γ pΓ : TyM Γ pΓ (Uunit Γ);
        Upim Γ A B pΓ pa : TyM _ (extm _ pΓ _ pa) B -> TyM Γ pΓ (Upi _ A B)
      }.

    Variable m : methods.

    Definition con_elim :=
      fix F (c : Con) : ConM c :=
        match c return (ConM c) with
        | empty => m.(emptym)
        | ext g t => m.(extm) g (F g) t (F0 g t)
        end
        with F0 (a : Con) (t : Ty a) {struct t} : TyM a (F a) t :=
          match t in Ty g return TyM g (F g) t with
          | Uunit g => m.(Uunitm) _ (F g)
          | Upi g a b => m.(Upim) g a b (F g) (F0 g a)
                                 (F0 (ext g a) b : TyM (ext g a) (F (ext g a)) b)
          end
            for F.

    Definition ty_elim : forall Γ (t : Ty Γ), TyM Γ (con_elim Γ) t :=
      fix F (c : Con) : ConM c :=
        match c return (ConM c) with
        | empty => m.(emptym)
        | ext g t => m.(extm) g (F g) t (F0 g t)
        end
        with F0 (a : Con) (t : Ty a) {struct t} : TyM a (F a) t :=
          match t in Ty g return TyM g (F g) t with
          | Uunit g => m.(Uunitm) _ (F g)
          | Upi g a b => m.(Upim) g a b (F g) (F0 g a)
                                 (F0 (ext g a) b : TyM (ext g a) (F (ext g a)) b)
          end
            for F0.
  End elim.

End TyElim2.

Module DTT.

Inductive Con : Set :=
| empty : Con
| ext (Γ : Con) : Ty Γ -> Con

with Ty : Con -> Set :=
| p Γ A : Ty (ext Γ A)
| q Γ A : Ty Γ -> Ty (ext Γ A)
| Uunit Γ :  Ty Γ
| pi Γ A (B : Ty (ext Γ A)) : Ty Γ
| sigma Γ A (B : Ty (ext Γ A)) : Ty Γ
| eq Γ (A : Ty Γ) (a b : Term A) : Ty Γ
| tysubst {Γ Γ'} (s : ConMap Γ Γ') (T : Ty Γ') : Ty Γ

with ConMap : Con -> Con -> Set :=
| id Γ : ConMap Γ Γ
| compose Γ Γ' Γ'' : ConMap Γ Γ' -> ConMap Γ' Γ'' -> ConMap Γ Γ''
| proj Γ A : ConMap (ext Γ A) Γ
| extM Γ A (t : Term A) : ConMap Γ (ext Γ A)

with Term : forall {Γ}, Ty Γ -> Set :=
| lam Γ A B (t : @Term (ext Γ A) B) : Term (pi Γ A B)
| tsubst Γ Γ' (s : ConMap Γ Γ') A (t : @Term Γ' A) : @Term Γ (tysubst s A)
| v Γ A : Term (p Γ A)
| app Γ A B (t : Term (pi Γ A B)) (u : Term A) : Term (tysubst (extM _ _ u) B)
| utt Γ : Term (Uunit Γ)
| eqrefl Γ (A : Ty Γ) (a : Term A) : Term (eq Γ A a a)

with TyEq : forall {Γ}, Ty Γ -> Ty Γ -> Set :=
| eqTefl Γ (t : Ty Γ) : TyEq t t

with TermEq : forall {Γ} {T : Ty Γ} (t u : Term Γ T), Set :=
| eqtermrefl Γ A : TermEq (v Γ A) (v Γ A)
| betaeq Γ A (B : Ty (ext Γ A)) t u :
    TermEq (app _ _ _ (lam Γ A B t) u) (tsubst _ _ (extM _ _ u) _ t).

Scheme con_elim := Induction for Con Sort Type
with ty_elim := Induction for Ty Sort Type
with ConMap_elim := Induction for ConMap Sort Type
with Term_elim := Induction for Term Sort Type
with TyEq_elim := Induction for TyEq Sort Type
with TermEq_elim := Induction for TermEq Sort Type.

End DTT.

(* Fixpoint El Γ (T : Ty Γ) (val : forall n, Γ -> Type) : Set := *)
(*   match T with *)
(*   | p g a =>  *)
(*   | unitcode _ => unit *)
(*   | pi Γ A B => forall X : El _ A, El _ B *)
(*   | sigma Γ A B => unit *)
(*   end *)

(* with val (Γ : Con) := *)
(*   match Γ with *)
(*   | empty => unit *)
(*   | ext Γ A => (val Γ x El Γ A) *)
(*   end. *)

(* Inductive valuation : Con -> Set := *)
(* | valempty : valuation empty *)
(* | valext Γ A (v : valuation Γ) (el : El Γ v A) : valuation (ext Γ A). *)
(* with El : forall Γ : Con, valuation Γ -> Ty Γ -> Set := *)
(* | Elunit Γ v : El Γ v (unitcode _). *)


(* Definition tyel := *)
(*   ty_elim *)
(*     (fix con c := match c with empty => unit | ext Γ A => {g : con Γ & Set} end) *)
(*     (fun c ty => Set) *)
(*     (fun Γ Γ' s => Set) *)
(*     tt *)
(*     (fun Γ g T ty => existT _ g ty) *)
(*     (fun Γ g A a => a) *)
(*     (fun Γ g A a T t => t) *)
(*     (fun Γ g => unit) *)
(*     (fun Γ g A a B b => forall x : a, b) *)
(*     (fun Γ g A a B b => { x : a &  b }). *)

(* Eval compute in tyel _ (pi empty (Uunit _) (p _ _)). *)
