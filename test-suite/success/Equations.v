Require Import Program.

Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.
 
Eval compute in neg.

Require Import Coq.Lists.List.

Equations head A (default : A) (l : list A) : A :=
head A default nil := default ;
head A default (cons a v) := a.

Eval compute in head.

Equations tail {A} (l : list A) : (list A) :=
tail A nil := nil ;
tail A (cons a v) := v.

Eval compute in @tail.

Eval compute in (tail (cons 1 nil)).

Reserved Notation " x ++ y " (at level 60, right associativity).

Equations app' {A} (l l' : list A) : (list A) :=
app' A nil l := l ;
app' A (cons a v) l := cons a (app' v l).

Equations app (l l' : list nat) : list nat :=
  [] ++ l       := l ;
  (a :: v) ++ l := a :: (v ++ l) 

where " x ++ y " := (app x y).

Eval compute in @app'.

Equations zip' {A} (f : A -> A -> A) (l l' : list A) : (list A) :=
zip' A f nil nil := nil ;
zip' A f (cons a v) (cons b w) := cons (f a b) (zip' f v w) ;
zip' A f nil (cons b w) := nil ;
zip' A f (cons a v) nil := nil.


Eval compute in @zip'.

Equations zip'' {A} (f : A -> A -> A) (l l' : list A) (def : list A) : (list A) :=
zip'' A f nil nil def := nil ;
zip'' A f (cons a v) (cons b w) def := cons (f a b) (zip'' f v w def) ;
zip'' A f nil (cons b w) def := def ;
zip'' A f (cons a v) nil def := def.

Eval compute in @zip''.

Inductive fin : nat -> Set :=
| fz : Π {n}, fin (S n)
| fs : Π {n}, fin n -> fin (S n).

Inductive finle : Π (n : nat) (x : fin n) (y : fin n), Prop :=
| leqz : Π {n j}, finle (S n) fz j
| leqs : Π {n i j}, finle n i j -> finle (S n) (fs i) (fs j).

Implicit Arguments finle [[n]].


Require Import Bvector.

Implicit Arguments Vnil [[A]].
Implicit Arguments Vcons [[A] [n]].

Equations vhead {A n} (v : vector A (S n)) : A := 
vhead A n (Vcons a v) := a.

Eval compute in (vhead (Vcons 2 (Vcons 1 Vnil))).
Eval compute in @vhead.

Equations vmap {A B} (f : A -> B) {n} (v : vector A n) : (vector B n) :=
vmap A B f 0 Vnil := Vnil ;
vmap A B f (S n) (Vcons a v) := Vcons (f a) (vmap f v).

Eval compute in (vmap id (@Vnil nat)).
Eval compute in (vmap id (@Vcons nat 2 _ Vnil)).
Eval compute in @vmap.

Record vlast_comp (A : Type) (n : nat) (v : vector A (S n)) : Type := { vlast_return : A }.

Class Comp (comp : Type) :=
  return_type : comp -> Type ; call : Π c : comp, return_type c.

Instance vlast_Comp A n v : Comp (vlast_comp A n v) :=
  return_type := λ c, A ;
  call := λ c, vlast_return A n v c.

Ltac ind v := 
  intros until v ; generalize_eqs_vars v ; induction v ; simplify_dep_elim.


Tactic Notation "rec" ident(v) "as" simple_intropattern(p) :=
  (try intros until v) ; generalize_eqs_vars v ; induction v as p ; simplify_dep_elim ; 
    simpl_IH_eqs.

Tactic Notation "rec" hyp(v) :=
  (try intros until v) ; generalize_eqs_vars v ; induction v ; simplify_dep_elim ; 
    simpl_IH_eqs.

Tactic Notation "case" "*" hyp(v) "as" simple_intropattern(p) :=
  (try intros until v) ; generalize_eqs_vars v ; destruct v as p ; simplify_dep_elim.

Tactic Notation "case" "*" hyp(v) :=
  (try intros until v) ; generalize_eqs_vars v ; destruct v ; simplify_dep_elim.

Tactic Notation "=>" constr(v) := 
  constructor ; 
    match goal with
      | [ |- ?T ] => refine (v:T)
    end.

Ltac make_refls_term c app :=
  match c with
    | _ = _ -> ?c' => make_refls_term (app (@refl_equal _ _))
    | @JMeq _ _ _ _ -> ?c' => make_refls_term (app (@JMeq_refl _ _))
    | _ => constr:app
  end.

Ltac make_refls_IH c app :=
  match c with
    | Π x : _, ?c' => make_refls_IH (app _)
    | _ => make_refls_term c app
  end.

Ltac simpl_IH H :=
  let ty := type of H in
    make_refls_IH ty H.

Ltac move_top H :=
  match reverse goal with [ H' : _ |- _ ] => move H after H' end.

Ltac simplify_dep_elim_hyp H evhyp :=
  let ev := eval compute in evhyp in
    subst evhyp ; intros evhyp ; move_top evhyp ; simplify_dep_elim ; 
      try clear H ; reverse ; intro evhyp ; eapply evhyp.

(* Tactic Notation "strengthen" hyp(H) := *)
(*   let strhyp := fresh "H'" in *)
(*   let ty := type of H in *)
(*     on_last_hyp ltac:(fun id => *)
(*       reverse ; evar (strhyp:Type) ; intros until id). *)

(*         assert(strhyp -> ty) ; [ simplify_dep_elim_hyp strhyp | intros ]). *)


Equations Below_nat (P : nat -> Type) (n : nat) : Type :=
Below_nat P 0 := unit ;
Below_nat P (S n) := prod (P n) (Below_nat P n).

Equations below_nat (P : nat -> Type) n (step : Π (n : nat), Below_nat P n -> P n) : Below_nat P n :=
below_nat P 0 step := tt ;
below_nat P (S n) step := let rest := below_nat P n step in
  (step n rest, rest).

Class BelowPack (A : Type) :=
  Below : Type ; below : Below.

Instance nat_BelowPack : BelowPack nat :=
  Below := Π P n step, Below_nat P n ;
  below := λ P n step, below_nat P n (step P).

Definition rec_nat (P : nat -> Type) n (step : Π n, Below_nat P n -> P n) : P n :=
  step n (below_nat P n step).

Fixpoint Below_vector (P : Π A n, vector A n -> Type) A n (v : vector A n) : Type :=
  match v with Vnil => unit | Vcons a n' v' => prod (P A n' v') (Below_vector P A n' v') end.

(* Equations Below_vector (P : Π A n, vector A n -> Type) A n (v : vector A n) : Type := *)
(* Below_vector P A ?(0) Vnil := unit ; *)
(* Below_vector P A ?(S n) (Vcons a v) := prod (P A n v) (Below_vector P A n v). *)

Equations below_vector (P : Π A n, vector A n -> Type) A n (v : vector A n)
  (step : Π A n (v : vector A n), Below_vector P A n v -> P A n v) : Below_vector P A n v :=
below_vector P A 0 Vnil step := tt ;
below_vector P A (S n) (Vcons a v) step := 
  let rest := below_vector P A n v step in
    (step A n v rest, rest).

Instance vector_BelowPack : BelowPack (Π A n, vector A n) :=
  Below := Π P A n v step, Below_vector P A n v ;
  below := λ P A n v step, below_vector P A n v (step P).

Instance vector_noargs_BelowPack A n : BelowPack (vector A n) :=
  Below := Π P v step, Below_vector P A n v ;
  below := λ P v step, below_vector P A n v (step P).

Definition rec_vector (P : Π A n, vector A n -> Type) A n v
  (step : Π A n (v : vector A n), Below_vector P A n v -> P A n v) : P A n v :=
  step A n v (below_vector P A n v step).

Class Recursor (A : Type) (BP : BelowPack A) := 
  rec_type : Π x : A, Type ; rec : Π x : A, rec_type x.

Instance nat_Recursor : Recursor nat nat_BelowPack :=
  rec_type := λ n, Π P step, P n ;
  rec := λ n P step, rec_nat P n (step P).

(* Instance vect_Recursor : Recursor (Π A n, vector A n) vector_BelowPack := *)
(*   rec_type := Π (P : Π A n, vector A n -> Type) step A n v, P A n v; *)
(*   rec := λ P step A n v, rec_vector P A n v step. *)

Instance vect_Recursor_noargs A n : Recursor (vector A n) (vector_noargs_BelowPack A n) :=
  rec_type := λ v, Π (P : Π A n, vector A n -> Type) step, P A n v;
  rec := λ v P step, rec_vector P A n v step.

Implicit Arguments Below_vector [P A n].

Notation " x ~= y " := (@JMeq _ x _ y) (at level 70, no associativity).

Ltac idify := match goal with [ |- ?T ] => change (id T) end.

(*  induction v as [ | a v']; simplify_dep_elim. *)
(*   on_last_hyp ltac:(fun id => *)
(*     let strhyp := fresh "H'" in *)
(*     let ty := type of IHv in *)
(*       reverse ; evar (strhyp:Type) ; intros ; *)
(*         let newhyp := fresh "IHv''" in *)
(*           assert(ty = strhyp) ; [ idtac (* simplify_dep_elim_hyp IHv strhyp *) | idtac ]). *)
(* (*         subst strhyp ; intros ; try (apply newhyp in IHv) ]). *) *)

Ltac simpl_rec X :=
  match type of X with
    | ?f (?c ?x) =>  
      let X1 := fresh in
      let X2 := fresh in
        hnf in X ; destruct X as [X1 X2] ; simplify_hyp X1
    | _ => idtac
  end.

Ltac recur v :=
  try intros until v ; generalize_eqs_vars v ; reverse ;
  intros until v ; assert (recv:=rec v) ; simpl in recv ;
    eapply recv; clear ; simplify_dep_elim.

Definition vlast {A} {n} (v : vector A (S n)) : vlast_comp A n v.
recur v. case* v0. case* v0. => a. simpl_rec X.
=> (call H).
Defined.
  
Record trans_comp {n:nat} {i j k : fin n} (p : finle i j) (q : finle j k) :=  {
  return_comp : finle i k }.

Equations trans {n} {i j k : fin n} (p : finle i j) (q : finle j k) : finle i k :=
trans (S n) fz j k leqz q := leqz ;
trans (S n) (fs i) (fs j) (fs k) (leqs p) (leqs q) := leqs (trans p q).

Lemma trans_eq1 n (j k : fin (S n)) (q : finle j k) : trans leqz q = leqz.
Proof. intros. simplify_equations ; reflexivity. Qed.

Lemma trans_eq2 n i j k p q : @trans (S n) (fs i) (fs j) (fs k) (leqs p) (leqs q) = leqs (trans p q).
Proof. intros. simplify_equations ; reflexivity. Qed.

Section Image.
  Context {S T : Type}.
  Variable f : S -> T.
  
  Inductive Imf : T -> Type := imf (s : S) : Imf (f s).

  Equations inv (t : T) (im : Imf t) : S :=
  inv (f s) (imf s) := s.

End Image.

Section Univ.

  Inductive univ : Set :=
  | ubool | unat | uarrow (from:univ) (to:univ).

  Equations interp (u : univ) : Type :=
  interp ubool := bool ; interp unat := nat ; 
  interp (uarrow from to) := interp from -> interp to.

  Equations foo (u : univ) (el : interp u) : interp u :=
  foo ubool true := false ;
  foo ubool false := true ;
  foo unat t := t ;
  foo (uarrow from to) f := id ∘ f.

  Eval lazy beta delta [ foo foo_obligation_1 foo_obligation_2 ] iota zeta in foo.

End Univ.

Eval compute in (foo ubool false).
Eval compute in (foo (uarrow ubool ubool) negb).
Eval compute in (foo (uarrow ubool ubool) id).

(* Overlap. *)

Inductive foobar : Set := bar | baz.

Equations bla f : bool :=
bla bar := true ;
bla baz := false.

Eval simpl in bla.
Print refl_equal.

Notation "'refl'" := (@refl_equal _ _).

Equations K {A} (x : A) (P : x = x -> Type) (p : P (refl_equal x)) (p : x = x) : P p :=
K A x P p refl := p.

Equations eq_sym {A} (x y : A) (H : x = y) : y = x :=
eq_sym A x x refl := refl.

(* Obligation Tactic := idtac. *)

Equations eq_trans {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eq_trans A x x x refl refl := refl.

Lemma eq_trans_eq A x : @eq_trans A x x x refl refl = refl.
Proof. reflexivity. Qed.

Equations nth {A} {n} (v : vector A n) (f : fin n) : A :=
nth A (S n) (Vcons a v) fz := a ;
nth A (S n) (Vcons a v) (fs f) := nth v f.

Equations tabulate {A} {n} (f : fin n -> A) : vector A n :=
tabulate A 0 f := Vnil ;
tabulate A (S n) f := Vcons (f fz) (tabulate (f ∘ fs)).

Equations vlast' {A} {n} (v : vector A (S n)) : A :=
vlast' A 0 (Vcons a Vnil) := a ;
vlast' A (S n) (Vcons a v) := vlast' v.

Lemma vlast_equation1 A (a : A) : vlast' (Vcons a Vnil) = a.
Proof. intros. compute ; reflexivity. Qed.

Lemma vlast_equation2 A n a v : @vlast' A (S n) (Vcons a v) = vlast' v.
Proof. intros. compute ; reflexivity. Qed.

Print Assumptions vlast.
Print Assumptions nth. 
Print Assumptions tabulate. 

Equations vliat {A} {n} (v : vector A (S n)) : vector A n :=
vliat A 0 (Vcons a Vnil) := Vnil ;
vliat A (S n) (Vcons a v) := Vcons a (vliat v).

Eval compute in (vliat (Vcons 2 (Vcons 5 (Vcons 4 Vnil)))).

Equations vapp {A} {n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vapp A 0 m Vnil w := w ;
vapp A (S n) m (Vcons a v) w := Vcons a (vapp v w).

Lemma JMeq_Vcons_inj A n m a (x : vector A n) (y : vector A m) : n = m -> JMeq x y -> JMeq (Vcons a x) (Vcons a y).
Proof. intros until y. simplify_dep_elim. reflexivity. Qed.

Equations NoConfusion_fin (P : Prop) {n : nat} (x y : fin n) : Prop :=
NoConfusion_fin P ?(S n) fz fz := P -> P ;
NoConfusion_fin P ?(S n) fz (fs y) := P ;
NoConfusion_fin P ?(S n) (fs x) fz := P ;
NoConfusion_fin P ?(S n) (fs x) (fs y) := (x = y -> P) -> P.

Equations noConfusion_fin P (n : nat) (x y : fin n) (H : x = y) : NoConfusion_fin P x y :=
noConfusion_fin P (S n) fz fz refl := λ p, p ;
noConfusion_fin P (S n) (fs x) (fs x) refl := λ p : x = x -> P, p refl.

Equations NoConfusion_vect (P : Prop) {A n} (x y : vector A n) : Prop :=
NoConfusion_vect P A 0 Vnil Vnil := P -> P ;
NoConfusion_vect P A (S n) (Vcons a x) (Vcons b y) := (a = b -> x = y -> P) -> P.

(* Equations noConfusion_vect (P : Prop) A n (x y : vector A n) (H : x = y) : NoConfusion_vect P x y := *)
(* noConfusion_vect P A 0 Vnil Vnil refl := λ p, p ; *)
(* noConfusion_vect P A (S n) (Vcons a v) (Vcons a v) refl := λ p : a = a -> v = v -> P, p refl refl. *)

(* Instance fin_noconf n : NoConfusionPackage (fin n) := *)
(*   NoConfusion := λ P, Π x y, x = y -> NoConfusion_fin P x y ; *)
(*   noConfusion := λ P x y, noConfusion_fin P n x y. *)

(* Instance vect_noconf A n : NoConfusionPackage (vector A n) := *)
(*   NoConfusion := λ P, Π x y, x = y -> NoConfusion_vect P x y ; *)
(*   noConfusion := λ P x y, noConfusion_vect P A n x y. *)

Equations fog {n} (f : fin n) : nat :=
fog (S n) fz := 0 ; fog (S n) (fs f) := S (fog f).

About vapp.

Inductive Split {X : Set}{m n : nat} : vector X (m + n) -> Set :=
  append : Π (xs : vector X m)(ys : vector X n), Split (vapp xs ys).

Implicit Arguments Split [[X]].

Equations split {X : Set}(m n : nat) (xs : vector X (m + n)) : Split m n xs :=
split X 0    n xs := append Vnil xs ;
split X (S m) n (Vcons x xs) := 
  let 'append xs' ys' in Split _ _ vec := split m n xs return Split (S m) n (Vcons x vec) in
    append (Vcons x xs') ys'.

Eval compute in (split 0 1 (vapp Vnil (Vcons 2 Vnil))).
Eval compute in (split _ _ (vapp (Vcons 3 Vnil) (Vcons 2 Vnil))).

Extraction Inline split_obligation_1 split_obligation_2.

Recursive Extraction split.

Eval compute in @split.
