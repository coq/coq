Require Import Bvector.
Require Import Program.

Obligation Tactic := try equations.

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

Eval compute in tail.

Eval compute in (tail _ (cons 1 nil)).

Equations app' {A} (l l' : list A) : (list A) :=
app' A nil l := l ;
app' A (cons a v) l := cons a (app v l).

Eval compute in app'.

Fixpoint zip {A} (f : A -> A -> A) (l l' : list A) : list A :=
  match l, l' with
    | nil, nil => nil
    | cons a v, cons b v' => cons (f a b) (zip f v v')
    | _, _ => nil
  end.

Equations zip' {A} (f : A -> A -> A) (l l' : list A) : (list A) :=
zip' A f nil nil := nil ;
zip' A f (cons a v) (cons b w) := cons (f a b) (zip f v w) ;
zip' A f nil (cons b w) := nil ;
zip' A f (cons a v) nil := nil.

Eval compute in zip'.

Eval cbv delta [ zip' zip'_obligation_1 zip'_obligation_2 zip'_obligation_3 ] beta iota zeta in zip'.

Equations zip'' {A} (f : A -> A -> A) (l l' : list A) (def : list A) : (list A) :=
zip'' A f nil nil def := nil ;
zip'' A f (cons a v) (cons b w) def := cons (f a b) (zip f v w) ;
zip'' A f nil (cons b w) def := def ;
zip'' A f (cons a v) nil def := def.

Eval compute in zip''.
Eval cbv delta [ zip'' ] beta iota zeta in zip''.

Implicit Arguments Vnil [[A]].
Implicit Arguments Vcons [[A] [n]].

Equations vhead A n (v : vector A (S n)) : A := 
vhead A n (Vcons a v) := a.

Eval compute in (vhead _ _ (Vcons 2 (Vcons 1 Vnil))).

Axiom cheat : Π A, A.

Equations vmap {A B} (f : A -> B) n (v : vector A n) : (vector B n) :=
vmap A B f 0 Vnil := Vnil ;
vmap A B f (S n) (Vcons a v) := Vcons (f a) (cheat _).

Eval compute in (vmap _ _ id _ (@Vnil nat)).
Eval compute in (vmap _ _ id _ (@Vcons nat 2 _ Vnil)).

Inductive fin : nat -> Set :=
| fz : Π {n}, fin (S n)
| fs : Π {n}, fin n -> fin (S n).

Inductive finle : Π (n : nat) (x : fin n) (y : fin n), Prop :=
| leqz : Π {n j}, finle (S n) fz j
| leqs : Π {n i j}, finle n i j -> finle (S n) (fs i) (fs j).

Implicit Arguments finle [[n]].

Equations trans {n} {i j k : fin n} (p : finle i j) (q : finle j k) : finle i k :=
trans (S n) fz j k leqz q := leqz ;
trans (S n) (fs i) (fs j) fz (leqs p) q :=! q ;
trans (S n) (fs i) (fs j) (fs k) (leqs p) (leqs q) := leqs (cheat _).

Lemma trans_eq1 n (j k : fin (S n)) q : trans (S n) fz j k leqz q = leqz.
Proof. intros. simplify_equations ; reflexivity. Qed.

Lemma trans_eq2 n i j k p q : trans (S n) (fs i) (fs j) (fs k) (leqs p) (leqs q) = leqs (cheat _).
Proof. intros. simplify_equations ; reflexivity. Qed.

Section Image.
  Context {S T : Type}.
  Variable f : S -> T.
  
  Inductive Imf : T -> Type := imf (s : S) : Imf (f s).

  Equations inv (t : T) (im : Imf t) : S :=
  inv (f s) (imf s) := s.

  Eval compute in inv.

End Image.