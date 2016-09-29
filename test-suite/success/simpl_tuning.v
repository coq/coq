(* as it is dynamically inferred by simpl *)
Arguments minus !n / m.

Lemma foo x y : S (S x) - S y = 0.
simpl.
match goal with |- (match y with O => S x | S _ => _ end = 0) => idtac end.
Abort. 

(* we avoid exposing a match *)
Arguments minus n m : simpl nomatch. 

Lemma foo x : minus 0 x = 0.
simpl.
match goal with |- (0 = 0) => idtac end.
Abort.

Lemma foo x y : S (S x) - S y = 0.
simpl.
match goal with |- (S x - y = 0) => idtac end.
Abort.

Lemma foo x y : S (S x) - (S (match y with O => O | S z => S z end)) = 0.
simpl.
match goal with |-(S x - (match y with O => _ | S _ => _ end) = 0) => idtac end.
Abort.

(* we unfold as soon as we have 1 args, but we avoid exposing a match *)
Arguments minus n / m : simpl nomatch. 

Lemma foo : minus 0 = fun x => 0.
simpl.
match goal with |- minus 0 = _ => idtac end.
Abort.
(* This does not work as one may expect. The point is that simpl is implemented
   as "strong (whd_simpl_state)" and after unfolding minus you have
   (fun m => match 0 => 0 | S n => ...) that is already in whd and exposes
   a match, that of course "strong" would reduce away but at that stage
   we don't know, and reducing by hand under the lambda is against whd *) 

(* extra tuning for the usual heuristic *)
Arguments minus !n / m : simpl nomatch. 

Lemma foo x y : S (S x) - S y = 0.
simpl.
match goal with |- (S x - y = 0) => idtac end.
Abort.

Lemma foo x y : S (S x) - (S (match y with O => O | S z => S z end)) = 0.
simpl.
match goal with |-(S x - (match y with O => _ | S _ => _ end) = 0) => idtac end.
Abort.

(* full control *)
Arguments minus !n !m /.

Lemma foo x y : S (S x) - S y = 0.
simpl.
match goal with |- (S x - y = 0) => idtac end.
Abort.

Lemma foo x y : S (S x) - (S (match y with O => O | S z => S z end)) = 0.
simpl.
match goal with |-(S x - (match y with O => _ | S _ => _ end) = 0) => idtac end.
Abort.

(* omitting /, that being immediately after the last ! is irrelevant *)
Arguments minus !n !m.

Lemma foo x y : S (S x) - S y = 0.
simpl.
match goal with |- (S x - y = 0) => idtac end.
Abort.

Lemma foo x y : S (S x) - (S (match y with O => O | S z => S z end)) = 0.
simpl.
match goal with |-(S x - (match y with O => _ | S _ => _ end) = 0) => idtac end.
Abort.

Definition pf (D1 C1 : Type) (f : D1 -> C1) (D2 C2 : Type) (g : D2 -> C2) := 
  fun x => (f (fst x), g (snd x)).

Delimit Scope foo_scope with F.
Notation "@@" := nat (only parsing) : foo_scope.
Notation "@@" := (fun x => x) (only parsing).

Arguments pf {D1%F C1%type} f [D2 C2] g x : simpl never.

Lemma foo x : @pf @@ nat @@ nat nat @@ x = pf @@ @@ x.
Abort.

Definition fcomp A B C f (g : A -> B) (x : A) : C := f (g x).

(* fcomp is unfolded if applied to 6 args *)
Arguments fcomp {A B C}%type f g x /.

Notation "f \o g" := (fcomp f g) (at level 50).

Lemma foo (f g h : nat -> nat) x : pf (f \o g) h x = pf f h (g (fst x), snd x).
simpl.
match goal with |- (pf (f \o g) h x = _) => idtac end.
case x; intros x1 x2. 
simpl.
match goal with |- (pf (f \o g) h _ = pf f h _) => idtac end.
unfold pf; simpl.
match goal with |- (f (g x1), h x2) = (f (g x1), h x2) => idtac end.
Abort. 

Definition volatile := fun x : nat => x.
Arguments volatile / _.

Lemma foo : volatile = volatile.
simpl.
match goal with |- (fun _ => _) = _ => idtac end.
Abort.

Set Implicit Arguments.

Section S1.

Variable T1 : Type.

Section S2.

Variable T2 : Type.

Fixpoint f (x : T1) (y : T2) n (v : unit) m {struct n} : nat :=
  match n, m with
  | 0,_ => 0
  | S _, 0 => n
  | S n', S m' => f x y n' v m' end.

Global Arguments f x y !n !v !m.

Lemma foo x y n m : f x y (S n) tt m = f x y (S n) tt (S m).
simpl.
match goal with |- (f _ _ _ _ _ = f _ _ _ _ _) => idtac end.
Abort.

End S2.

Lemma foo T x y n m : @f T x y (S n) tt m = @f T x y (S n) tt (S m).
simpl.
match goal with |- (f _ _ _ _ _ = f _ _ _ _ _) => idtac end.
Abort.

End S1.

Arguments f : clear implicits and scopes.

