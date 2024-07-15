(* Playing with (co-)fixpoints with local definitions *)

Inductive listn : nat -> Set :=
  niln : listn 0
| consn : forall n:nat, nat -> listn n -> listn (S n).

Fixpoint f (n:nat) (m:=pred n) (l:listn m) (p:=S n) {struct l} : nat :=
   match n with O => p | _ =>
     match l with niln => p | consn q _ l => f (S q) l end
   end.

Eval compute in (f 2 (consn 0 0 niln)).

CoInductive Stream : nat -> Set :=
  Consn : forall n, nat -> Stream n -> Stream (S n).

CoFixpoint g (n:nat) (m:=pred n) (l:Stream m) (p:=S n) : Stream p :=
    match n return (let m:=pred n in forall l:Stream m, let p:=S n in Stream p)
    with
    | O => fun l:Stream 0 => Consn O 0 l
    | S n' =>
      fun l:Stream n' =>
      let l' :=
        match l in Stream q return Stream (pred q) with Consn _ _ l => l end
      in
      let a := match l with Consn _ a l => a end in
      Consn (S n') (S a) (g n' l')
   end l.

Eval compute in (fun l => match g 2 (Consn 0 6 l) with Consn _ a _ => a end).

(* Check inference of simple types in presence of non ambiguous
   dependencies (needs revision 10125) *)

Section folding.

Inductive vector (A:Type) : nat -> Type :=
  | Vnil : vector A 0
  | Vcons : forall (a:A) (n:nat), vector A n -> vector A (S n).

Variables (B C : Set) (g : B -> C -> C) (c : C).

Fixpoint foldrn n bs :=
  match bs with
  | Vnil _ => c
  | Vcons _ b _ tl => g b (foldrn _ tl)
  end.

End folding.

(* Check definition by tactics *)

Inductive even : nat -> Type :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Type :=
    odd_S : forall n, even n -> odd (S n).

Fixpoint even_div2 n (H:even n) : nat :=
  match H with
  | even_O => 0
  | even_S n H => S (odd_div2 n H)
  end
with odd_div2 n H : nat.
destruct H.
apply even_div2 with n.
assumption.
Qed.

Fixpoint even_div2' n (H:even n) : nat with odd_div2' n (H:odd n) : nat.
destruct H.
exact 0.
apply odd_div2' with n.
assumption.
destruct H.
apply even_div2' with n.
assumption.
Qed.

CoInductive Stream1 (A B:Type) := Cons1 : A -> Stream2 A B -> Stream1 A B
with Stream2 (A B:Type) := Cons2 : B -> Stream1 A B -> Stream2 A B.

CoFixpoint ex1 (n:nat) (b:bool) : Stream1 nat bool
with ex2 (n:nat) (b:bool) : Stream2 nat bool.
apply Cons1.
exact n.
apply (ex2 n b).
apply Cons2.
exact b.
apply (ex1 (S n) (negb b)).
Defined.

Section visibility.

  Let Fixpoint imm (n:nat) : True := I.

  Let Fixpoint by_proof (n:nat) : True.
  Proof. exact I. Defined.

  Let Fixpoint foo (n:nat) : bool with bar (n:nat) : bool.
  Proof.
    - destruct n as [|n].
      + exact true.
      + exact (bar n).
    - destruct n as [|n].
      + exact false.
      + exact (foo n).
  Qed.

  Let Fixpoint bla (n:nat) : Type with bli (n:nat) : bool.
  Admitted.

End visibility.

Fail Check imm.
Fail Check by_proof.
Check bla. Check bli.

Module Import mod_local.
  Fixpoint imm_importable (n:nat) : True := I.

  Local Fixpoint imm_local (n:nat) : True := I.

  Fixpoint by_proof_importable (n:nat) : True.
  Proof. exact I. Defined.

  Local Fixpoint by_proof_local (n:nat) : True.
  Proof. exact I. Defined.
End mod_local.

Check imm_importable.
Fail Check imm_local.
Check mod_local.imm_local.
Check by_proof_importable.
Fail Check by_proof_local.
Check mod_local.by_proof_local.

(* Miscellaneous tests *)

Module IotaRedex.

Fixpoint minus (n m:nat) {struct n} : nat :=
  match (n, m) with
  | (O , _) => O
  | (S _ , O) => n
  | (S n', S m') => minus n' m'
  end.

End IotaRedex.

Module ReturningInductive.

Fail Fixpoint geneq s (x: list nat) {struct s} : Prop :=
  match x with
  | cons a t => geneq (S a) t /\ geneq (S a) t
  | _ => False
  end.

End ReturningInductive.

Module NestingAndUnfolding.

Fail Fixpoint f (x:nat) := id (fix g x : nat := f x) 0.

Fixpoint f x :=
  match x with
  | 0 => 0
  | S n => id (fix g x := f x) n
  end.

End NestingAndUnfolding.

Module NestingAndConstructedUnfolding.

Definition fold_left {A B : Type} (f : A -> B -> A) :=
fix fold_left (l : list B) (a0 : A) {struct l} : A :=
  match l with
  | nil => a0
  | cons b t => fold_left t (f a0 b)
  end.

Record t A : Type :=
    mk {
        elt: A
      }.

Arguments elt {A} t.

Inductive LForm : Type :=
| LIMPL : t LForm -> list (t LForm) -> LForm.

Fixpoint hcons  (m : unit) (f : LForm) :=
  match f with
  | LIMPL f l => fold_left (fun m f => hcons m f.(elt) ) (cons f l) m
  end.
End NestingAndConstructedUnfolding.

Module CofixRedex.

CoInductive Stream := {hd : nat; tl : Stream}.
Definition zeros := cofix zeros := {|hd := 0; tl := zeros|}.

Fixpoint f n :=
  match n with
  | 0 => 0
  | S n =>
    match zeros with
    | {|hd:=_|} => fun f => f n
    end f
  end.

End CofixRedex.

Module CofixRedexPrimProj.

Set Primitive Projections.
CoInductive Stream A := {hd : A; tl : Stream A}.
Arguments hd {A} s.

Fixpoint f n :=
  match n with
  | 0 => 0
  | S n => (cofix cst := {|hd := (fun f => f n); tl := cst|}).(hd) f
  end.

End CofixRedexPrimProj.

Module ArgumentsAcrossMatch.

(* large subterm passed across match *)
Fail Fixpoint f n p {struct n} :=
  match n with
  | 0 => fun _ => 0
  | S q => fun r => f q (f r 0)
  end n.

(* strict subterm passed across match *)
Fixpoint f n p {struct n} :=
  match n with
  | 0 => 0
  | S q =>
     match q with
     | 0 => fun _ => 0
     | S q' => fun r => f q (f r 0)
     end q
  end.

End ArgumentsAcrossMatch.

Module LetToExpand.

Fixpoint h n :=
  let f n := (fun x : h n -> True => True) (fun y : h n => I) in
  match n with
  | 0 => True
  | S n => f n
  end.

End LetToExpand.

Module RecursiveCallInsideCoFix.

CoInductive I := { field : I }.

Fail Fixpoint f (n:nat) :=
  (cofix g n := {| field := f n |}) 0.

End RecursiveCallInsideCoFix.

Module NestedRedexes.

Fixpoint f n :=
  match n with
  | 0 => 0
  | S n => id (fun x => id (fun _ => id (f x)) 0) n
  end.

End NestedRedexes.

Module NestedRedexesWithCofix.

CoInductive I := { field : nat -> nat }.

Fail Fixpoint f n :=
  ((cofix g h := {| field := h |}) f).(field) n.

Fixpoint f n :=
  match n with
  | 0 => 0
  | S p => ((cofix g h := {| field := h |}) f).(field) p
  end.

End NestedRedexesWithCofix.

Module NestedApplicationsWithVariables.

Section S.
Variable h : (nat -> nat) -> nat.
Fixpoint f n :=
  match n with
  | 0 => 0
  | S p => (fun _ => 0) (h f)
  end.
End S.

End NestedApplicationsWithVariables.

Module NestedApplicationsWithParameters.

Parameter h : (nat -> nat) -> nat.
Fixpoint f n :=
  match n with
  | 0 => 0
  | S p => (fun _ => 0) (h f)
  end.

End NestedApplicationsWithParameters.

Module NestedApplicationsWithLocalVariables.

Fixpoint f (h:(nat->nat)->nat) n :=
  match n with
  | 0 => 0
  | S p => (fun _ => 0) (h (f h))
  end.

End NestedApplicationsWithLocalVariables.

Module NestedApplicationsWithProjections.

Set Primitive Projections.
Record R := { field : (nat -> nat) -> nat }.

Fixpoint f x n :=
  match n with
  | 0 => 0
  | S p => (fun _ => 0) (x.(field) (f x))
  end.

End NestedApplicationsWithProjections.

Module NestedRedexesWithFix.

Fixpoint f n :=
  match n with
  | 0 => 0
  | S p => (fun _ => 0) ((fix h k (q:nat) {struct q} := k) f)
  end.

(* inner fix fully applied with a match subterm *)
Fixpoint f' n :=
  match n with
  | 0 => 0
  | S p => (fun _ => 0) ((fix h k (q:nat) {struct q} := k) f' p)
  end.

(* inner fix fully applied with an arbitrary term *)
Fixpoint f'' o n :=
  match n with
  | 0 => 0
  | S p => (fun _ => 0) ((fix h k (q:nat) {struct q} := k o) f'' o)
  end.

End NestedRedexesWithFix.

Module NestedRedexesWithMatch.

Fixpoint f o n :=
  match n with
  | 0 => 0
  | S p => (fun _ => 0) (match o with tt => f o end)
  end.

Fixpoint f' o n :=
  match n with
  | 0 => 0
  | S p => (fun _ => 0) ((match o with tt => fun x => x o end) f')
  end.

End NestedRedexesWithMatch.

Module ErasableInertSubterm.

Fixpoint P (n:nat) :=
  (fun _ => True) (forall a : (forall p, P p), True).

End ErasableInertSubterm.

Module WithLetInLift.

Fixpoint f (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n => (let x := 0 in fun n => f n) n
  end.

End WithLetInLift.

Module WithLateCaseReduction.

Definition B := true.
Fixpoint f (n : nat) :=
  match n with
  | 0 => 0
  | S n => (if B as b return if b then nat -> nat else unit then fun n => f n else tt) n
  end.

End WithLateCaseReduction.

Module NtnInteractiveFixpoint.

Reserved Notation "# n" (at level 2, right associativity).
Fixpoint f (n:nat) : nat where "# n" := (f n).
exact (match n with 0 => 0 | S n => # n end).
Defined.
Check eq_refl : # 0 = f 0.

End NtnInteractiveFixpoint.

Module NoArgumentFixpoint.

Fail Fixpoint f : nat. (* was an anomaly at some time *)

End NoArgumentFixpoint.

Module FixpointRelevance.

(* Check that the recursive reference to a fixpoint name has correct
   relevance, in different execution paths *)

Inductive STrue : SProp := SI.
Inductive seq (a:STrue) : STrue -> SProp := srefl : seq a a.
Fixpoint g1 (n:nat) : STrue :=
  match n with
  | 0 => SI
  | S n => let x := srefl (g1 n) : seq (g1 n) (g2 n) in g2 n
  end
with g2 (n:nat) : STrue :=
  match n with
  | 0 => SI
  | S n => let x := srefl (g1 n) : seq (g1 n) (g2 n) in g1 n
  end.
Fixpoint h1 (n:nat) : STrue with h2 (n:nat) : STrue.
exact
 (match n with
  | 0 => SI
  | S n => let x := srefl (h1 n) : seq (h1 n) (h2 n) in h2 n
  end).
exact
 (match n with
  | 0 => SI
  | S n => let x := srefl (h1 n) : seq (h1 n) (h2 n) in h1 n
  end).
Defined.
Theorem k1 (n:nat) : STrue with k2 (n:nat) : STrue.
exact
 (match n with
  | 0 => SI
  | S n => let x := srefl (k1 n) : seq (k1 n) (k2 n) in k2 n
  end).
exact
 (match n with
  | 0 => SI
  | S n => let x := srefl (k1 n) : seq (k1 n) (k2 n) in k1 n
  end).
Defined.

End FixpointRelevance.

Module ClearFixBody.

CoInductive Stream : Set := Cons : nat -> Stream -> Stream.

Section S.
#[clearbody] Let CoFixpoint f : Stream := Cons 1 f.
#[clearbody] Let Fixpoint g n := match n with 0 => 0 | S n => g n end.
Goal True.
Fail Check eq_refl : f = cofix f := Cons 1 f.
Fail Check eq_refl : g = fix g n := match n with 0 => 0 | S n => g n end.
Abort.
End S.

End ClearFixBody.

Module TheoremWithUnivs.

Fail Fixpoint f@{u} (n:nat) : nat with g@{v} (n:nat) : nat.
Fail Theorem f@{u} (n:nat) : nat with g@{v} (n:nat) : nat.
Fail CoFixpoint f@{u} (n:nat) : Stream 0 with g@{v} (n:nat) : Stream 0.
Succeed Fixpoint f@{u} (n:nat) : nat with g@{u} (n:nat) : nat.
Succeed Theorem f@{u} (n:nat) : nat with g@{u} (n:nat) : nat.
Succeed CoFixpoint f@{u} (n:nat) : Stream 0 with g@{u} (n:nat) : Stream 0.
Succeed Fixpoint f@{u} (n:nat) : nat with g (n:nat) : nat. (* Accepted *)
Succeed Theorem f@{u} (n:nat) : nat with g (n:nat) : nat. (* Accepted *)
Succeed CoFixpoint f@{u} (n:nat) : Stream 0 with g (n:nat) : Stream 0. (* Accepted *)

End TheoremWithUnivs.

Module DependMutualFix.

Inductive tree (A : Type) := Node : A -> list (tree A) -> tree A.

Definition lmap' {A B} (f : A -> B) : list A -> list B :=
fix F l :=
match l with
| nil => nil
| cons x l => cons (f x) (G l)
end
with G l :=
match l with
| nil => nil
| cons x l => cons (f x) (F l)
end for F.

(* Not yet able to accept this *)
Fail Fixpoint map {A B} (f : A -> B) (t : tree A) {struct t} : tree B :=
match t with
| Node _ x l => Node _ (f x) (lmap' (map f) l)
end.

End DependMutualFix.

Module Wish16040.

Inductive tree (A : Type) := Node : A -> list (tree A) -> tree A.

Fixpoint lmap {A B} (f : A -> B) (l : list A) : list B :=
match l with
| nil => nil
| cons x l => cons (f x) (lmap f l)
end.

Fixpoint map {A B} (f : A -> B) (t : tree A) {struct t} : tree B :=
match t with
| Node _ x l => Node _ (f x) (lmap (map f) l)
end.

(* Check that we don't find too much uniform parameters *)

Fixpoint lmap' {A} (f g : A -> A) (l : list A) : list A :=
match l with
| nil => nil
| cons x l => cons (f x) (lmap' g f l)
end.

(* Not supposed to be detected guarded, as only A is uniform in lmap' *)
Fail Fixpoint map' {A} (f : A -> A) (t : tree A) {struct t} : tree A :=
match t with
| Node _ x l => Node _ (f x) (lmap' (map' f) (map' f) l)
end.

(* Uniform arguments after a non-uniform one *)

Fixpoint lmap'' {A} n (f : A -> A) (l : list A) : list A :=
match l with
| nil => nil
| cons x l => cons (f x) (lmap'' (S n) f l)
end.

(* The current guard supports extrusion of uniform arguments only in prefix position *)
Fail Fixpoint map'' {A} (f : A -> A) (t : tree A) {struct t} : tree A :=
match t with
| Node _ x l => Node _ (f x) (lmap'' 0 (map'' f) l)
end.

End Wish16040.

Module TheoremWith.

CoInductive Stream : Set := Cons : nat -> Stream -> Stream.

(* Support for mutually recursive theorems in non-mutual types *)
Theorem a : Stream with b : Stream.
Proof.
apply (Cons 0), b.
apply (Cons 0), a.
Defined.

Theorem c (n:nat) : Stream with d (n:nat) : Stream. (* corecursive *)
Proof.
apply (Cons n), (d n).
apply (Cons n), (c n).
Defined.

Theorem c' (n:nat) : Stream with d' (n:nat) : Stream. (* recursive *)
Proof.
destruct n as [|n']. apply a. apply (d' n').
destruct n as [|n']. apply a. apply (c' n').
Defined.

End TheoremWith.

Module HighlyNested.

Inductive T A := E : A * list A * list (list A) -> T A.
Inductive U := H : T (T U) -> U.

Definition map {A B : Type} (f : A -> B) :=
  fix map (l : list A) : list B :=
  match l with
  | nil => nil
  | cons a t => cons (f a) (map t)
  end.

Definition mapT {A B} (f:A -> B) t :=
  match t with E _ (a, l, ll) => E _ (f a, map f l, map (map f) ll) end.

Fixpoint mapU (f:U->U) u :=
  match u with
  | H t => H (mapT (mapT (mapU f)) t)
  end.

End HighlyNested.

Module TestIntersection.

(* This example used to stress rtree.inter (3 nested types) *)

Inductive Pmap_ne (A : Type) :=
| PNode010 : A -> Pmap_ne A
| PNode110 : Pmap_ne A -> A -> Pmap_ne A.
Arguments PNode010 {A} _ : assert.
Arguments PNode110 {A} _ _ : assert.

Variant Pmap (A : Type) := PEmpty : Pmap A | PNodes : Pmap_ne A -> Pmap A.
Arguments PEmpty {A}.
Arguments PNodes {A} _.

Definition Pmap_ne_case {A B} (t : Pmap_ne A) (f : Pmap A -> option A -> Pmap A -> B) : B :=
  match t with
  | PNode010 x => f PEmpty (Some x) PEmpty
  | PNode110 l x => f (PNodes l) (Some x) PEmpty
  end.
Definition Pmap_fold_aux {A B} (go : B -> Pmap_ne A -> B) (y : B) (mt : Pmap A) : B :=
  match mt with PEmpty => y | PNodes t => go y t end.
Definition Pmap_ne_fold {A B} (f : A -> B -> B) : B -> Pmap_ne A -> B :=
  fix go y t :=
    Pmap_ne_case t (fun ml mx mr => Pmap_fold_aux go
      (Pmap_fold_aux go match mx with None => y | Some x => f x y end ml) mr).
Definition Pmap_fold {A} {B} (f : A -> B -> B) := Pmap_fold_aux (Pmap_ne_fold f).

Inductive test := Test : Pmap test -> test.
Fixpoint test_size (t : test) : nat :=
  let 'Test ts := t in S (Pmap_fold (fun t' => plus (test_size t')) 0%nat ts).

End TestIntersection.
