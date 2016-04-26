(* Checking use of retyping in w_unify0 in the presence of unification
problems of the form \x:Meta.Meta = \x:ind.match x with ... end *)

Require Import List.
Require Import QArith.
Require Import Qcanon.

Set Implicit Arguments.

Inductive dynamic : Type :=
  | Dyn : forall T, T -> dynamic.

Definition perm := Qc.

Locate Qle_bool.

Definition compatibleb (p1 p2 : perm) : bool :=
let p1pos := Qle_bool 0 p1 in
  let p2pos := Qle_bool 0 p2 in
    negb (
         (p1pos && p2pos)
      || ((p1pos || p2pos) && (negb (Qle_bool 0 ((p1 + p2)%Qc)))))%Qc.

Definition compatible (p1 p2 : perm) := compatibleb p1 p2 = true.

Definition perm_plus (p1 p2 : perm) : option perm :=
  if compatibleb p1 p2 then Some (p1 + p2) else None.

Infix "+p" := perm_plus (at level 60, no associativity).

Axiom axiom_ptr : Set.

Definition ptr := axiom_ptr.

Axiom axiom_ptr_eq_dec : forall (a b : ptr), {a = b} + {a <> b}.

Definition ptr_eq_dec := axiom_ptr_eq_dec.

Definition hval := (dynamic * perm)%type.

Definition heap := ptr -> option hval.

Bind Scope heap_scope with heap.
Delimit Scope heap_scope with heap.
Local Open Scope heap_scope.

Definition read (h : heap) (p : ptr) : option hval := h p.

Notation "a # b" := (read a b) (at level 55, no associativity) : heap_scope.

Definition val (v:hval) := fst v.
Definition frac (v:hval) := snd v.

Definition hval_plus (v1 v2 : hval) : option hval :=
  match (frac v1) +p (frac v2) with
    | None => None
    | Some v1v2 => Some (val v1, v1v2)
  end.

Definition hvalo_plus (v1 v2 : option hval) :=
  match v1 with
    | None => v2
    | Some v1' =>
      match v2 with
        | None => v1
        | Some v2' => (hval_plus v1' v2')
      end
  end.

Notation "v1 +o v2" := (hvalo_plus v1 v2) (at level 60, no associativity) : heap_scope.

Definition join (h1 h2 : heap) : heap :=
  (fun p => (h1 p) +o (h2 p)).

Infix "*" := join (at level 40, left associativity) : heap_scope.

Definition hprop := heap -> Prop.

Bind Scope hprop_scope with hprop.
Delimit Scope hprop_scope with hprop.

Definition hprop_cell (p : ptr) T (v : T) (pi:Qc): hprop := fun h =>
  h#p = Some (Dyn v, pi) /\ forall p', p' <> p -> h#p' = None.

Notation "p ---> v" := (hprop_cell p v (0%Qc)) (at level 38, no associativity) : hprop_scope.

Definition empty : heap := fun _ => None.

Definition hprop_empty : hprop := eq empty.
Notation "'emp'" := hprop_empty : hprop_scope.

Definition hprop_inj (P : Prop) : hprop := fun h => h = empty /\ P.
Notation "[ P ]" := (hprop_inj P) (at level 0, P at level 200) : hprop_scope.

Definition hprop_imp (p1 p2 : hprop) : Prop := forall h, p1 h -> p2 h.
Infix "==>" := hprop_imp (right associativity, at level 55).

Definition hprop_ex T (p : T -> hprop) : hprop := fun h => exists v, p v h.
Notation "'Exists' v :@ T , p" := (hprop_ex (fun v : T => p%hprop))
  (at level 90, T at next level) : hprop_scope.

Local Open Scope hprop_scope.
Definition disjoint (h1 h2 : heap) : Prop :=
  forall p,
    match h1#p with
      | None => True
      | Some v1 => match h2#p with
                     | None => True
                     | Some v2 => val v1 = val v2
                               /\ compatible (frac v1) (frac v2)
                  end
    end.

Infix "<#>" := disjoint (at level 40, no associativity) : heap_scope.

Definition split (h h1 h2 : heap) : Prop := h1 <#> h2 /\ h = h1 * h2.

Notation "h ~> h1 * h2" := (split h h1 h2) (at level 40, h1 at next level, no associativity).

Definition hprop_sep (p1 p2 : hprop) : hprop := fun h =>
  exists h1, exists h2, h ~> h1 * h2
    /\ p1 h1
    /\ p2 h2.
Infix "*" := hprop_sep (at level 40, left associativity) : hprop_scope.

Section Stack.
  Variable T : Set.

  Record node : Set := Node {
    data : T;
    next : option ptr
  }.

  Fixpoint listRep (ls : list T) (hd : option ptr) {struct ls} : hprop :=
    match ls with
    | nil => [hd = None]
    | h :: t =>
      match hd with
      | None => [False]
      | Some hd' => Exists p :@ option ptr, hd' ---> Node h p * listRep t p
      end
    end%hprop.

  Definition stack := ptr.

  Definition rep q ls := (Exists po :@ option ptr, q ---> po * listRep ls po)%hprop.

  Definition isExistential T (x : T) := True.

  Theorem himp_ex_conc_trivial : forall T p p1 p2,
    p ==> p1 * p2
    -> T
    -> p ==> hprop_ex (fun _ : T => p1) * p2.
  Admitted.

  Goal forall (s : ptr) (x : T) (nd : ptr) (v : unit) (x0 : list T) (v0 : option ptr)
              (H0 : isExistential v0),
  nd ---> {| data := x; next := v0 |} * (s ---> Some nd * listRep x0 v0) ==>
  (Exists po :@ option ptr,
    s ---> po *
    match po with
    | Some hd' =>
        Exists p :@ option ptr,
        hd' ---> {| data := x; next := p |} * listRep x0 p
    | None => [False]
    end) * emp.
  Proof.
    intros. 
    try apply himp_ex_conc_trivial.
