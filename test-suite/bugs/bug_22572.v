(* A stuck match must not pass its reduction request to an enclosing redex
   that erases the recursive call. For the original example, evaluating the
   let definition at [Some (fun x => x)] and [0] repeats the same call. *)

Fail Fixpoint hidden_option
    (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ :=
    match b with
    | Some g => hidden_option b (g n)
    | None => 0
    end
  in 0.

(* Beta and delta erasure must not hide the same stuck-match obligation. *)
Fail Fixpoint beta_erasure
    (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  (fun _ : nat => 0)
    (match b with
     | Some g => beta_erasure b (g n)
     | None => 0
     end).

Definition ignore_nat (_ : nat) : nat := 0.

Fail Fixpoint delta_erasure
    (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  ignore_nat
    (match b with
     | Some g => delta_erasure b (g n)
     | None => 0
     end).

(* A constructor and an outer iota redex cannot hide it either. *)
Fail Fixpoint iota_erasure
    (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  match Some
    (match b with
     | Some g => iota_erasure b (g n)
     | None => 0
     end)
  with
  | Some _ => 0
  | None => 0
  end.

(* Direct non-decreasing calls remain invalid through beta wrappers. *)
Fail Fixpoint direct_call (n : nat) {struct n} : nat :=
  (fun x : nat => let _ := direct_call x in 0) n.

Fail Fixpoint identity_wrapper (n : nat) {struct n} : nat :=
  ((fun g : nat -> nat => g)
     (fun x : nat => let _ := identity_wrapper x in 0)) n.

(* Ordinary decreasing recursion remains accepted. *)
Fixpoint decreasing (n : nat) : nat :=
  match n with
  | O => O
  | S p => decreasing p
  end.

(* Beta/zeta inspection still propagates the actual smaller argument. *)
Fixpoint beta_zeta_decreasing (n : nat) : nat :=
  match n with
  | O => O
  | S p => let x := p in (fun y : nat => beta_zeta_decreasing y) x
  end.

(* A requested iota reduction that succeeds may expose a valid call. *)
Fixpoint iota_decreasing (n : nat) : nat :=
  match n with
  | O => O
  | S p => match Some p with
           | Some x => iota_decreasing x
           | None => O
           end
  end.

(* Erasing a bare recursive function value is still permitted. *)
Fixpoint erase_function_value (n : nat) : nat :=
  (fun _ : nat -> nat => O) erase_function_value.

(* Additional shapes accepted by the unpatched guard checker. None of these
   tests evaluates a divergent term; rejection is checked at declaration. *)

Fail Fixpoint pair_case (b : nat * (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := match b with (_, g) => pair_case b (g n) end in 0.

Fail Fixpoint nested_case
    (b c : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := match b with
           | Some g => nested_case b c
               (match c with Some h => g (h n) | None => g n end)
           | None => 0
           end in 0.

Definition identity_nat (x : nat) := x.
Fail Fixpoint argument_delta (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := match b with
           | Some g => argument_delta b (identity_nat (g n))
           | None => 0
           end in 0.

Fail Fixpoint local_alias (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := match b with
           | Some g => let h := g in local_alias b (h n)
           | None => 0
           end in 0.

Fail Fixpoint nested_lets (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := let _ := match b with
                         | Some g => nested_lets b (g n)
                         | None => 0
                         end in 1
  in 0.

Record result_box := { result_field : nat; extra_field : nat }.
Fail Fixpoint projection_erasure
    (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  result_field {| result_field := 0;
                  extra_field := match b with
                                 | Some g => projection_erasure b (g n)
                                 | None => 0
                                 end |}.

Definition constant_ignore (_ : nat) := 0.
Definition constant_alias := constant_ignore.
Fail Fixpoint delta_chain (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  constant_alias (match b with Some g => delta_chain b (g n) | None => 0 end).

Fail Fixpoint nested_fix (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ :=
    (fix aux (m : nat) : nat :=
       match m with
       | O => match b with Some g => nested_fix b (g n) | None => 0 end
       | S p => aux p
       end) n
  in 0.

CoInductive stream := Cons : nat -> stream -> stream.
Fail Fixpoint cofix_wrapper (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ :=
    match (cofix s : stream :=
             Cons (match b with Some g => cofix_wrapper b (g n) | None => 0 end) s)
    with Cons x _ => x end
  in 0.

Fail Fixpoint mutual_left (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := match b with Some g => mutual_right b (g n) | None => 0 end in 0
with mutual_right (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := match b with Some g => mutual_left b (g n) | None => 0 end in 0.

(* Fully applied recursive calls in types must not be hidden either. *)
Fail Fixpoint type_erasure (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := fun (_ : match b with Some g => type_erasure b (g n) = 0
                               | None => True end) => 0
  in 0.

(* Deferring checks must still allow an enclosing application to supply a
   smaller argument. These shapes failed with unconditional stuck rejection. *)
Module NestedApplication.
Fixpoint f x :=
  match x with
  | 0 => 0
  | S n => id (fix g x := f x) n
  end.
End NestedApplication.

Module ProjectedApplication.
Set Primitive Projections.
Record T := { a : nat -> nat }.
Fixpoint f (b : bool) (n : nat) {struct n} : nat :=
  match n with
  | 0 => 0
  | S n => (if b then {| a := f b |}.(a) else f b) n
  end.
End ProjectedApplication.

Module NestedInduction.
Unset Primitive Projections.
Set Depth Scheme All 2.
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.
Inductive RoseRoseTree A : Type :=
| Nleaf (a : A) : RoseRoseTree A
| Nnode (p : list (list (RoseRoseTree A))) : RoseRoseTree A.
Check RoseRoseTree_ind.
End NestedInduction.

(* Further erasure variants accepted by the unpatched checker. *)
(* Outer binder dependencies must not hide a non-decreasing call. *)
Fail Fixpoint beta_match (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  (fun x => let _ := match x with Some g => beta_match b (g n) | None => 0 end in 0) b.
Fail Fixpoint argument_let (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let x := b in let _ := match x with Some g => argument_let b (g n) | None => 0 end in 0.
Fail Fixpoint returned_callback (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := ((fun x => fun m => match x with Some g => returned_callback b (g m) | None => 0 end) b) n in 0.
Fail Fixpoint nested_betas (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  (fun x => (fun y => let _ := match x with Some g => nested_betas b (g y) | None => 0 end in 0) n) b.
Definition identity {A} (x : A) := x.
Fail Fixpoint aliased_scrutinee (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := match identity b with Some g => aliased_scrutinee b (g n) | None => 0 end in 0.
Fail Fixpoint double_case (b : option (option (nat -> nat))) (n : nat) {struct n} : nat :=
  let _ := match b with
           | Some c => match c with Some g => double_case b (g n) | None => 0 end
           | None => 0 end in 0.
Fail Fixpoint returning_case (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := (match b with Some g => fun m => returning_case b (g m) | None => fun _ => 0 end) n in 0.
Record holder := { contents : option (nat -> nat) }.
Fail Fixpoint projected_scrutinee (b : holder) (n : nat) {struct n} : nat :=
  let _ := match contents b with Some g => projected_scrutinee b (g n) | None => 0 end in 0.
Fail Fixpoint applied_nested_fix (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := (fix aux (m : nat) :=
              match m with
              | 0 => match b with Some g => applied_nested_fix b (g n) | None => 0 end
              | S p => aux p
              end) n in 0.

(* Origin: success/Fixpoint.v:192. A constructed fold argument must be
   contracted to expose its recursively smaller fields. *)
Module ConstructedFold.

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

Fixpoint hcons  (m : unit) (f : LForm) {struct f} :=
  match f with
  | LIMPL f l => fold_left (fun m f => hcons m f.(elt) ) (cons f l) m
  end.
(* The closure's term must be interpreted in its saved environment even
   when binders have since been pushed by the nested fixpoint. *)
Fixpoint hcons_alias (m : unit) (f : LForm) {struct f} : unit :=
  match f with
  | LIMPL f l =>
      let xs := cons f l in
      fold_left (fun m f => hcons_alias m f.(elt)) xs m
  end.
End ConstructedFold.
(* Constructor arguments must trigger rechecking of the nested fixpoint,
   rather than permit an enclosing let to erase its obligation.
   These three declarations were accepted by the unpatched checker. *)
Module ConstructedErasure.
Definition fold_left {A B : Type} (f : A -> B -> A) :=
  fix go (l : list B) (acc : A) {struct l} : A :=
    match l with nil => acc | cons b t => go t (f acc b) end.
Fail Fixpoint fold_erasure (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := fold_left
    (fun _ x => match x with Some g => fold_erasure b (g n) | None => 0 end)
    (cons b nil) 0 in 0.
Fail Fixpoint constructed_fix (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := (fix aux (bs : list (option (nat -> nat))) : nat :=
              match bs with
              | nil => 0
              | cons x _ => match x with Some g => constructed_fix b (g n) | None => 0 end
              end) (cons b nil) in 0.
Fail Fixpoint constructed_fix_tail (b : option (nat -> nat)) (n : nat) {struct n} : nat :=
  let _ := (fix aux (bs : list (option (nat -> nat))) : nat :=
              match bs with
              | nil => 0
              | cons x tl => let _ := match x with Some g => constructed_fix_tail b (g n) | None => 0 end in aux tl
              end) (cons b nil) in 0.
End ConstructedErasure.
