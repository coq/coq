(* -*- coq-prog-args: ("-native-compiler" "no"); -*- *)
(* Examples of use of Scheme Equality *)

Module A.
Definition N := nat.
Inductive list := nil | cons : N -> list -> list.
Scheme Equality for list.
End A.

Module B.
  Section A.
    Context A (eq_A:A->A->bool)
            (A_bl : forall x y, eq_A x y = true -> x = y)
            (A_lb : forall x y, x = y -> eq_A x y = true).
    Inductive I := C : A -> I.
    Scheme Equality for I.
  End A.
End B.

Module C.
  Parameter A : Type.
  Parameter eq_A : A->A->bool.
  Parameter A_bl : forall x y, eq_A x y = true -> x = y.
  Parameter A_lb : forall x y, x = y -> eq_A x y = true.
  #[export] Hint Resolve A_bl A_lb : core.
  Inductive I := C : A -> I.
  Scheme Equality for I.
  Inductive J := D : list A -> J.
  Scheme Equality for J.
End C.

(* Universe polymorphism *)
Module D.
  Set Universe Polymorphism.
  Inductive unit := tt.
  Scheme Equality for unit.

  Inductive prod (A B:Type) := pair : A -> B -> prod A B.
  Scheme Equality for prod.

  (* With an indirection *)
  Inductive box A := c : A -> box A.
  Inductive prodbox (A B:Type) := pairbox : box A -> box B -> prodbox A B.
  Scheme Equality for prodbox.
  Check eq_refl : prodbox_beq @{Set Set} =
    fun (A B : Type@{Set}) eq_A eq_B (X Y : prodbox A B) =>
      match X, Y with
      | pairbox _ _ x x0, pairbox _ _ x1 x2 =>
              (internal_box_beq A eq_A x x1 &&
               internal_box_beq B eq_B x0 x2)%bool
      end.
End D.

(* With hidden "X" and "Y" (was formerly cause of collisions) *)
Module E.
  Section S.
  Variables X Y : Type.
  Variable eq_X : X -> X -> bool.
  Variable eq_Y : Y -> Y -> bool.
  Inductive EI := EC : X -> Y -> EI.
  Scheme Boolean Equality for EI.
  End S.
End E.

(* With inductive parameters instantiated by non-variable types *)
Module F.
  Inductive FI := FC : list nat -> FI.
  Scheme Boolean Equality for FI.

  Inductive tree := node : list tree -> tree.
  Scheme Boolean Equality for tree.

  Inductive rose A := Leaf : A -> rose A | Node : list (rose A) -> rose A.
  Scheme Boolean Equality for rose.
  Print rose_beq.
  Check eq_refl : rose_beq =
    fun (A : Type) (eq_A : A -> A -> bool) =>
    fix rose_eqrec (X Y : rose A) {struct X} : bool :=
      match X with
      | Leaf _ x => match Y with
                    | Leaf _ x0 => eq_A x x0
                    | Node _ _ => false
                    end
      | Node _ x =>
          match Y with
          | Leaf _ _ => false
          | Node _ x0 => C.internal_list_beq (rose A) rose_eqrec x x0
          end
      end.
End F.

(* With higher-order parameters and non-Type parameters *)
Module G.
  Inductive GI (F:Type->Type) A := GC : F A -> F nat -> GI F A.
  Scheme Boolean Equality for GI.

  Inductive GJ (F:nat->(nat->Type->Type)->Type) (f:nat->nat) (n:nat) (A:nat->Type->Type) :=
     GD : F 0 (fun n => list) -> F 1 A -> GJ F f n A.
  Scheme Boolean Equality for GJ.
End G.

(* With local definitions in constructors *)
Module H.
  Inductive HJ A : Type := HD : let a := 0 in nat -> list A -> HJ A.
  Scheme Boolean Equality for HJ.
End H.

(* With recursively non-uniform arguments *)
Module I.
  Inductive T A := C : A -> T (option A) -> T A.
  Scheme Boolean Equality for T.
  Check eq_refl : T_beq =
    fix T_eqrec
    (A : Type) (eq_A : A -> A -> bool)
    (X Y : T A) {struct X} : bool :=
      match X, Y with
      | C _ x x0, C _ x1 x2 =>
              (eq_A x x1 &&
               T_eqrec (option A)
                 (internal_option_beq A eq_A) x0 x2)%bool
      end.
End I.

(* With mutual definitions *)
Module J.
  Inductive tree A := node : forest A -> tree A
  with forest A := nil : forest A | cons : A -> tree A -> forest A.
  Scheme Boolean Equality for tree.

  Inductive K (F:nat->(nat->Type->Type)->Type) (A:nat->Type->Type) :=
     D : L F A -> F 1 A -> K F A
  with L (F:nat->(nat->Type->Type)->Type) (A:nat->Type->Type) :=
     E : F 0 (fun n => list) -> K F A -> L F A.
  Scheme Boolean Equality for K.
End J.

(* With "match" or "fix" *)
Module K.
  Inductive K1 (b:bool) (F : if b then Type else Type->Type) : Type :=
  C1 : nat -> K1 b F.
  Scheme Boolean Equality for K1.

  Inductive K2 (b:bool) (F : if b then Type else Type->Type) : Type :=
  C2 : (if b return (if b then Type else Type->Type) -> Type
        then fun A => A else fun F => F nat) F ->
       K2 b F.
  Scheme Boolean Equality for K2.

  (* Almost work *)
  Inductive K3 (n:nat) (A : Type) : Type :=
   C3 : (fix mkprod n := match n with 0 => A | S n => (mkprod n * A)%type end) n ->
       K3 n A.
  Fail Scheme Boolean Equality for K3.
End K.

Require PrimInt63 PrimFloat.

Module ElpiTestSuite.

Inductive empty := .
Scheme Equality for empty.

Inductive unit := tt.
Scheme Equality for unit.

Inductive peano := Zero | Succ (n : peano).
Scheme Equality for peano.

Inductive option A := None | Some (_ : A).
Scheme Equality for option.

Inductive pair A B := Comma (a : A) (b : B).
Scheme Equality for pair.

Inductive seq A := Nil | Cons (x : A) (xs : seq A).
Scheme Equality for seq.

Inductive nest A := NilN | ConsN (x : A) (xs : nest (pair A A)).
Scheme Boolean Equality for nest.

Inductive zeta Sender (Receiver := Sender) := Envelope (a : Sender) (ReplyTo := a) (c : Receiver).
Scheme Boolean Equality for zeta.

Inductive beta (A : (fun x : Type => x) Type) := Redex (a : (fun x : Type => x) A).
Scheme Boolean Equality for beta.

Inductive large :=
| K1 (_ : bool)
| K2 (_ : bool) (_ : bool)
| K3 (_ : bool) (_ : bool) (_ : bool)
| K4 (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K5 (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K6 (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K7 (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K8 (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K9 (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K10(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K11(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K12(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K13(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K14(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K15(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K16(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K17(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K18(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K19(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K20(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K21(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K22(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K23(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K24(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K25(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool)
| K26(_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool) (_ : bool).
Scheme Equality for large.

Inductive prim_int := PI (i : PrimInt63.int).
Scheme Boolean Equality for prim_int.

Inductive prim_float := PF (f : PrimFloat.float).
Scheme Boolean Equality for prim_float.

Record fo_record := { f1 : peano; f2 : bool; }.
Scheme Equality for fo_record.

Record pa_record A := { f3 : peano; f4 : A; }.
Scheme Equality for pa_record.

Set Primitive Projections.
Record pr_record A := { pf3 : peano; pf4 : A; }.
Unset Primitive Projections.
Scheme Boolean Equality for pr_record.

Variant enum := E1 | E2 | E3.
Scheme Equality for enum.

End ElpiTestSuite.

(* Ignoring SProp/Prop subterms *)
Module L.
  Inductive seq {A} (x:A) : A -> SProp := seq_refl : seq x x.
  Inductive A := C : forall n, seq n 0 -> A.
  Scheme Boolean Equality for A.
  Check eq_refl : A_beq =
    fun (X Y : A) =>
      match X, Y with
      | C n _, C n0 _ => A.internal_nat_beq n n0
      end.
End L.
