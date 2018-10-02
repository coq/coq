Universes a b c ω ω'.
Definition Typeω := Type@{ω}.
Definition Type2 : Typeω := Type@{c}.
Definition Type1 : Type2 := Type@{b}.
Definition Type0 : Type1 := Type@{a}.

Set Universe Polymorphism.
Set Printing Universes.

Definition Typei' (n : nat)
  := match n return Type@{ω'} with
     | 0 => Type0
     | 1 => Type1
     | 2 => Type2
     | _ => Typeω
     end.
Definition TypeOfTypei' {n} (x : Typei' n) : Type@{ω'}
  := match n return Typei' n -> Type@{ω'} with
     | 0 | 1 | 2 | _ => fun x => x
     end x.
Definition Typei (n : nat) : Typei' (S n)
  := match n return Typei' (S n) with
     | 0 => Type0
     | 1 => Type1
     | _ => Type2
     end.
Definition TypeOfTypei {n} (x : TypeOfTypei' (Typei n)) : Type@{ω'}
  := match n return TypeOfTypei' (Typei n) -> Type@{ω'} with
     | 0 | 1 | _ => fun x => x
     end x.
Check Typei 0 : Typei 1.
Check Typei 1 : Typei 2.

Definition lift' {n} : TypeOfTypei' (Typei n) -> TypeOfTypei' (Typei (S n))
  := match n return TypeOfTypei' (Typei n) -> TypeOfTypei' (Typei (S n)) with
     | 0 | 1 | 2 | _ => fun x => (x : Type)
     end.
Definition lift'' {n} : TypeOfTypei' (Typei n) -> TypeOfTypei' (Typei (S n))
  := match n return TypeOfTypei' (Typei n) -> TypeOfTypei' (Typei (S n)) with
     | 0 | 1 | 2 | _ => fun x => x
     end. (* The command has indeed failed with message:
In environment
n : nat
x : TypeOfTypei' (Typei 0)
The term "x" has type "TypeOfTypei' (Typei 0)" while it is expected to have type
 "TypeOfTypei' (Typei 1)" (universe inconsistency: Cannot enforce b = a because  a < b).
 *)
Check (fun x : TypeOfTypei' (Typei 0) => TypeOfTypei' (Typei 1)).

Definition lift''' {n} : TypeOfTypei' (Typei n) -> TypeOfTypei' (Typei (S n)).
  refine match n return TypeOfTypei' (Typei n) -> TypeOfTypei' (Typei (S n))  with
         | 0 | 1 | 2 | _ => fun x => _
         end.
  exact x.
  Undo.
  (* The command has indeed failed with message:
In environment
n : nat
x : TypeOfTypei' (Typei 0)
The term "x" has type "TypeOfTypei' (Typei 0)" while it is expected to have type
 "TypeOfTypei' (Typei 1)" (universe inconsistency: Cannot enforce b = a because  a < b).
 *)
  all:compute in *.
  all:exact x.
