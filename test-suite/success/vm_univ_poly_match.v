Set Dump Bytecode.
Set Printing Universes.
Set Printing All.

Polymorphic Class Applicative@{d c} (T : Type@{d} -> Type@{c}) :=
{ pure : forall {A : Type@{d}}, A -> T A
 ; ap : forall {A B : Type@{d}}, T (A -> B) -> T A -> T B
}.

Universes Uo Ua.

Eval compute in @pure@{Uo Ua}.

Global Instance Applicative_option : Applicative@{Uo Ua} option :=
{| pure := @Some
 ; ap := fun _ _ f x =>
           match f , x with
             | Some f , Some x => Some (f x)
             | _ , _ => None
           end
|}.

Definition foo := ap (ap (pure plus) (pure 1)) (pure 1).

Print foo.


Eval vm_compute in foo.
