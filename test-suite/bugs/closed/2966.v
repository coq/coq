(** Non-termination and state monad with extraction *)
Require Import List.

Set Implicit Arguments.
Set Asymmetric Patterns.

Module MemSig.
  Definition t: Type := list Type.
  
  Definition Nth (sig: t) (n: nat) :=
    nth n sig unit.
End MemSig.

(** A memory of type [Mem.t s] is the union of cells whose type is specified
    by [s]. *)
Module Mem.
  Inductive t: MemSig.t -> Type :=
  | Nil: t nil
  | Cons: forall (T: Type), option T -> forall (sig: MemSig.t), t sig ->
    t (T :: sig).
End Mem.

Module Ref.
  Inductive t (sig: MemSig.t) (T: Type): Type :=
  | Input: t sig T.
  
  Definition Read (sig: MemSig.t) (T: Type) (ref: t sig T) (s: Mem.t sig)
    : option T :=
    match ref with
    | Input => None
    end.
End Ref.

Module Monad.
  Definition t (sig: MemSig.t) (A: Type) :=
    Mem.t sig -> option A * Mem.t sig.
  
  Definition Return (sig: MemSig.t) (A: Type) (x: A): t sig A :=
    fun s =>
      (Some x, s).
  
  Definition Bind (sig: MemSig.t) (A B: Type) (x: t sig A) (f: A -> t sig B)
    : t sig B :=
    fun s =>
    match x s with
    | (Some x', s') => f x' s'
    | (None, s') => (None, s')
    end.

  Definition Select (T: Type) (f g: unit -> T): T :=
    f tt.
  
  (** Read in a reference. *)
  Definition Read (sig: MemSig.t) (T: Type) (ref: Ref.t sig T)
    : t sig T :=
    fun s =>
      match Ref.Read ref s with
      | None => (None, s)
      | Some x => (Some x, s)
      end.
End Monad.

Import Monad.

Definition pop (sig: MemSig.t) (T: Type) (trace: Ref.t sig (list T))
  : Monad.t sig T :=
  Bind (Read trace) (fun _ s => (None, s)).

Definition sig: MemSig.t := (list nat: Type) :: nil.

Definition trace: Ref.t sig (list nat).
Admitted.

Definition Gre (sig: MemSig.t) (trace: _)
    (f: bool -> bool): Monad.t sig nat :=
    Select (fun _ => pop trace) (fun _ => Return 0).

Definition Arg :=
  Gre trace (fun _ => false).
