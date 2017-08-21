

Polymorphic Fixpoint g@{i} (t : Type@{i}) (n : nat) : Type@{i} :=
  t.


Module A.
Polymorphic Fixpoint foo@{i} (t : Type@{i}) (n : nat) : Type@{i} :=
  match n with
  | 0 => t
  | S n => bar t n
  end

with bar (t : Type@{i}) (n : nat) : Type@{i} :=
    match n with
    | 0 => t
    | S n => foo t n
    end.
End A.

Module B.
Polymorphic Fixpoint foo@{i} (t : Type@{i}) (n : nat) : Type@{i} :=
  match n with
  | 0 => t
  | S n => bar t n
  end

with bar@{i} (t : Type@{i}) (n : nat) : Type@{i} :=
    match n with
    | 0 => t
    | S n => foo t n
    end.
End B.

Module C.
Fail Polymorphic Fixpoint foo@{i} (t : Type@{i}) (n : nat) : Type@{i} :=
  match n with
  | 0 => t
  | S n => bar t n
  end

with bar@{j} (t : Type@{j}) (n : nat) : Type@{j} :=
    match n with
    | 0 => t
    | S n => foo t n
    end.
End C.

Module D.
Polymorphic Fixpoint foo@{i j} (t : Type@{i}) (n : nat) : Type@{i} :=
  match n with
  | 0 => t
  | S n => bar t n
  end

with bar@{i j} (t : Type@{j}) (n : nat) : Type@{j} :=
    match n with
    | 0 => t
    | S n => foo t n
    end.
End D.

Module E.
Fail Polymorphic Fixpoint foo@{i j} (t : Type@{i}) (n : nat) : Type@{i} :=
  match n with
  | 0 => t
  | S n => bar t n
  end

with bar@{j i} (t : Type@{j}) (n : nat) : Type@{j} :=
    match n with
    | 0 => t
    | S n => foo t n
    end.
End E.

(*
Polymorphic Fixpoint g@{i} (t : Type@{i}) (n : nat) : Type@{i} :=
  t.

Print g.

Polymorphic Fixpoint a@{i} (t : Type@{i}) (n : nat) : Type@{i} :=
  t
with b@{i} (t : Type@{i}) (n : nat) : Type@{i} :=
  t.

Print a.
Print b.
*)

Polymorphic CoInductive foo@{i} (T : Type@{i}) : Type@{i} :=
| A : foo T -> foo T.

Polymorphic CoFixpoint cg@{i} (t : Type@{i}) : foo@{i} t :=
  @A@{i} t (cg t).

Print cg.

Polymorphic CoFixpoint ca@{i} (t : Type@{i}) : foo@{i} t :=
  @A@{i} t (cb t)
with cb@{i} (t : Type@{i}) : foo@{i} t :=
  @A@{i} t (ca t).

Print ca.
Print cb.
  
