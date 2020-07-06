(** Practical Sized Typing for Coq

You will need your environment set up to build Coq. Instructions are provided
in the Coq repository, but they are generally as follows:
  1. `sudo apt install opam` (OCaml package manager) (for Ubuntu)
  2. `opam init && opam switch create ocaml-base-compiler` (OCaml compiler)
  3. `opam install num ocamlfind` (OCaml libraries needed for compilation)

To build the Coq toplevel locally (REPL):
  1. `./configure -local` (N.B. this turns warnings into errors)
  2. `make coqbinaries` (for native code) or `make byte` (for bytecode)
  3. `make coqlib` (stdlib) or `make theories/Init/Prelude.vo` (core library)
  4. `bin/coqtop` (if native code) or `bin/coqtop.byte` (if bytecode)

The `Guard Checking` flag toggles the existing guard-predicate-based checking,
while the `Sized Typing` flag toggles our new CIC^* size inference/checking.

More example programs can be found in coq/test-suite/success/sized_typing.v.
Programs mentioned in the paper are included below. *)

Unset Guard Checking.
Set Sized Typing.

(** Coinductives *)

CoInductive Stream (A : Type) :=
  Cons : A -> Stream A -> Stream A.

CoFixpoint const A a : Stream A := Cons A a (const A a).

(** Arithmetic *)

Reserved Infix "+" (at level 50, left associativity).
Reserved Infix "-" (at level 50, left associativity).
Reserved Infix "/" (at level 40, left associativity).

Fixpoint plus n m : nat :=
  match n with
  | O => m
  | S p => S (plus p m)
  end
where "n + m" := (plus n m).

Fixpoint minus n m :=
  match n, m with
  | O, _ => n
  | _, O => n
  | S n', S m' =>
    minus n' m'
  end
where "n - m" := (minus n m).

Fixpoint div n m :=
  match n with
  | O => O
  | S n' => S (div (minus n' m) m)
  end
where "n / m" := (div n m).

(** Quicksort *)

Fixpoint leb n m :=
  match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
  end.

Definition gtb n m :=
  negb (leb n m).

Fixpoint filter {T} (p: T -> bool) (l: list T) :=
  match l with
  | nil => nil
  | cons hd tl =>
    if (p hd) then
      cons hd (filter p tl)
    else
      filter p tl
  end.

Fixpoint append {T} (l1 l2: list T) :=
  match l1 with
  | nil => l2
  | cons hd tl =>
    cons hd (append tl l2)
  end.

Fixpoint quicksort (l: list nat) :=
  match l with
  | nil => nil
  | cons hd tl => append
    (quicksort (filter (gtb hd) tl))
    (cons hd (quicksort (filter (leb hd) tl)))
  end.

(** GCD
  These are lifted directly from Nat in the standard library. *)

Fixpoint divmod x y q u :=
  match x with
  | 0 => (q, u)
  | S x' =>
    match u with
    | 0 => divmod x' y (S q) y
    | S u' => divmod x' y q u'
    end
  end.

Definition modulo x y :=
  match y with
    | 0 => y
    | S y' => y' - snd (divmod x y' 0 y')
  end.

Infix "mod" := modulo (at level 40, no associativity).

Fail Fixpoint gcd a b :=
  match a with
  | O => b
  | S a' => gcd (b mod (S a')) (S a')
  end.

Set Guard Checking.

Fixpoint gcd a b :=
  match a with
  | O => b
  | S a' => gcd (b mod (S a')) (S a')
  end.

Unset Guard Checking.

(** STLC
  A model of capture-avoiding substitution in simply-typed lambda calculus.
  You may need to run `make theories/Strings/String.vo` first.

  Notice that `freshen` is size-preserving, which is why it can be used in
  the recursive argument of `subst`, but `subst` itself is not size-preserving,
  since `val` may be a "larger" term than `exp`. *)

Require Import Strings.String.

Module stlc.

Parameter names: list string.
Parameter fresh: True -> string.

Inductive Typ: Type :=
  | unit: Typ
  | arr (T U: Typ): Typ.

Inductive Exp: Type :=
  | var (x: string): Exp
  | lam (x: string) (T: Typ) (body: Exp): Exp
  | app (e1: Exp) (e2: Exp): Exp.

(* freshen : string^∞ → string^∞ → Exp^ι → Exp^ι *)
Fixpoint freshen (old: string) (new: string) (e: Exp) :=
  match e with
  | var x => if (x =? old)%string then var new else e
  | app e1 e2 => app (freshen old new e1) (freshen old new e2)
  | lam x T body => lam x T (freshen old new body)
  end.

(* subst : string^∞ → Exp^∞ → Exp^ι → Exp^∞ *)
Fixpoint subst (name: string) (val exp: Exp) {struct exp} :=
  match exp with
  | var x => if (x =? name)%string then val else exp
  | app e1 e2 => app (subst name val e1) (subst name val e2)
  | lam x T body =>
    if (x =? name)%string then exp else
    let y := fresh I in
    lam y T (subst name val (freshen x y body))
  end.

End stlc.
