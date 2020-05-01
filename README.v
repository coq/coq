(** Practical Sized Typing for Coq

(Commands below are enclosed within backticks.)

You will need your environment set up to build Coq. Instructions are provided
in the Coq repository, but they are generally as follows (for Ubuntu):
  1. `sudo apt install opam` (OCaml package manager)
  2. `opam init && opam switch create ocaml-base-compiler` (OCaml compiler)
  3. `opam install num ocamlfind` (OCaml libraries needed for compilation)

To build the Coq toplevel (REPL):
  1. `./configure -profile devel` (N.B. this turns warnings into errors)
  2. `make coqbinaries` (for native code) or `make byte` (for bytecode; faster)
  3. `make COQUSERFLAGS="-set 'Sized Typing'" coqlib` (libraries; slow)
    Note that currently (as of 18 October 2019), not all Coq libraries are able
    to be compiled. Allow the compilation to proceed as far as it can. To
    compile specific libraries, run `make <path>.vo`. For instance, the Strings
    library can be built using `make theories/Strings/String.vo`.
  4. `bin/coqtop` (if native code) or `bin/coqtop.byte` (if bytecode)

In the toplevel, before running any Coq code, first turn off guard checking
using
  `Unset Guard Checking.`
then turn on sized typing using
  `Set Sized Typing.`
Flags can be printed using
  `Print Typing Flags.`
Example programs can be found in coq/test-suite/success/sized_typing.v.
We have included programs mentioned in the paper below.
*)

Unset Guard Checking.
Set Sized Typing.

(* Coinductives *)

CoInductive Stream (A : Type) :=
  Cons : A -> Stream A -> Stream A.

CoFixpoint const A a : Stream A := Cons A a (const A a).

(* Arithmetic *)
Fixpoint add n m : nat :=
  match n with
  | O => m
  | S p => S (add p m)
  end.


Fixpoint minus n m :=
  match n, m with
  | O, _ => n
  | _, O => n
  | S n', S m' =>
    minus n' m'
  end.

Fixpoint div n m :=
  match n with
  | O => O
  | S n' => S (div (minus n' m) m)
  end.

(* Quicksort *)

Fixpoint leb n m :=
  match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
  end.

Fixpoint filter T (f: T -> bool) (l: list T) :=
  match l with
  | nil => nil
  | cons x l' =>
    if (f x) then
      cons x (filter T f l')
    else
      filter T f l'
  end.

Fixpoint append T (l1 l2: list T) :=
  match l1 with
  | nil => l2
  | cons x l => cons x (append T l l2)
  end.

Fixpoint quicksort l :=
  match l with
  | nil => nil
  | cons hd tl => append nat
    (quicksort (filter nat (fun x => (leb x hd)) tl))
    (cons hd (quicksort (filter nat (fun x => negb (leb x hd)) tl)))
  end.

(* GCD *)

Fixpoint divmod x y q u :=
  match x with
    | 0 => (q,u)
    | S x' =>
      match u with
      | 0 => divmod x' y (S q) y
      | S u' => divmod x' y q u'
      end
  end.

Definition div' x y :=
  match y with
    | 0 => y
    | S y' => fst (divmod x y' 0 y')
  end.

Definition modulo x y :=
  match y with
    | 0 => y
    | S y' => y' - snd (divmod x y' 0 y')
  end.

Infix "/" := div' : nat_scope.
Infix "mod" := modulo (at level 40, no associativity) : nat_scope.

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

(* The following is a model of capture-avoiding substitution
  in simply-typed lambda calculus.
  You will need to run `make theories/Strings/String.vo` first. *)

Require Import Strings.String.

Module stlc.

Parameter names: list string.
Parameter fresh: True -> string.

Inductive STLCA: Type :=
  | unit: STLCA
  | arr (A b: STLCA): STLCA.

Inductive STLCE: Type :=
  | vare (v: string): STLCE
  | lambdae (v: string) (A: STLCA) (body: STLCE): STLCE
  | appe (e1: STLCE) (e2: STLCE): STLCE.

Fixpoint size (e: STLCE): nat :=
  match e with
  | vare _ => 1
  | lambdae _ _ body => 1 + (size body)
  | appe e1 e2 => 1 + (size e1) + (size e2)
  end.

(* We assume [new] to be unbound in e. *)
Fixpoint freshen (old: string) (new: string) (e: STLCE) :=
  match e with
  | vare n => if (n =? old)%string then vare new else e
  | appe e1 e2 => appe (freshen old new e1) (freshen old new e2)
  | lambdae n A body => lambdae n A (freshen old new body)
  end.

Fixpoint subst (name: string) (v: STLCE) (exp: STLCE) {struct exp} :=
  match exp with
  | vare n => if (n =? name)%string then v else exp
  | appe e1 e2 => appe (subst name v e1) (subst name v e2)
  | lambdae n A body =>
    if (n =? name)%string then exp else
    let n' := fresh I in
    lambdae n' A (subst name v (freshen n n' body))
  end.

End stlc.
