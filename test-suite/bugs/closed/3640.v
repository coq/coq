(* File reduced by coq-bug-finder from original input, then from 14990 lines to 70 lines, then from 44 lines to 29 lines *)
(* coqc version trunk (September 2014) compiled on Sep 17 2014 0:22:30 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (d34e1eed232c84590ddb80d70db9f7f7cf13584a) *)
Set Primitive Projections.
Set Implicit Arguments.
Record sigT {A} P := existT { pr1 : A ; pr2 : P pr1 }.
Notation "{ x : A & P }" := (sigT (A := A) (fun x : A => P)) : type_scope.
Notation "x .1" := (pr1 x) (at level 3, format "x '.1'").
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'").
Record Equiv A B := { equiv_fun :> A -> B }.
Notation "A <~> B" := (Equiv A B) (at level 85).
Inductive Bool : Type := true | false.
Definition negb (b : Bool) := if b then false else true.
Axiom eval_bool_isequiv : forall (f : Bool -> Bool), f false = negb (f true).
Lemma bool_map_equiv_not_idmap (f : { f : Bool <~> Bool & ~(forall x, f x = x) })
: forall b, ~(f.1 b = b).
Proof.
  intro b.
  intro H''.
  apply f.2.
  intro b'.
  pose proof (eval_bool_isequiv f.1) as H.
  destruct b', b.
  Fail match type of H with
    | _ = negb (f.1 true) => fail 1 "no f.1 true"
  end. (* Error: No matching clauses for match. *)
  destruct (f.1 true).
  simpl in *.
  Fail match type of H with
    | _ = negb ?T => unify T (f.1 true); fail 1 "still has f.1 true"
  end. (* Error: Tactic failure: still has f.1 true. *)
