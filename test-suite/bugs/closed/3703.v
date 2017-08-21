Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 6746 lines to 4190 lines, then from 29 lines to 18 lines, then fro\
m 30 lines to 19 lines *)
(* coqc version trunk (October 2014) compiled on Oct 7 2014 12:42:41 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (2313bde0116a5916912bebbaca77d291f7b2760a) *)
Record PreCategory := { identity : forall x, x -> x }.
Definition set_cat : PreCategory := @Build_PreCategory (fun T x => x).
Module UnKeyed.
  Global Unset Keyed Unification.
  Goal forall (T : Type) (g0 g1 : T) (k : T) (H' : forall x : T, k = @identity set_cat T x),
         ((fun x : T => x) g0) = ((fun x : T => x) g1).
    intros T g0 g1 k H'.
    change (identity _ _) with (fun y : T => y) in H';
      rewrite <- H' || fail "too early".
    Undo.
    rewrite <- H'.
    admit.
  Defined.
End UnKeyed.
Module Keyed.
  Global Set Keyed Unification.
  Declare Equivalent Keys (fun x => _) identity.
  Goal forall (T : Type) (g0 g1 : T) (k : T) (H' : forall x : T, k = @identity set_cat T x),
         ((fun x : T => x) g0) = ((fun x : T => x) g1).
    intros T g0 g1 k H'.
    change (identity _ _) with (fun y : T => y) in H';
      rewrite <- H' || fail "too early".
    Undo.
    rewrite <- H'.
    admit.
  Defined.
End Keyed.
