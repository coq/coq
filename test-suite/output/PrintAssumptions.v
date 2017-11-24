
(** Print Assumption and opaque modules :

  Print Assumption used to consider as axioms the modular fields
  unexported by their signature, cf bug report #2186. This should
  now be fixed, let's test this here. *)

(* First, a minimal test-case *)

Axiom foo : nat.

Module Type T.
 Parameter bar : nat.
End T.

Module M : T.
  Module Hide. (* An entire sub-module could be hidden *)
  Definition x := foo.
  End Hide.
  Definition bar := Hide.x.
End M.

Module N (X:T) : T.
  Definition y := X.bar. (* A non-exported field *)
  Definition bar := y.
End N.

Module P := N M.

Print Assumptions M.bar. (* Should answer: foo *)
Print Assumptions P.bar. (* Should answer: foo *)


(* The original test-case of the bug-report *)

Require Import Arith.

Axiom extensionality : forall P Q (f g:P -> Q),
  (forall x, f x = g x) -> f = g.

Module Type ADD_COMM_EXT.
  Axiom add_comm_ext : forall n, (fun x => x + n) = (fun x => n + x).
End ADD_COMM_EXT.

Module AddCommExt_Opaque : ADD_COMM_EXT.
  Lemma add_comm_ext : forall n, (fun x => x + n) = (fun x => n + x).
  Proof.
    intro n; apply extensionality; auto with arith.
  Qed.
End AddCommExt_Opaque.

Module AddCommExt_Transparent <: ADD_COMM_EXT.
  Lemma add_comm_ext : forall n, (fun x => x + n) = (fun x => n + x).
  Proof.
    intro n; apply extensionality; auto with arith.
  Qed.
End AddCommExt_Transparent.

Print Assumptions AddCommExt_Opaque.add_comm_ext.
(* Should answer: extensionality *)

Print Assumptions AddCommExt_Transparent.add_comm_ext.
(* Should answer: extensionality *)

Lemma add1_comm_ext_opaque :
  (fun x => x + 1) = (fun x => 1 + x).
Proof. exact (AddCommExt_Opaque.add_comm_ext 1). Qed.

Lemma add1_comm_ext_transparent :
  (fun x => x + 1) = (fun x => 1 + x).
Proof. exact (AddCommExt_Transparent.add_comm_ext 1). Qed.

Print Assumptions add1_comm_ext_opaque.
(* Should answer: extensionality *)

Print Assumptions add1_comm_ext_transparent.
(* Should answer: extensionality *)

Module Type FALSE_POSITIVE.
  Axiom add_comm : forall n x, x + n = n + x.
End FALSE_POSITIVE.

Module false_positive : FALSE_POSITIVE.
  Lemma add_comm : forall n x, x + n = n + x.
  Proof. auto with arith. Qed.

  Print Assumptions add_comm.
  (* Should answer : Closed under the global context *)
End false_positive.

Lemma comm_plus5 : forall x,
  x + 5 = 5 + x.
Proof. exact (false_positive.add_comm 5). Qed.

Print Assumptions comm_plus5.
(* Should answer : Closed under the global context *)

(** Print Assumption and Include *)

Module INCLUDE.

Module M.
Axiom foo : False.
End M.

Module N.
Include M.
End N.

Print Assumptions N.foo.

End INCLUDE.
