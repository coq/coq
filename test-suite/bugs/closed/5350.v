(* Error: Tactic failure: Not equal. *)



(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "." "Fscq" "-top" "Pred") -*- *)
(* File reduced by coq-bug-finder from original input, then from 2710 lines to 
84 lines, then from 308 lines to 89 lines, then from 103 lines to 99 lines *)
(* coqc version trunk (February 2017) compiled on Feb 9 2017 9:47:18 with OCaml 
4.04.0
   coqtop version cauchy.local:/Users/tchajed/code/sw/coq,ltac-missing-args-msg 
(2c7df345aead8d44a835e609caa41e348bfb021c) *)
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.

Set Universe Polymorphism.
Set Implicit Arguments.

Definition EqDec (T : Type) := forall (a b : T), {a = b} + {a <> b}.

Definition mem {A : Type} {AEQ : EqDec A} {V : Type} := A -> option V.

Section GenPredDef.

Variable AT : Type.
Variable AEQ : EqDec AT.
Variable V : Type.

Definition pred := @mem AT AEQ V -> Prop.

Definition mem_union (m1 m2 : @mem AT AEQ V) : (@mem AT AEQ V) := fun a =>
  match m1 a with
  | Some v => Some v
  | None => m2 a
  end.

Definition sep_star_impl (p1: pred) (p2: pred) : pred :=
  fun m => exists m1 m2, m = mem_union m1 m2 /\ p1 m1 /\ p2 m2.

Definition mem_except (m: @mem AT AEQ V) (a: AT) : @mem AT AEQ V :=
  fun a' => if AEQ a' a then None else m a'.

End GenPredDef.

Module Type SEP_STAR.
  Unset Universe Polymorphism.
  Parameter sep_star : forall {AT:Type} {AEQ:EqDec AT} {V:Type}, @pred AT AEQ V 
-> @pred AT AEQ V -> @pred AT AEQ V.
  Axiom sep_star_is : @sep_star = @sep_star_impl.
End SEP_STAR.

Module Sep_Star : SEP_STAR.
  Unset Universe Polymorphism.
  Definition sep_star := @sep_star_impl.
  Theorem sep_star_is : @sep_star = @sep_star_impl.
    reflexivity.
  Qed.
End Sep_Star.

Definition sep_star := @Sep_Star.sep_star.

Ltac unfold_sep_star :=
  unfold sep_star; rewrite Sep_Star.sep_star_is; unfold sep_star_impl.

Section GenPredThm.

Variable AT : Type.
Variable AEQ : EqDec AT.

Theorem ptsto_mem_except : forall (V : Type) (F : pred AEQ V) (a : AT) (m1 m2 : 
mem),
    F m1 /\ F m2 -> F (mem_except (mem_union m1 m2) a).
Proof.
  intros.
  (* this works *)
  let k := constr:(mem_except (mem_union m1 m2) a) in
  match goal with
  | [ |- F ?x ] => unify x k; constr_eq x k
  end.
Admitted.

Theorem ptsto_mem_except' : forall V F a (m : @mem AT AEQ V),
  (sep_star (AEQ:=AEQ) F F) m -> F (mem_except m a).
Proof.
  unfold_sep_star.
  intros.
  destruct H as [m1 H].
  destruct H as [m2 H].
  destruct H.
  subst.

  let k := constr:(mem_except (mem_union m1 m2) a) in
  match goal with
  | [ |- F ?x ] => unify x k
  end.
  (* the same goal, produced with unfold_sep_star, doesn't work; unify succeeds
  but constr_eq does not *)
  Set Printing Universes.
  let k := constr:(mem_except (mem_union m1 m2) a) in
  match goal with
  | [ |- F ?x ] => constr_eq x k
  end.

  pattern (mem_union m1 m2).
  simpl.

  replace (mem_union m1 m2) with m1.
  match goal with
    |- F (mem_except m1 a) => idtac
  end.
Abort.


Polymorphic Axiom x : Type -> Prop.
Goal True.
  constr_eq Type Type. (* success *)
  constr_eq x x. (* Error: Tactic failure: Not equal. *)

