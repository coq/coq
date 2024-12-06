From Corelib Require Import Program.Tactics.

(* Part using attributes *)

#[bypass_check(guard)] Fixpoint att_f' (n : nat) : nat := att_f' n.
#[bypass_check(guard)] Program Fixpoint p_att_f' (n : nat) : nat := p_att_f' n.

#[bypass_check(universes)] Definition att_T := let t := Type in (t : t).
#[bypass_check(universes)] Program Definition p_att_T := let t := Type in (t : t).

#[bypass_check(positivity)]
Inductive att_Cor :=
| att_Over : att_Cor
| att_Next : ((att_Cor -> list nat) -> list nat) -> att_Cor.

Fail #[bypass_check(guard=no)] Fixpoint f_att_f' (n : nat) : nat := f_att_f' n.
Fail #[bypass_check(universes=no)] Definition f_att_T := let t := Type in (t : t).

Fail #[bypass_check(positivity=no)]
Inductive f_att_Cor :=
| f_att_Over : f_att_Cor
| f_att_Next : ((f_att_Cor -> list nat) -> list nat) -> f_att_Cor.

Print Assumptions att_f'.
Print Assumptions att_T.
Print Assumptions att_Cor.

(* Interactive + atts *)
#[bypass_check(universes=yes)] Definition i_att_T' : Type. Proof. exact (let t := Type in (t : t)). Defined.
#[bypass_check(universes=yes)] Definition d_att_T' : Type. Proof. exact (let t := Type in (t : t)). Qed.
#[bypass_check(universes=yes)] Program Definition pi_att_T' : Type. Proof. exact (let t := Type in (t : t)). Qed.

(* Note: be aware of tactics invoking [Global.env()] if this test fails. *)
#[bypass_check(guard=yes)] Fixpoint i_att_f' (n : nat) : nat.
Proof. exact (i_att_f' n). Defined.

#[bypass_check(guard=yes)] Fixpoint d_att_f' (n : nat) : nat.
Proof. exact (d_att_f' n). Qed.

(* check regular mode is still safe *)
Fail Fixpoint f_att_f' (n : nat) : nat := f_att_f' n.
Fail Definition f_att_T := let t := Type in (t : t).

Fail Inductive f_att_Cor :=
| f_att_Over : f_att_Cor
| f_att_Next : ((f_att_Cor -> list nat) -> list nat) -> f_att_Cor.

(* Part using Set/Unset *)
Print Typing Flags.
Unset Guard Checking.
Fixpoint f' (n : nat) : nat := f' n.

Fixpoint f (n : nat) : nat.
Proof.
  exact (f n).
Defined.

Fixpoint bla (A:Type) (n:nat) := match n with 0 =>0 | S n => n end.

Print Typing Flags.

Set Guard Checking.

Print Assumptions f.

Unset Universe Checking.

Definition T := Type.
Fixpoint g (n : nat) : T := T.

Print Typing Flags.
Set Universe Checking.

Fail Definition g2 (n : nat) : T := T.

Fail Definition e := fix e (n : nat) : nat := e n.

Unset Positivity Checking.

Inductive Cor :=
| Over : Cor
| Next : ((Cor -> list nat) -> list nat) -> Cor.

Set Positivity Checking.
Print Assumptions Cor.

Inductive Box :=
| box : forall n, f n = n -> g 2 -> Box.

Print Assumptions Box.

(** CoFixpoint *)

CoInductive Stream : Type :=  Cons : nat -> Stream -> Stream.
#[bypass_check(guard)] CoFixpoint f2 : Stream := f2.
