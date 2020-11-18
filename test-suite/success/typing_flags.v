From Coq Require Import Program.Tactics.

(* Part using attributes *)

#[typing(guarded=no)] Fixpoint att_f' (n : nat) : nat := att_f' n.
#[typing(guarded=no)] Program Fixpoint p_att_f' (n : nat) : nat := p_att_f' n.

#[typing(universes=no)] Definition att_T := let t := Type in (t : t).
#[typing(universes=no)] Program Definition p_att_T := let t := Type in (t : t).

#[typing(positive=no)]
Inductive att_Cor :=
| att_Over : att_Cor
| att_Next : ((att_Cor -> list nat) -> list nat) -> att_Cor.

Fail #[typing(guarded=yes)] Fixpoint f_att_f' (n : nat) : nat := f_att_f' n.
Fail #[typing(universes=yes)] Definition f_att_T := let t := Type in (t : t).

Fail #[typing(positive=yes)]
Inductive f_att_Cor :=
| f_att_Over : f_att_Cor
| f_att_Next : ((f_att_Cor -> list nat) -> list nat) -> f_att_Cor.

Print Assumptions att_f'.
Print Assumptions att_T.
Print Assumptions att_Cor.

(* Interactive + atts *)
#[typing(universes=no)] Definition i_att_T' : Type. Proof. exact (let t := Type in (t : t)). Defined.
#[typing(universes=no)] Definition d_att_T' : Type. Proof. exact (let t := Type in (t : t)). Qed.
#[typing(universes=no)] Program Definition pi_att_T' : Type. Proof. exact (let t := Type in (t : t)). Qed.

(* Note: be aware of tactics invoking [Global.env()] if this test fails. *)
#[typing(guarded=no)] Fixpoint i_att_f' (n : nat) : nat.
Proof. exact (i_att_f' n). Defined.

#[typing(guarded=no)] Fixpoint d_att_f' (n : nat) : nat.
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
