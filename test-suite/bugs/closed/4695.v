(* 
The Qed at the end of this file was slow in 8.5 and 8.5pl1 because the kernel
term comparison after evaluation was done on constants according to their user
names. The conversion still succeeded because delta applied, but was much
slower than with a canonical names comparison.
*)

Module Mod0.

  Fixpoint rec_ t d : nat :=
    match d with
    | O => O
    | S d' =>
      match t with
      | true => rec_ t d'
      | false => rec_ t d'
      end
    end.

  Definition depth := 1000.

  Definition rec t := rec_ t depth.

End Mod0.


Module Mod1.
  Module M := Mod0.
End Mod1.


Axiom rec_prop : forall t d n, Mod1.M.rec_ t d = n.

Lemma slow_qed : forall t n,
    Mod0.rec t = n.
Proof.
  intros; unfold Mod0.rec; apply rec_prop.
Timeout 2 Qed.
