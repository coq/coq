(* Coq 8.2beta4 *)
Require Import Classical_Prop. 

Unset Structural Injection.

Record coreSemantics : Type := CoreSemantics {
  core: Type;
  corestep: core ->  core -> Prop;
  corestep_fun: forall q q1 q2, corestep q q1 -> corestep q q2 -> q1 = q2
}.

Definition state : Type := {sem: coreSemantics & sem.(core)}.

Inductive step: state -> state -> Prop :=
  | step_core: forall sem st st'
             (Hcs: sem.(corestep) st st'),
             step (existT _ sem st) (existT _ sem st').

Lemma step_fun: forall st1 st2 st2', step st1 st2 -> step st1 st2' -> st2 = st2'.
Proof.
intros.
inversion H; clear H; subst. inversion H0; clear H0; subst; auto.
generalize (inj_pairT2 _ _ _ _ _ H2); clear H2; intro; subst.
rewrite (corestep_fun _ _ _ _ Hcs Hcs0); auto.
Qed.

Record oe_core := oe_Core {
    in_core: Type;
    in_corestep: in_core -> in_core -> Prop;
    in_corestep_fun: forall q  q1 q2,  in_corestep q q1 -> in_corestep q q2 -> q1 = q2;
   in_q: in_core
}.

Definition oe2coreSem (oec : oe_core) : coreSemantics :=
  CoreSemantics oec.(in_core) oec.(in_corestep)  oec.(in_corestep_fun).

Definition oe_corestep (q q': oe_core) :=
    step (existT _ (oe2coreSem q) q.(in_q)) (existT _ (oe2coreSem q') q'.(in_q)).

Lemma inj_pairT1: forall (U: Type) (P: U -> Type) (p1 p2: U) x y,
      existT P p1 x = existT P p2 y -> p1=p2.
Proof. intros; injection H; auto.
Qed.

Definition f := CoreSemantics oe_core.

Lemma oe_corestep_fun: forall q q1 q2, 
       oe_corestep q q1 -> oe_corestep q q2 -> q1 = q2.
Proof.
unfold oe_corestep; intros.
assert (HH:= step_fun _ _ _ H H0); clear H H0.
destruct q1; destruct q2; unfold oe2coreSem; simpl in *.
generalize (inj_pairT1 _ _ _ _ _ _ HH); clear HH; intros.
injection H.
revert in_q1  in_corestep1 in_corestep_fun1
          H.
pattern in_core1.
apply eq_ind_r with (x := in_core0).
admit.
apply sym_eq.
(** good to here **)
Show Universes.
Print Universes.
Fail apply H0.
