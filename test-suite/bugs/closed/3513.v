(* File reduced by coq-bug-finder from original input, then from 5752 lines to 3828 lines, then from 2707 lines to 558 lines, then from 472 lines to 168 lines, then from 110 lines to 101 lines, then from 96 lines to 77 lines, then from 80 lines to 64 lines *)
Require Coq.Setoids.Setoid.
Import Coq.Setoids.Setoid.
Generalizable All Variables.
Axiom admit : forall {T}, T.
Class Equiv (A : Type) := equiv : relation A.
Class type (A : Type) {e : Equiv A} := eq_equiv : Equivalence equiv.
Class ILogicOps Frm := { lentails: relation Frm;
                         ltrue: Frm;
                         land: Frm -> Frm -> Frm;
                         lor: Frm -> Frm -> Frm }.
Infix "|--"  := lentails (at level 79, no associativity).
Class ILogic Frm {ILOps: ILogicOps Frm} := { lentailsPre:> PreOrder lentails }.
Definition lequiv `{ILogic Frm} P Q := P |-- Q /\ Q |-- P.
Infix "-|-"  := lequiv (at level 85, no associativity).
Instance lequiv_inverse_lentails `{ILogic Frm} : subrelation lequiv (inverse lentails) := admit.
Record ILFunFrm (T : Type) `{e : Equiv T} `{ILOps : ILogicOps Frm} := mkILFunFrm { ILFunFrm_pred :> T -> Frm }.
Section ILogic_Fun.
  Context (T: Type) `{TType: type T}.
  Context `{IL: ILogic Frm}.
  Local Instance ILFun_Ops : ILogicOps (@ILFunFrm T _ Frm _) := admit.
  Definition ILFun_ILogic : ILogic (@ILFunFrm T _ Frm _) := admit.
End ILogic_Fun.
Arguments ILFunFrm _ {e} _ {ILOps}.
Instance ILogicOps_Prop : ILogicOps Prop | 2 := {| lentails P Q := (P : Prop) -> Q;
                                                   ltrue        := True;
                                                   land     P Q := P /\ Q;
                                                   lor      P Q := P \/ Q |}.
Axiom Action : Set.
Definition Actions := list Action.
Instance ActionsEquiv : Equiv Actions := { equiv a1 a2 := a1 = a2 }.
Definition OPred := ILFunFrm Actions Prop.
Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.
Definition catOP (P Q: OPred) : OPred := admit.
Add Parametric Morphism : catOP with signature lentails ==> lentails ==> lentails as catOP_entails_m.
apply admit.
Defined.
Definition catOPA (P Q R : OPred) : catOP (catOP P Q) R -|- catOP P (catOP Q R) := admit.
Class IsPointed (T : Type) := point : T.
Notation IsPointed_OPred P := (IsPointed (exists x : Actions, (P : OPred) x)).
Record PointedOPred := mkPointedOPred {
                           OPred_pred :> OPred;
                           OPred_inhabited: IsPointed_OPred OPred_pred
                         }.
Existing Instance OPred_inhabited.
Canonical Structure default_PointedOPred O `{IsPointed_OPred O} : PointedOPred
  := {| OPred_pred := O ; OPred_inhabited := _ |}.
Instance IsPointed_catOP `{IsPointed_OPred P, IsPointed_OPred Q} : IsPointed_OPred (catOP P Q) := admit.
Goal forall (T : Type) (O0 : T -> OPred) (O1 : T -> PointedOPred)
            (tr : T -> T) (O2 : PointedOPred) (x : T)
            (H : forall x0 : T, catOP (O0 x0) (O1 (tr x0)) |-- O1 x0),
     exists e1 e2,
       catOP (O0 e1) (OPred_pred e2) |-- catOP (O1 x) O2.
  intros; do 2 esplit.
  rewrite <- catOPA.
  lazymatch goal with
  | |- ?R (?f ?a ?b) (?f ?a' ?b') =>
    let P := constr:(fun H H' => @Morphisms.proper_prf (OPred -> OPred -> OPred)
         (@Morphisms.respectful OPred (OPred -> OPred)
            (@lentails OPred
               (@ILFun_Ops Actions ActionsEquiv Prop ILogicOps_Prop))
            (@lentails OPred
               (@ILFun_Ops Actions ActionsEquiv Prop ILogicOps_Prop) ==>
             @lentails OPred
               (@ILFun_Ops Actions ActionsEquiv Prop ILogicOps_Prop))) catOP
         catOP_entails_m_Proper a a' H b b' H') in
    pose P;
    refine (P _ _)
  end; unfold Basics.flip.
  Focus 2.
  (* As in 8.5, allow a shelved subgoal to remain *)
  apply reflexivity.
  
