From Stdlib Require Export Morphisms Setoid.

Class Empty A := empty : A.

Class MapFold K A M := map_fold B : (K -> A -> B -> B) -> B -> M -> B.
Global Arguments map_fold {_ _ _ _ _}.

Class FinMap K M `{forall A, Empty (M A), forall A, MapFold K A (M A)} := { }.

Definition map_filter {K A M} `{MapFold K A M, Empty M} (P : A -> Prop) : M -> M :=
  map_fold (fun k v m => m) empty.

Global Instance map_filter_proper {K A M} `{FinMap K M} (P : A -> Prop) :
  Proper (@eq (M A) ==> eq) (map_filter P).
Proof. Admitted.

#[projections(primitive=yes)]
Record seal {A} (f : A) := { unseal : A; seal_eq : unseal = f }.
Global Arguments unseal {_ _}.

Record ofe := { ofe_car :> Type }.

Definition iProto (Σ V : Type) : ofe. Admitted.

Definition iProto_dual_def {Σ V} (p : iProto Σ V) : iProto Σ V := p.
Definition iProto_dual_aux : seal (@iProto_dual_def). Proof. eexists. reflexivity. Qed.
Definition iProto_dual : forall {Σ V}, iProto Σ V -> iProto Σ V := iProto_dual_aux.(unseal).

Lemma test {Σ V} (p q q' : iProto Σ V) (Hq : q = q') :
  iProto_dual q = p.
Proof.
  setoid_rewrite Hq.
Abort.
