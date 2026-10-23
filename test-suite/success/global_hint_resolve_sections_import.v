Require TestSuite.global_hint_resolve_sections_provider.

Module Provider := TestSuite.global_hint_resolve_sections_provider.

Goal forall (A : Type) (a : A), Provider.VoPred A.
Proof. intros; auto with ghrs_vo_global nocore. Qed.

Goal forall (A : Type) (a : A), Provider.VoPred A.
Proof.
  intros.
  Fail solve [auto with ghrs_vo_export nocore].
Abort.

Import Provider.Exported.

Goal forall (A : Type) (a : A), Provider.VoPred A.
Proof. intros; auto with ghrs_vo_export nocore. Qed.

(* Opening the same module again must not duplicate its persistent hints. *)
Import Provider.Exported.

Goal forall (A : Type) (a : A), Provider.VoPred A.
Proof. intros; auto with ghrs_vo_export nocore. Qed.
