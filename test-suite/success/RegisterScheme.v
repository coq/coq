Set Universe Polymorphism.

Definition paths_rew_r_dep (A : Type) (x y : A) (P : forall y0 : A, y0 = y -> Type)
  (u : P y eq_refl) (H : x = y)
  : P x H.
Proof. destruct H;assumption. Defined.

Module TestLocal.
  Local Register Scheme paths_rew_r_dep as rew_r_dep for eq.

  Section GenMem.
    Variable A : Type.

    Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
      : eq_refl a = eq_refl.
    Proof.
      subst.
      exact H.
    Qed.
  End GenMem.
End TestLocal.

Module TestExport.
  #[export] Register Scheme paths_rew_r_dep as rew_r_dep for eq.

  Section GenMem.
    Variable A : Type.

    Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
      : eq_refl a = eq_refl.
    Proof.
      subst.
      exact H.
    Qed.
  End GenMem.
End TestExport.

Module Test1.
  Section GenMem.
    Variable A : Type.

    Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
      : eq_refl a = eq_refl.
    Proof.
      (* neither TestLocal or TestExport registered the scheme *)
      Fail subst.
      Export TestLocal.
      Fail subst.
      Export TestExport.
      subst.
      exact H.
    Qed.
  End GenMem.
End Test1.

Section GenMem.
  Variable A : Type.

  Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
    : eq_refl a = eq_refl.
  Proof.
    (* Export reverted by section end *)
    Fail subst.
  Abort.
End GenMem.


Module TestGlobal.
  Global Register Scheme paths_rew_r_dep as rew_r_dep for eq.

  Section GenMem.
    Variable A : Type.

    Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
      : eq_refl a = eq_refl.
    Proof.
      subst.
      exact H.
    Qed.
  End GenMem.
End TestGlobal.

Section GenMem.
  Variable A : Type.

  Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
    : eq_refl a = eq_refl.
  Proof.
    subst.
    exact H.
  Qed.
End GenMem.
