Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Definition relation := fun A : Type => A -> A -> Prop.

Class Decision (P : Prop) := decide : {P} + {not P}.
Global Arguments decide _ {_} : simpl never, assert.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
  inj x y : S (f x) (f y) -> R x y.

Definition kmap {K1} {K2} {M1} {M2 : Type -> Type} {A} (f : K1 -> K2) (m : M1 A) : M2 A.
admit.
Defined.
Definition kmap_inj {K1} {K2} {M1} {M2 : Type -> Type} {A} (f : K1 -> K2) (m : M1 A) : Inj (@eq (M1 A)) (eq) (@kmap K1 K2 M1 M2 A f).
Admitted.

Module Export functions.

Section dep_fn_insert.
  Context {A : Type} `{forall x y:A, Decision (eq x y)} {T : A -> Type}.

  Import EqNotations.
Definition dep_fn_insert a0 (t : T a0) (f : forall a : A, T a) : forall a : A, T a.
exact (fun a =>
    match decide (a0 = a) with
    | left E => rew E in t
    | right _ => f a
    end).
Defined.
End dep_fn_insert.

End functions.

Module Export Sts.

  Record sts {Label : Type} : Type :=
  { _state      :> Type }.
  #[global] Arguments sts _ : clear implicits.

  Record t :=
  { Label : Type
  ; _sts :> sts Label }.
  #[global] Arguments Build_t {_} _.
  Definition State (x : t) := x.(_sts).(_state).
End Sts.

Module Export Compose.

  Record config := {
    name : Set;
    external_event : Set;
    sts_name : name -> Sts.t;
  }.
End Compose.

  Section Compose.
    Context (sf: config).
Definition State : Type.
exact (forall n, Sts.State (sts_name sf n)).
Defined.
Definition compose_lts : Sts.sts (external_event sf).
exact ({|
      Sts._state := State;
      |}).
Defined.
  End Compose.
  Variant guestT := guest | host.

    Variant t : Set :=  A.

    Class Types {arch : t} := MKTYPES {
      regs_t : guestT -> Type;
    }.

Module Export isa.

Module Type OPSEM_ISA.
End OPSEM_ISA.

End isa.

Module Export nova.

Module Type NOVA_ISA.
  Module Export opsem_isa.
  End opsem_isa.
End NOVA_ISA.

End nova.

Module Export aarch64.

  Module Import isa.

Module Type aarch64.

  Definition the_arch := A.
End aarch64.
  End isa.

Module Export nova.

Module Export Nova_aarch64.
  Module Export opsem_isa.
    Include aarch64.
  End opsem_isa.

End Nova_aarch64.

Implicit Types (is_guest : guestT).

Module Type CPU_STS_BASE.
  Parameter cpu_sts : forall is_guest, Sts.t.

End CPU_STS_BASE.

Module Type CPU_STS_DERIVED (Import cpu_sts_base : CPU_STS_BASE).

  Module Export regs.
Definition t is_guest : Type.
exact (Sts.State (cpu_sts is_guest)).
Defined.
  End regs.
End CPU_STS_DERIVED.

Module Type CPU_STS := CPU_STS_BASE <+ CPU_STS_DERIVED.

Module Type CPU_REGS (isa_regs : OPSEM_ISA) :=
  CPU_STS.

Section cpuid.
Definition gicv : Sts.t.
Admitted.
End cpuid.

Module Export cpu_regs.

  Module Export guest.
    Variant name : Set := | NAME.
Definition sts_config : Compose.config.
exact ({| Compose.name := name
         ; Compose.external_event := False
         ; Compose.sts_name nm :=
            match nm with
            | NAME => gicv
            end
         |}).
Defined.
Definition sts : Sts.sts False.
exact (compose_lts sts_config).
Defined.
  End guest.

Definition cpu_sts (is_guest : guestT) : Sts.t.
exact (if is_guest
    then Sts.Build_t guest.sts
    else Sts.Build_t guest.sts).
Defined.

  Include CPU_STS_DERIVED.

  End cpu_regs.

Module NOVA_STATE_DEFS (Import nova_isa : NOVA_ISA) (Import opsem_cpu : CPU_REGS nova_isa.opsem_isa).

#[global] Instance nova_arch_types : @Types the_arch.
exact ({|
      regs_t := opsem_cpu.regs.t ;
    |}).
Defined.

End NOVA_STATE_DEFS.
Module Import M := NOVA_STATE_DEFS aarch64.nova.Nova_aarch64 cpu_regs.
Create HintDb empty.

Goal forall eqdec v (vRegs : @Sts._state False cpu_regs.guest.sts),
 (@Inj (@Sts._state False cpu_regs.guest.sts) (@regs_t _ nova_arch_types guest)
                          (@eq (@Sts._state False cpu_regs.guest.sts)) (@eq (@regs_t _ nova_arch_types guest))
                          (@functions.dep_fn_insert cpu_regs.guest.name eqdec
                             (fun x : cpu_regs.guest.name =>
                              Sts.State
                                match x return Sts.t with
                                | cpu_regs.guest.NAME => gicv
                                end) cpu_regs.guest.NAME (v (vRegs cpu_regs.guest.NAME)))).
Proof.
  intros.
  Fail autoapply @kmap_inj with empty.
Abort.
End nova.
End aarch64.
