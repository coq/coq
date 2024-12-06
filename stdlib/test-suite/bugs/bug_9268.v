From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

Definition Register := Z%type.

Definition Opcode := Z%type.

Inductive InstructionI : Type
  := Lb : Register -> Register -> Z -> InstructionI
  |  InvalidI : InstructionI.

Inductive Instruction : Type
  := IInstruction : InstructionI -> Instruction.

Definition funct3_LB : Z := 0.

Definition opcode_LOAD : Opcode := 3.

Set Universe Polymorphism.

Definition MachineInt := Z.

Definition funct3_JALR := 0.

Axiom InstructionMapper: Type -> Type.

Definition apply_InstructionMapper(mapper: InstructionMapper Z)(inst: Instruction): Z :=
  match inst with
  | IInstruction   InvalidI   => 2
  | IInstruction   (Lb  rd rs1 oimm12) => 3
   end.

Axiom Encoder: InstructionMapper MachineInt.

Definition encode: Instruction -> MachineInt := apply_InstructionMapper Encoder.

Lemma foo: forall (ins: InstructionI),
    0 <= encode (IInstruction ins) ->
    0 <= encode (IInstruction ins) .
Proof.
  Set Printing Universes.
  intros.
  lia.
Qed.
