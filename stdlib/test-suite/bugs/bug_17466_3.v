From Stdlib Require String.
From Stdlib Require ZArith.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Class Monad(M: Type -> Type) := mkMonad {
  Bind: forall {A B}, M A -> (A -> M B) -> M B;
  Return: forall {A}, A -> M A;

  left_identity: forall {A B} (a: A) (f: A -> M B),
    Bind (Return a) f = f a;
  right_identity: forall {A} (m: M A),
    Bind m Return = m;
  associativity: forall {A B C} (m: M A) (f: A -> M B) (g: B -> M C),
    Bind (Bind m f) g = Bind m (fun x => Bind (f x) g)
}.

Definition StateAbortFail(S A: Type) := S -> (option (option A) * S).

#[global] Instance StateAbortFail_Monad(S: Type): Monad (StateAbortFail S).
Admitted.
Local Set Universe Polymorphism.
  Inductive list {A : Type} : Type := nil | cons (_:A) (_:list).
  Arguments list : clear implicits.

  Section WithElement.
    Context {A} (x : A).
    Fixpoint repeat (x : A) (n : nat) {struct n} : list A :=
      match n with
      | 0 => nil
      | S k => cons x (repeat x k)
      end.
  End WithElement.

Fixpoint hlist@{i j k} (argts : list@{j} Type@{i}) : Type@{k} :=
  match argts with
  | nil => unit
  | cons T argts' => T * hlist argts'
  end.

Definition tuple A n := hlist (repeat A n).
  Notation byte := (Stdlib.Init.Byte.byte: Type).
Import BinInt.
Local Open Scope Z_scope.

Module Export word.
  Class word {width : Z} := {
    rep : Type;

    unsigned : rep -> Z;
    signed : rep -> Z;
    of_Z : Z -> rep;

    add : rep -> rep -> rep;
    sub : rep -> rep -> rep;
    opp : rep -> rep;

    or : rep -> rep -> rep;
    and : rep -> rep -> rep;
    xor : rep -> rep -> rep;
    not : rep -> rep;
    ndn : rep -> rep -> rep;

    mul : rep -> rep -> rep;
    mulhss : rep -> rep -> rep;
    mulhsu : rep -> rep -> rep;
    mulhuu : rep -> rep -> rep;

    divu : rep -> rep -> rep;
    divs : rep -> rep -> rep;
    modu : rep -> rep -> rep;
    mods : rep -> rep -> rep;

    slu : rep -> rep -> rep;
    sru : rep -> rep -> rep;
    srs : rep -> rep -> rep;

    eqb : rep -> rep -> bool;
    ltu : rep -> rep -> bool;
    lts : rep -> rep -> bool;

    gtu x y := ltu y x;
    gts x y := lts y x;

    swrap z := (z + 2^(width-1)) mod 2^width - 2^(width-1);

    sextend: Z -> rep -> rep;
  }.
  Arguments word : clear implicits.
  Global Hint Mode word + : typeclass_instances.
  Local Hint Mode word - : typeclass_instances.

  Class ok {width} {word : word width}: Prop := {
    wrap z := z mod 2^width;

    width_pos: 0 < width;

    unsigned_of_Z : forall z, unsigned (of_Z z) = wrap z;
    signed_of_Z : forall z, signed (of_Z z) = swrap z;
    of_Z_unsigned : forall x, of_Z (unsigned x) = x;

    unsigned_add : forall x y, unsigned (add x y) = wrap (Z.add (unsigned x) (unsigned y));
    unsigned_sub : forall x y, unsigned (sub x y) = wrap (Z.sub (unsigned x) (unsigned y));
    unsigned_opp : forall x, unsigned (opp x) = wrap (Z.opp (unsigned x));

    unsigned_or : forall x y, unsigned (or x y) = wrap (Z.lor (unsigned x) (unsigned y));
    unsigned_and : forall x y, unsigned (and x y) = wrap (Z.land (unsigned x) (unsigned y));
    unsigned_xor : forall x y, unsigned (xor x y) = wrap (Z.lxor (unsigned x) (unsigned y));
    unsigned_not : forall x, unsigned (not x) = wrap (Z.lnot (unsigned x));
    unsigned_ndn : forall x y, unsigned (ndn x y) = wrap (Z.ldiff (unsigned x) (unsigned y));

    unsigned_mul : forall x y, unsigned (mul x y) = wrap (Z.mul (unsigned x) (unsigned y));
    signed_mulhss : forall x y, signed (mulhss x y) = swrap (Z.mul (signed x) (signed y) / 2^width);
    signed_mulhsu : forall x y, signed (mulhsu x y) = swrap (Z.mul (signed x) (unsigned y) / 2^width);
    unsigned_mulhuu : forall x y, unsigned (mulhuu x y) = wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    unsigned_divu : forall x y, unsigned y <> 0 -> unsigned (divu x y) = wrap (Z.div (unsigned x) (unsigned y));
    signed_divs : forall x y, signed y <> 0 -> signed x <> -2^(width-1) \/ signed y <> -1 -> signed (divs x y) = swrap (Z.quot (signed x) (signed y));
    unsigned_modu : forall x y, unsigned y <> 0 -> unsigned (modu x y) = wrap (Z.modulo (unsigned x) (unsigned y));
    signed_mods : forall x y, signed y <> 0 -> signed (mods x y) = swrap (Z.rem (signed x) (signed y));

    unsigned_slu : forall x y, Z.lt (unsigned y) width -> unsigned (slu x y) = wrap (Z.shiftl (unsigned x) (unsigned y));
    unsigned_sru : forall x y, Z.lt (unsigned y) width -> unsigned (sru x y) = wrap (Z.shiftr (unsigned x) (unsigned y));
    signed_srs : forall x y, Z.lt (unsigned y) width -> signed (srs x y) = swrap (Z.shiftr (signed x) (unsigned y));

    unsigned_eqb : forall x y, eqb x y = Z.eqb (unsigned x) (unsigned y);
    unsigned_ltu : forall x y, ltu x y = Z.ltb (unsigned x) (unsigned y);
    signed_lts : forall x y, lts x y = Z.ltb (signed x) (signed y);
  }.
  Arguments ok {_} _.
End word.
Global Coercion word.rep : word >-> Sortclass.

Class Bitwidth(width: Z): Prop := {
  width_cases: width = 32%Z \/ width = 64%Z
}.

Definition w8  := tuple byte 1.
Definition w16 := tuple byte 2.
Definition w32 := tuple byte 4.
Definition w64 := tuple byte 8.

Class MachineWidth(t: Type) := {

  add: t -> t -> t;
  sub: t -> t -> t;
  mul: t -> t -> t;
  div: t -> t -> t;
  rem: t -> t -> t;

  negate: t -> t;

  reg_eqb: t -> t -> bool;
  signed_less_than: t -> t -> bool;
  ltu: t -> t -> bool;

  xor: t -> t -> t;
  or: t -> t -> t;
  and: t -> t -> t;

  XLEN: Z;

  regToInt8: t -> w8;
  regToInt16: t -> w16;
  regToInt32: t -> w32;
  regToInt64: t -> w64;

  uInt8ToReg: w8 -> t;
  uInt16ToReg: w16 -> t;
  uInt32ToReg: w32 -> t;
  uInt64ToReg: w64 -> t;

  int8ToReg: w8 -> t;
  int16ToReg: w16 -> t;
  int32ToReg: w32 -> t;
  int64ToReg: w64 -> t;

  s32: t -> t;
  u32: t -> t;

  regToZ_signed: t -> Z;
  regToZ_unsigned: t -> Z;

  sll: t -> Z -> t;
  srl: t -> Z -> t;
  sra: t -> Z -> t;

  divu: t -> t -> t;
  remu: t -> t -> t;

  maxSigned: t;
  maxUnsigned: t;
  minSigned: t;

  regToShamt5: t -> Z;
  regToShamt: t -> Z;

  highBits: Z -> t;

  ZToReg: Z -> t;
}.

#[global] Instance MachineWidth_XLEN{width}{_: Bitwidth width}{word: word width}: MachineWidth word.
Admitted.

Notation Register := BinInt.Z (only parsing).

Inductive InstructionSet : Type :=
  | RV32I : InstructionSet
  | RV32IM : InstructionSet
  | RV32IA : InstructionSet
  | RV32IMA : InstructionSet
  | RV32IF : InstructionSet
  | RV32IMF : InstructionSet
  | RV32IAF : InstructionSet
  | RV32IMAF : InstructionSet
  | RV64I : InstructionSet
  | RV64IM : InstructionSet
  | RV64IA : InstructionSet
  | RV64IMA : InstructionSet
  | RV64IF : InstructionSet
  | RV64IMF : InstructionSet
  | RV64IAF : InstructionSet
  | RV64IMAF : InstructionSet.

Module Export map.
  Class map {key value} := mk {
    rep : Type;

    get: rep -> key -> option value;

    empty : rep;
    put : rep -> key -> value -> rep;
    remove : rep -> key -> rep;
    fold{R: Type}: (R -> key -> value -> R) -> R -> rep -> R;
  }.
  Arguments map : clear implicits.

  Global Coercion map.rep : map >-> Sortclass.
Import Stdlib.Strings.String.

Section Machine.

  Context {width: Z} {word: word width} {word_ok: word.ok word}.
  Context {Registers: map.map Register word}.
  Context {Mem: map.map word byte}.

  Definition LogItem{_: Bitwidth width}: Type := (Mem * string * list word) * (Mem * list word).
Definition XAddrs: Type.
admit.
Defined.

  Section WithBitwidth.
    Context {BW: Bitwidth width}.

    Record RiscvMachine := mkRiscvMachine {
      getRegs: Registers;
      getPc: word;
      getNextPc: word;
      getMem: Mem;
      getXAddrs: XAddrs;
      getLog: list LogItem;
    }.

  End WithBitwidth.
End Machine.
Module Export Run.

Section Riscv.

  Context {mword: Type}.
  Context {MW: MachineWidth mword}.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
Definition run1(iset: InstructionSet):
    M unit.
Admitted.

End Riscv.

Module Export Naive.

Definition word width: word.word width.
Admitted.
Notation word64 := (word 64%Z).

End Naive.
#[global] Instance word: word.word 64.
Admitted.
#[global] Instance Words64Naive: Bitwidth 64.
Admitted.
#[global] Instance Mem: map.map word64 Byte.byte.
Admitted.
#[global] Instance Zkeyed_map(V: Type): map.map Z V.
Admitted.
Fixpoint run(fuel: nat)(s: RiscvMachine): bool * RiscvMachine.
exact (match fuel with
  | O => (true, s)
  | S fuel' => match Run.run1 RV64IM s with
               | (Some _, s') => run fuel' s'
               | (None, s') => (false, s')
               end
  end).
Defined.

End Run.
End map.
