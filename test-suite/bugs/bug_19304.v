Require Import TestSuite.vector.
Require Export BinNums IntDef.

Record ulv (upper lower : Z) (T : Set) := {
  len : nat := Z.to_nat (Z.sub (Z.add upper (Zpos xH)) lower);
  val : Vector.t T len
}.

Axiom op : forall {u l : Z} (a b : ulv u l bool), ulv u l bool.



Time Record test := {
  x00 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool;
  x01 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x00 (op x00 (op x00 x00));
  x02 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x00 (op x00 (op x00 x01));
  x03 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x00 (op x00 (op x01 x02));
  x04 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x00 (op x01 (op x02 x03));
  x05 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x01 (op x02 (op x03 x04));
  x06 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x02 (op x03 (op x04 x05));
  x07 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x03 (op x04 (op x05 x06));
  x08 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x04 (op x05 (op x06 x07));
  x09 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x05 (op x06 (op x07 x08));
  x10 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x06 (op x07 (op x08 x09)); (* 0.005s *)
  x11 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x07 (op x08 (op x09 x10));
  x12 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x08 (op x09 (op x10 x11));
  x13 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x09 (op x10 (op x11 x12));
  x14 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x10 (op x11 (op x12 x13));
  x15 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x11 (op x12 (op x13 x14));
  x16 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x12 (op x13 (op x14 x15));
  x17 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x13 (op x14 (op x15 x16));
  x18 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x14 (op x15 (op x16 x17));
  x19 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x15 (op x16 (op x17 x18));
  x20 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x16 (op x17 (op x18 x19)); (* 0.337s *)
  x21 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x17 (op x18 (op x19 x20));
  x22 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x18 (op x19 (op x20 x21)); (* 1.368s *)
  x23 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x19 (op x20 (op x21 x22));
  x24 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x20 (op x21 (op x22 x23)); (* 5.685s *)
  x25 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x21 (op x22 (op x23 x24));
  x26 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x22 (op x23 (op x24 x25)); (* 23.405s *)
  x27 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x23 (op x24 (op x25 x26));
  x28 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x24 (op x25 (op x26 x27));
  x29 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x25 (op x26 (op x27 x28));
  x30 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x26 (op x27 (op x28 x29));
  x31 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x27 (op x28 (op x29 x30));
  x32 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x28 (op x29 (op x30 x31));
  x33 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x29 (op x30 (op x31 x32));
  x34 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x30 (op x31 (op x32 x33));
  x35 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x31 (op x32 (op x33 x34));
  x36 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x32 (op x33 (op x34 x35));
  x37 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x33 (op x34 (op x35 x36));
  x38 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x34 (op x35 (op x36 x37));
  x39 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x35 (op x36 (op x37 x38));
  x40 : ulv (Zpos (xI (xI (xO (xO (xO (xI xH))))))) Z0 bool := op x36 (op x37 (op x38 x39));
}.
