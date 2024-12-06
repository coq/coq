(* Taken from bedrock2 *)

(* Note: not an utf8 file *)
From Stdlib Require Import BinInt List.
From Stdlib.Init Require Byte.
From Stdlib.Strings Require Byte String.

Definition allBytes: list Byte.byte :=
  map (fun nn => match Byte.of_N (BinNat.N.of_nat nn) with
                 | Some b => b
                 | None => Byte.x00 (* won't happen *)
                 end)
      (seq 32 95).

Notation "a b" := (@cons Byte.byte a b)
  (only printing, right associativity, at level 3, format "a b").

Notation "" := (@nil Byte.byte)
  (only printing, right associativity, at level 3, format "").

Set Warnings "-notation-incompatible-prefix".

Notation "  " := (Byte.x20) (only printing).
Notation "'!'" := (Byte.x21) (only printing).
Notation "'""'" := (Byte.x22) (only printing).
Notation "'#'" := (Byte.x23) (only printing).
Notation "'$'" := (Byte.x24) (only printing).
Notation "'%'" := (Byte.x25) (only printing).
Notation "'&'" := (Byte.x26) (only printing).
Notation "'''" := (Byte.x27) (only printing).
Notation "'('" := (Byte.x28) (only printing).
Notation "')'" := (Byte.x29) (only printing).
Notation "'*'" := (Byte.x2a) (only printing).
Notation "'+'" := (Byte.x2b) (only printing).
Notation "','" := (Byte.x2c) (only printing).
Notation "'-'" := (Byte.x2d) (only printing, at level 0).
Notation "'.'" := (Byte.x2e) (only printing).
Notation "'/'" := (Byte.x2f) (only printing, at level 0).
Notation "'0'" := (Byte.x30) (only printing).
Notation "'1'" := (Byte.x31) (only printing).
Notation "'2'" := (Byte.x32) (only printing).
Notation "'3'" := (Byte.x33) (only printing).
Notation "'4'" := (Byte.x34) (only printing).
Notation "'5'" := (Byte.x35) (only printing).
Notation "'6'" := (Byte.x36) (only printing).
Notation "'7'" := (Byte.x37) (only printing).
Notation "'8'" := (Byte.x38) (only printing).
Notation "'9'" := (Byte.x39) (only printing).
Notation "':'" := (Byte.x3a) (only printing).
Notation "';'" := (Byte.x3b) (only printing).
Notation "'<'" := (Byte.x3c) (only printing).
Notation "'='" := (Byte.x3d) (only printing).
Notation "'>'" := (Byte.x3e) (only printing).
Notation "'?'" := (Byte.x3f) (only printing).
Notation "'@'" := (Byte.x40) (only printing).
Notation "'A'" := (Byte.x41) (only printing).
Notation "'B'" := (Byte.x42) (only printing).
Notation "'C'" := (Byte.x43) (only printing).
Notation "'D'" := (Byte.x44) (only printing).
Notation "'E'" := (Byte.x45) (only printing).
Notation "'F'" := (Byte.x46) (only printing).
Notation "'G'" := (Byte.x47) (only printing).
Notation "'H'" := (Byte.x48) (only printing).
Notation "'I'" := (Byte.x49) (only printing).
Notation "'J'" := (Byte.x4a) (only printing).
Notation "'K'" := (Byte.x4b) (only printing).
Notation "'L'" := (Byte.x4c) (only printing).
Notation "'M'" := (Byte.x4d) (only printing).
Notation "'N'" := (Byte.x4e) (only printing).
Notation "'O'" := (Byte.x4f) (only printing).
Notation "'P'" := (Byte.x50) (only printing).
Notation "'Q'" := (Byte.x51) (only printing).
Notation "'R'" := (Byte.x52) (only printing).
Notation "'S'" := (Byte.x53) (only printing).
Notation "'T'" := (Byte.x54) (only printing).
Notation "'U'" := (Byte.x55) (only printing).
Notation "'V'" := (Byte.x56) (only printing).
Notation "'W'" := (Byte.x57) (only printing).
Notation "'X'" := (Byte.x58) (only printing).
Notation "'Y'" := (Byte.x59) (only printing).
Notation "'Z'" := (Byte.x5a) (only printing).
Notation "'['" := (Byte.x5b) (only printing).
Notation "'\'" := (Byte.x5c) (only printing).
Notation "']'" := (Byte.x5d) (only printing).
Notation "'^'" := (Byte.x5e) (only printing).
Notation "'_'" := (Byte.x5f) (only printing).
Notation "'`'" := (Byte.x60) (only printing).
Notation "'a'" := (Byte.x61) (only printing).
Notation "'b'" := (Byte.x62) (only printing).
Notation "'c'" := (Byte.x63) (only printing).
Notation "'d'" := (Byte.x64) (only printing).
Notation "'e'" := (Byte.x65) (only printing).
Notation "'f'" := (Byte.x66) (only printing).
Notation "'g'" := (Byte.x67) (only printing).
Notation "'h'" := (Byte.x68) (only printing).
Notation "'i'" := (Byte.x69) (only printing).
Notation "'j'" := (Byte.x6a) (only printing).
Notation "'k'" := (Byte.x6b) (only printing).
Notation "'l'" := (Byte.x6c) (only printing).
Notation "'m'" := (Byte.x6d) (only printing).
Notation "'n'" := (Byte.x6e) (only printing).
Notation "'o'" := (Byte.x6f) (only printing).
Notation "'p'" := (Byte.x70) (only printing).
Notation "'q'" := (Byte.x71) (only printing).
Notation "'r'" := (Byte.x72) (only printing).
Notation "'s'" := (Byte.x73) (only printing).
Notation "'t'" := (Byte.x74) (only printing).
Notation "'u'" := (Byte.x75) (only printing).
Notation "'v'" := (Byte.x76) (only printing).
Notation "'w'" := (Byte.x77) (only printing).
Notation "'x'" := (Byte.x78) (only printing).
Notation "'y'" := (Byte.x79) (only printing).
Notation "'z'" := (Byte.x7a) (only printing).
Notation "'{'" := (Byte.x7b) (only printing).
Notation "'|'" := (Byte.x7c) (only printing).
Notation "'}'" := (Byte.x7d) (only printing).
Notation "'~'" := (Byte.x7e) (only printing, at level 0).

Global Set Printing Width 300.

Goal False.
  let cc := eval cbv in allBytes in idtac cc.
Abort.
