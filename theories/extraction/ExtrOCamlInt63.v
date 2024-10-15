(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to OCaml of native 63-bit machine integers. *)

From Stdlib Require Uint63 Sint63 Extraction.

(** Basic data types used by some primitive operators. *)

Extract Inductive bool => bool [ true false ].
Extract Inductive prod => "( * )" [ "" ].
Extract Inductive DoubleType.carry => "Uint63.carry" [ "Uint63.C0" "Uint63.C1" ].

(** Primitive types and operators. *)
Extract Constant Uint63.int => "Uint63.t".
Extraction Inline Uint63.int.
(* Otherwise, the name conflicts with the primitive OCaml type [int] *)

Extract Constant Uint63.lsl => "Uint63.l_sl".
Extract Constant Uint63.lsr => "Uint63.l_sr".
Extract Constant Sint63.asr => "Uint63.a_sr".
Extract Constant Uint63.land => "Uint63.l_and".
Extract Constant Uint63.lor => "Uint63.l_or".
Extract Constant Uint63.lxor => "Uint63.l_xor".

Extract Constant Uint63.add => "Uint63.add".
Extract Constant Uint63.sub => "Uint63.sub".
Extract Constant Uint63.mul => "Uint63.mul".
Extract Constant Uint63.mulc => "Uint63.mulc".
Extract Constant Uint63.div => "Uint63.div".
Extract Constant Uint63.mod => "Uint63.rem".
Extract Constant Sint63.div => "Uint63.divs".
Extract Constant Sint63.rem => "Uint63.rems".


Extract Constant Uint63.eqb => "Uint63.equal".
Extract Constant Uint63.ltb => "Uint63.lt".
Extract Constant Uint63.leb => "Uint63.le".
Extract Constant Sint63.ltb => "Uint63.lts".
Extract Constant Sint63.leb => "Uint63.les".

Extract Constant Uint63.addc => "Uint63.addc".
Extract Constant Uint63.addcarryc => "Uint63.addcarryc".
Extract Constant Uint63.subc => "Uint63.subc".
Extract Constant Uint63.subcarryc => "Uint63.subcarryc".

Extract Constant Uint63.diveucl => "Uint63.diveucl".
Extract Constant Uint63.diveucl_21 => "Uint63.div21".
Extract Constant Uint63.addmuldiv => "Uint63.addmuldiv".

Extract Constant Uint63.compare => "(fun x y -> let c = Uint63.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Constant Sint63.compare => "(fun x y -> let c = Uint63.compares x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".

Extract Constant Uint63.head0 => "Uint63.head0".
Extract Constant Uint63.tail0 => "Uint63.tail0".
