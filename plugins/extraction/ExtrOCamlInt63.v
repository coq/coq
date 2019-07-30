(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to OCaml of native 63-bit machine integers. *)

From Coq Require Int63 Extraction.

(** Basic data types used by some primitive operators. *)

Extract Inductive bool => bool [ true false ].
Extract Inductive prod => "( * )" [ "" ].
Extract Inductive comparison => int [ "0" "(-1)" "1" ].
Extract Inductive DoubleType.carry => "Uint63.carry" [ "Uint63.C0" "Uint63.C1" ].

(** Primitive types and operators. *)
Extract Constant Int63.int => "Uint63.t".
Extraction Inline Int63.int.
(* Otherwise, the name conflicts with the primitive OCaml type [int] *)

Extract Constant Int63.lsl => "Uint63.l_sl".
Extract Constant Int63.lsr => "Uint63.l_sr".
Extract Constant Int63.land => "Uint63.l_and".
Extract Constant Int63.lor => "Uint63.l_or".
Extract Constant Int63.lxor => "Uint63.l_xor".

Extract Constant Int63.add => "Uint63.add".
Extract Constant Int63.sub => "Uint63.sub".
Extract Constant Int63.mul => "Uint63.mul".
Extract Constant Int63.mulc => "Uint63.mulc".
Extract Constant Int63.div => "Uint63.div".
Extract Constant Int63.mod => "Uint63.rem".

Extract Constant Int63.eqb => "Uint63.equal".
Extract Constant Int63.ltb => "Uint63.lt".
Extract Constant Int63.leb => "Uint63.le".

Extract Constant Int63.addc => "Uint63.addc".
Extract Constant Int63.addcarryc => "Uint63.addcarryc".
Extract Constant Int63.subc => "Uint63.subc".
Extract Constant Int63.subcarryc => "Uint63.subcarryc".

Extract Constant Int63.diveucl => "Uint63.diveucl".
Extract Constant Int63.diveucl_21 => "Uint63.div21".
Extract Constant Int63.addmuldiv => "Uint63.addmuldiv".

Extract Constant Int63.compare => "Uint63.compare".

Extract Constant Int63.head0 => "Uint63.head0".
Extract Constant Int63.tail0 => "Uint63.tail0".
