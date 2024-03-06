(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is deprecated since 8.19, use list Coq.Init.Byte.byte. *)
Local Set Warnings "-deprecated".
Local Set Warnings "-stdlib-vector".

Require Import Ascii Basics Bvector String Vector.
Export VectorNotations.
Open Scope program_scope.
Open Scope string_scope.

Require Import Coq.Init.Byte.

#[deprecated(since="8.19", note="Use list Coq.Init.Byte.byte.")]
Definition ByteVector := Vector.t ascii.

#[deprecated(since="8.19", note="Use @nil Coq.Init.Byte.byte.")]
Definition ByteNil : ByteVector 0 := Vector.nil ascii.

#[deprecated(since="8.19", note="Use Coq.Strings.String.list_byte_of_string.")]
Definition little_endian_to_string {n : nat} (v : ByteVector n) : string :=
  fold_right String v "".

#[deprecated(since="8.19", note="Use Coq.Strings.String.list_byte_of_string.")]
Definition to_string {n : nat} : ByteVector n -> string :=
  little_endian_to_string ∘ rev.

#[deprecated(since="8.19", note="Use Coq.Strings.String.list_byte_of_string_of_list_byte.")]
Fixpoint little_endian_of_string (s : string) : ByteVector (length s) :=
  match s with
  | "" => ByteNil
  | String b s' => b :: little_endian_of_string s'
  end.

#[deprecated(since="8.19", note="Use Coq.Strings.String.list_byte_of_string_of_list_byte.")]
Definition of_string (s : string) : ByteVector (length s) :=
  rev (little_endian_of_string s).

#[deprecated(since="8.19", note="Use Coq.Init.Byte.to_bits or Byte.to_N.")]
Fixpoint to_Bvector {n : nat} (v : ByteVector n) : Bvector (n * 8) :=
  match v with
  | [] => []
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7::v' =>
    b0::b1::b2::b3::b4::b5::b6::b7::to_Bvector v'
  end.

#[deprecated(since="8.19", note="Use Coq.Init.Byte.of_bits or Byte.of_N.")]
Fixpoint of_Bvector {n : nat} : Bvector (n * 8) -> ByteVector n :=
  match n with
  | 0 => fun _ => []
  | S _ =>
    fun v =>
      let (b0, v1) := uncons v in
      let (b1, v2) := uncons v1 in
      let (b2, v3) := uncons v2 in
      let (b3, v4) := uncons v3 in
      let (b4, v5) := uncons v4 in
      let (b5, v6) := uncons v5 in
      let (b6, v7) := uncons v6 in
      let (b7, v8) := uncons v7 in
      Ascii b0 b1 b2 b3 b4 b5 b6 b7::of_Bvector v8
  end.
