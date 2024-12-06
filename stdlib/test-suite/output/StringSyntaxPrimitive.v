From Stdlib Require Import List.
From Stdlib.Strings Require Import String Byte Ascii.
From Stdlib Require PArray PrimFloat.
From Stdlib Require Import BinNums Uint63.

Set Printing Depth 100000.
Set Printing Width 1000.

Close Scope char_scope.
Close Scope string_scope.

(* Notations for primitive integers inside polymorphic datatypes *)
Module Test1.
  Inductive intList := mk_intList (_ : list int).
  Definition i63_from_byte (b : byte) : int := Uint63Axioms.of_Z (BinInt.Z.of_N (Byte.to_N b)).
  Definition i63_to_byte (i : int) : byte :=
      match Byte.of_N (BinInt.Z.to_N (Uint63Axioms.to_Z i)) with Some x => x | None => x00%byte end.

  Definition to_byte_list '(mk_intList a) := List.map i63_to_byte a.

  Definition from_byte_list (xs : list byte) : intList:=
    mk_intList (List.map i63_from_byte xs).

  Declare Scope intList_scope.
  Delimit Scope intList_scope with intList.

  String Notation intList from_byte_list to_byte_list : intList_scope.

  Open Scope intList_scope.
  Import List.ListNotations.
  Check mk_intList [97; 98; 99]%uint63%list.
  Check "abc"%intList.

  Definition int' := int.
  Check mk_intList (@cons int' 97 [98; 99])%uint63%list.
End Test1.

Import PArray.

(* Notations for primitive arrays *)
Module Test2.
  Inductive intArray := mk_intArray (_ : array int).

  Definition i63_from_byte (b : byte) : Uint63.int := Uint63Axioms.of_Z (BinInt.Z.of_N (Byte.to_N b)).
  Definition i63_to_byte (i : Uint63.int) : byte :=
  match Byte.of_N (BinInt.Z.to_N (Uint63Axioms.to_Z i)) with Some x => x | None => x00%byte end.

  Definition i63_to_nat x := BinInt.Z.to_nat (Uint63Axioms.to_Z x).
  Local Definition nat_length {X} (x : array X) :nat := i63_to_nat (length x).

  Local Fixpoint list_length_i63 {A} (xs : list A) :int :=
            match xs with
            | nil => 0
            | cons _ xs => 1 + list_length_i63 xs
            end.

  Definition to_byte_list '(mk_intArray a) :=
    ((fix go (n : nat) (i : Uint63.int) (acc : list byte) :=
        match n with
        | 0 => acc
        | S n => go n (i - 1) (cons (i63_to_byte a.[i]) acc)
        end) (nat_length a) (length a - 1) nil)%uint63.

  Definition from_byte_list (xs : list byte) :=
    (let arr := make (list_length_i63 xs) 0 in
    mk_intArray ((fix go i xs acc :=
        match xs with
        | nil => acc
        | cons x xs => go (i + 1) xs (acc.[i <- i63_from_byte x])
        end) 0 xs arr))%uint63.

  Declare Scope intArray_scope.
  Delimit Scope intArray_scope with intArray.

  String Notation intArray from_byte_list to_byte_list : intArray_scope.

  Open Scope intArray_scope.
  Check mk_intArray ( [| 97; 98; 99 | 0|])%uint63%array.
  Check "abc"%intArray.

End Test2.

(* Primitive arrays inside primitive arrays *)
Module Test3.

  Inductive nestArray := mk_nestArray (_ : array (array int)).
  Definition to_byte_list '(mk_nestArray a) :=
    ((fix go (n : nat) (i : Uint63.int) (acc : list byte) :=
        match n with
        | 0 => acc
        | S n => go n (i - 1) (cons (Test2.i63_to_byte a.[i].[0]) acc)
        end) (Test2.nat_length a) (length a - 1) nil)%uint63.

  Definition from_byte_list (xs : list byte) :=
    (let arr := make (Test2.list_length_i63 xs) (make 0 0) in
    mk_nestArray ((fix go i xs acc :=
        match xs with
        | nil => acc
        | cons x xs => go (i + 1) xs (acc.[i <- make 1 (Test2.i63_from_byte x)])
        end) 0 xs arr))%uint63.

  Declare Scope nestArray_scope.
  Delimit Scope nestArray_scope with nestArray.

  String Notation nestArray from_byte_list to_byte_list : nestArray_scope.

  Open Scope nestArray_scope.
  Eval cbv in mk_nestArray ( [| make 1 97; make 1 98; make 1 99 | make 0 0|])%uint63%array.
  Check "abc"%nestArray.
End Test3.



(* Notations for primitive floats inside polymorphic datatypes *)
Module Test4.
  Import PrimFloat.
  Inductive floatList := mk_floatList (_ : list float).
  Definition float_from_byte (b : byte) : float :=
    if Byte.eqb b "0"%byte then PrimFloat.zero else PrimFloat.one.
  Definition float_to_byte (f : float) : byte :=
    if PrimFloat.is_zero f then "0" else "1".
  Definition to_byte_list '(mk_floatList a) := List.map float_to_byte a.

  Definition from_byte_list (xs : list byte) : floatList:=
    mk_floatList (List.map float_from_byte xs).

  Declare Scope floatList_scope.
  Delimit Scope floatList_scope with floatList.

  String Notation floatList from_byte_list to_byte_list : floatList_scope.

  Open Scope floatList_scope.
  Import List.ListNotations.
  Check mk_floatList [97; 0; 0]%float%list.
  Check "100"%floatList.

  Definition float' := float.
  Check mk_floatList (@cons float' 1 [0; 0])%float%list.
End Test4.

Module Bug11237.

Inductive bytes := wrap_bytes { unwrap_bytes : list byte }.

Declare Scope bytes_scope.
Delimit Scope bytes_scope with bytes.
Bind Scope bytes_scope with bytes.
String Notation bytes wrap_bytes unwrap_bytes : bytes_scope.

Open Scope bytes_scope.

Example test_match :=
  match "foo" with
  | "foo" => "bar"
  | "bar" => "foo"
  | x => x
  end.

End Bug11237.
