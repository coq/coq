From Stdlib Require Import BinNums PosDef IntDef ListDef.
From Stdlib Require Export PrimInt63 Uint63Axioms.
From Stdlib Require Export PrimString.

Definition char63_valid (c : char63) :=
  PrimInt63.land c 255%uint63 = c.

(** * Conversion to / from lists *)

Notation of_nat n := (of_Z (Z.of_nat n)).
Notation to_nat i := (Z.to_nat (to_Z i)).

Definition to_list (s : string) : list char63 :=
  ListDef.map (fun i => get s (of_nat i)) (ListDef.seq 0 (to_nat (length s))).

Fixpoint of_list (cs : list char63) : string :=
  match cs with
  | nil       => ""%pstring
  | cons c cs => cat (make 1 c) (of_list cs)
  end.

Axiom of_to_list :
  forall (s : string),
    of_list (to_list s) = s.

Axiom to_list_length :
  forall (s : string),
    Datatypes.length (to_list s) <= to_nat max_length.

Axiom to_list_char63_valid :
  forall (s : string),
    ListDef.Forall char63_valid (to_list s).

(** * Axioms relating string operations with list operations *)

Axiom length_spec :
  forall (s : string),
    to_nat (length s) = Datatypes.length (to_list s).

Axiom get_spec :
  forall (s : string) (i : int),
    get s i = ListDef.nth (to_nat i) (to_list s) 0%uint63.

Axiom make_spec :
  forall (i : int) (c : char63),
    to_list (make i c) =
      ListDef.repeat (PrimInt63.land c 255%uint63)
        (Nat.min (to_nat i) (to_nat max_length)).

Axiom sub_spec :
  forall (s : string) (off len : int),
    to_list (sub s off len) =
      ListDef.firstn (to_nat len) (ListDef.skipn (to_nat off) (to_list s)).

Axiom cat_spec :
  forall (s1 s2 : string),
    to_list (cat s1 s2) =
      ListDef.firstn (to_nat max_length) (to_list s1 ++ to_list s2).

Notation char63_compare := PrimInt63.compare (only parsing).

Axiom compare_spec :
  forall (s1 s2 : string),
    compare s1 s2 =
      ListDef.list_compare char63_compare (to_list s1) (to_list s2).
