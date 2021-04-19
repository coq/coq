(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Control.
Require Ltac2.List.
Require Import Ltac2.Printf.

Ltac2 Type t.
(** Type of attribute declarations.
    A mutable set of attribute declarations: string -> attribute_value. *)

Module Attribute.
Ltac2 Type attribute_value.
(** Type of an attribute declaration *)

Ltac2 @ external to_string : attribute_value -> string option := "ltac2" "attributes_attribute_to_string".
Ltac2 @ external to_ident : attribute_value -> ident option := "ltac2" "attributes_attribute_to_ident".
Ltac2 @ external to_attributes : attribute_value -> t option := "ltac2" "attributes_attribute_to_attributes".
Ltac2 @ external is_empty : attribute_value -> bool := "ltac2" "attributes_attribute_is_empty".
Ltac2 @ external to_message : string -> attribute_value -> message := "ltac2" "attributes_attribute_to_message".
(** Prints the key and attribute. *)

(* For internal use: constructs attributes *)
Ltac2 @ external empty : unit -> attribute_value := "ltac2" "attributes_attribute_empty".
Ltac2 @ external of_string : string -> attribute_value := "ltac2" "attributes_attribute_of_string".
Ltac2 @ external of_ident : ident -> attribute_value := "ltac2" "attributes_attribute_of_ident".
Ltac2 @ external of_attributes : t -> attribute_value := "ltac2" "attributes_attribute_of_attributes".
End Attribute.

Ltac2 @ external is_empty : t -> bool := "ltac2" "attributes_is_empty".
(** Checks if the attributes are empty. *)

Ltac2 @ external consume : t -> string -> Attribute.attribute_value option  := "ltac2" "attributes_consume".
(** [consume attrs key] Consumes the first attribute of key `key` from the attributes [attrs],
    removing it from the list of attributes as a side-effect. *)

Ltac2 @ external to_message : t -> message := "ltac2" "attributes_to_message".
(** Prints the current state of the attributes. *)

Ltac2 @ external of_list : (string * Attribute.attribute_value) list -> t := "ltac2" "attributes_of_list".
(* For internal use: constructs a list of attributes *)

(* Higher-level functions to work with attributes. *)

Ltac2 check_empty_attributes tac attrs :=
  if Attributes.is_empty attrs then ()
  else Control.throw (Invalid_argument (Some
    (Message.concat (Message.of_string "Tactic ") (Message.concat (Message.of_string tac)
      (Message.concat (Message.of_string " does not support attribute(s): ")
      (Attributes.to_message attrs)))))).

Ltac2 unsupported_attribute_value tac key value :=
  Control.throw (Invalid_argument (Some
  (Message.concat (Message.of_string "Tactic ") (Message.concat (Message.of_string tac)
    (Message.concat (Message.of_string " does not support attribute: ")
    (Attributes.Attribute.to_message key value)))))).

(** [parse_option attrs k cont] parses an option [k] in attributes [attrs]:
    - if present it ensures that there is no duplicate attribute declaration,
      and returns [cont k]
    - otherwise returns [None]. *)
Ltac2 parse_option attrs k cont :=
  let value := Attributes.consume attrs k in
  match value with
  | Some v =>
    match Attributes.consume attrs k with
    | Some duplicate =>
      Control.throw (Invalid_argument (Some (fprintf "Duplicate attribute values for %s." k)))
    | None => cont v
    end
  | None => None
  end.

(** Parse a flag [k] in attributes [attrs]:
    - if present ensure that there is no attached value and no duplicate attribute declaration,
      and returns [true]
    - otherwise returns [false]. *)
Ltac2 parse_flag attrs k :=
  let cont v :=
    match Attributes.Attribute.is_empty v with
    | true => Some ()
    | false =>
        Control.throw (Invalid_argument (Some (fprintf "Attribute %s does not accept any value" k)))
    end
  in
  match parse_option attrs k cont with
  | Some _ => true
  | None => false
  end.
