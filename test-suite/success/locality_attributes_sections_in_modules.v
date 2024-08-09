(** This file tests how locality attributes affect usual vernacular commands.
    PLEASE, when this file fails to compute following a voluntary change in
    Coq's behaviour, modify accordingly the tables in [sections.rst] and
    [modules.rst] in [doc/sphinx/language/core].

    Also look at the corresponding discussions about locality attributes in the
    refman (directory doc/sphinx)
    - For Definition, Lemma, ..., look at language/core/definitions.rst
    - For Axiom, Conjecture, ..., look at language/core/assumptions.rst
    - For abbreviations, look at user-extensions/syntax-extensions.rst
    - For Notations, look at user-extensions/syntax-extensions.rst
    - For Tactic Notations, look at user-extensions/syntax-extensions.rst
    - For Ltac, look at proof-engine/ltac.rst
    - For Canonical Structures, look at language/extensions/canonical.rst
    - For Hints, look at proofs/automatic-tactics/auto.rst
    - For Coercions, look at addendum/implicit-coercions.rst
    - For Ltac2, look at proof-engine/ltac2.rst
    - For Ltac2 Notations, look at proof-engine/ltac2.rst
    - For Set, look at language/core/basic.rst
*)


(** This structure is used to test availability or not of a
    [Canonical Structure]. *)
Structure PointedType : Type := { Carrier :> Set; point : Carrier }.

(** ** Tests of visibility attributes in a section inside a module *)

(** We only test [Definition], [Coercion], [Canonical] and [Set], the other
    commands only support the [local] attribute in sections, which is also
    the default visibility, making them unavailable outside the section. *)

(** *** Without attribute (default) *)

Module InSectionDefault.

Module M.
Section Bar.
  (* A definition: *)
  Definition foo := 42.
  (* A Coercion: *)
  Coercion to_nat (b : bool) := if b then 1 else 0.
  (* A Canonical Structure: *)
  Canonical natPointed : PointedType := {| Carrier := nat; point := 42 |}.
  (* A Setting: *)
  Set Universe Polymorphism.
End Bar.
End M.

Module M_not_imported.
(** First, we do not import M. *)
(* Availability of the definition *)
Fail Check foo. (* not imported *)
(* Availability of the coercion *)
Fail Check (true + 2). (* not imported *)
(* Availability of the canonical structure *)
Fail Check (point nat). (* not imported *)
(* Availability of [Set Universe Polymorphism] *)
Definition foo_i@{u} := nat.
Fail Check foo_i@{_}.
End M_not_imported.

Module M_imported.
(** Now we import M. *)
Import M.
(* Availability of the definition *)
Check foo.
(* Availability of the coercion *)
Check (true + 2).
(* Availability of the canonical structure *)
Check (point nat).
(* Availability of [Set Universe Polymorphism] *)
Definition foo_i@{u} := nat.
Fail Check foo_i@{_}.
End M_imported.

End InSectionDefault.

(** *** With the [local] attribute *)
(** We only need to test a definition, we know the other commands have no effect
    outside the section (hence outside the module containing the section). *)
Module InSectionLocal.

Module M.
Section Bar.
  (* A definition: *)
  #[local]
  Definition foo := 42.
End Bar.
End M.

Module M_not_imported.
(** First, we do not import M. *)
(* Availability of the definition *)
Fail Check foo. (* not imported *)
Check M.foo.
End M_not_imported.

Module M_imported.
(** Now we import M. *)
Import M.
(* Availability of the definition *)
Fail Check foo.
(* /!\ notice the local attribute has been passed to the module! *)
Check M.foo.
End M_imported.

End InSectionLocal.

(** *** With the [export] attribute *)
(** We only need to test a setting, it is the only command for which [export]
    is supported inside a [Section]. *)
Module InSectionExport.

Module M.
Section Bar.
  (* A Setting *)
  #[export]
  Set Universe Polymorphism.
End Bar.
End M.

Module M_not_imported.
(** **** Without importing: *)
(* Availability of [Set Universe Polymorphism] *)
Definition foo_ni@{u} := nat.
Fail Check foo_ni@{_}.
End M_not_imported.

Module M_imported.
Import M.
(* Availability of [Set Universe Polymorphism] *)
Definition foo_ni@{u} := nat.
Check foo_ni@{_}.
End M_imported.
End InSectionExport.

(** *** With the [export] attribute *)
(** We only need to test [Coercion], [Canonical] and [Set]. *)

Module InSectionGlobal.

Module M.
Section Bar.
  (* A Coercion: *)
  #[global]
  Coercion to_nat (b : bool) := if b then 1 else 0.
  (* A Canonical Structure: *)
  #[global]
  Canonical natPointed : PointedType := {| Carrier := nat; point := 42 |}.
  (* A Setting: *)
  #[global]
  Set Universe Polymorphism.
End Bar.
End M.

Module M_not_imported.
(** First, we do not import M. *)
(* Availability of the coercion *)
Fail Check (true + 2). (* not imported *)
(* Availability of the canonical structure *)
Fail Check (point nat). (* not imported *)
(* Availability of [Set Universe Polymorphism] *)
Definition foo_i@{u} := nat.
Check foo_i@{_}. (* available *)
(* /!\ global for [Set] in a section is passed to the module! *)
End M_not_imported.

Module M_imported.
(** Now we import M. *)
Import M.
(* Availability of the coercion *)
Check (true + 2).
(* Availability of the canonical structure *)
Check (point nat).
(* Availability of [Set Universe Polymorphism] *)
Definition foo_i@{u} := nat.
Check foo_i@{_}.
End M_imported.

End InSectionGlobal.
