From A.B.C Require Import R.X L.Y.G Z.W.

From


    A.B.C

     Require


     Import R.X L.Y.G

     Z.W.

(** Some comments *)

(** others
with
alot
of
lines *)

Load X.
Load "A/b/c".

Time Require Import timed.

Import not_required.

Declare ML
Module "foo.bar.baz".
(* Declare ML Module "dont.include.me". *)

Declare
ML

Module

"foo"

      "bar.baz"

  "tar".


Require A B

C

.

Require Import AI BI CI.

Timeout 1234  Declare ML Module "a".

Load (* something *) here.

From foo Extra Dependency "bar/file".
Comments From foz Extra Dependency "baz/file".
Comments but also regular comments.

(* Import categories *)
Require Import -(coercions) baz (Aasdf).
Require Import - (coercions) baz (Aasdf).
Require Import-(coercions) baz.
Require Import (coercions, baz) baz (Aasdf).
Require Import(coercions, baz) baz.
Require Export -(coercions) baz (Aasdf).
Require Export-(coercions) baz.
Require Export (coercions, baz) baz (Aasdf).
Require Export(coercions, baz) baz.

(* Filtered imports *)
Require Import baz (foo(bar)).

Comments with confusing content such as Require foo.

(** * Categories *)
(** We collect here all of the files about categories. *)
(** Since there are only notations in [Category.Notations], we can just export those. *)
Require Export Category.Notations.

(** ** Definition of precategories *)
Require Category.Core.
(** ** Opposite precategories *)
Require Category.Dual.
(** ** Morphisms in precategories *)
Require Category.Morphisms.
(** ** Classification of path space *)
Require Category.Paths.
(** ** Universal objects *)
Require Category.Objects.
(** ** Product precategories *)
Require Category.Prod.
(** ** Dependent product precategories *)
Require Category.Pi.
(** ** ∑-precategories *)
Require Category.Sigma.
(** ** Strict categories *)
Require Category.Strict.
(** ** Coproduct precategories *)
Require Category.Sum.
(** ** Categories (univalent or saturated) *)
Require Category.Univalent.

Local Set Warnings Append "-notation-overridden".
Include Category.Core.
Include Category.Dual.
Include Category.Morphisms.
Include Category.Paths.
Include Category.Objects.
Include Category.Prod.
Include Category.Pi.
(** We use the [Sigma] folder only to allow us to split up the various files and group conceptually similar lemmas, but not for namespacing.  So we include the main file in it. *)
Include Category.Sigma.
Include Category.Strict.
Include Category.Sum.
Include Category.Univalent.
(** We don't want to make utf-8 notations the default, so we don't export them. *)

(** ** Subcategories *)
(** For the subfolders, we need to re-create the module structure.  Alas, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
Require Category.Subcategory.


(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Notations.
Require Export Logic.
Require Export Datatypes.
Require Export Specif.
Require Coq.Init.Byte.
Require Coq.Init.Decimal.
Require Coq.Init.Hexadecimal.
Require Coq.Init.Number.
Require Coq.Init.Nat.
Require Export Peano.
Require Export Coq.Init.Wf.
Require Export Coq.Init.Ltac.
Require Export Coq.Init.Tactics.
Require Export Coq.Init.Tauto.
(* Some initially available plugins. See also:
   - ltac_plugin (in Ltac)
   - tauto_plugin (in Tauto).
*)
Declare ML Module "cc_plugin".
Declare ML Module "firstorder_plugin".
