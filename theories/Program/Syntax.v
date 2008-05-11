(* -*- coq-prog-args: ("-emacs-U") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Custom notations and implicits for Coq prelude definitions.
 *
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(** Notations for the unit type and value. *)

Notation " () " := Datatypes.unit : type_scope.
Notation " () " := tt.

(** Set maximally inserted implicit arguments for standard definitions. *)

Implicit Arguments eq [[A]].

Implicit Arguments Some [[A]].
Implicit Arguments None [[A]].

Implicit Arguments inl [[A] [B]].
Implicit Arguments inr [[A] [B]].

Implicit Arguments left [[A] [B]].
Implicit Arguments right [[A] [B]].

Require Import Coq.Lists.List.

Implicit Arguments nil [[A]].
Implicit Arguments cons [[A]].

(** Standard notations for lists. *)

Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

(** n-ary exists *)

Notation " 'exists' x y , p" := (ex (fun x => (ex (fun y => p))))
  (at level 200, x ident, y ident, right associativity) : type_scope.

Notation " 'exists' x y z , p" := (ex (fun x => (ex (fun y => (ex (fun z => p))))))
  (at level 200, x ident, y ident, z ident, right associativity) : type_scope.

Notation " 'exists' x y z w , p" := (ex (fun x => (ex (fun y => (ex (fun z => (ex (fun w => p))))))))
  (at level 200, x ident, y ident, z ident, w ident, right associativity) : type_scope.

Tactic Notation "exist" constr(x) := exists x.
Tactic Notation "exist" constr(x) constr(y) := exists x ; exists y.
Tactic Notation "exist" constr(x) constr(y) constr(z) := exists x ; exists y ; exists z.
Tactic Notation "exist" constr(x) constr(y) constr(z) constr(w) := exists x ; exists y ; exists z ; exists w.
