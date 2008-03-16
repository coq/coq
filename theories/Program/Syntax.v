(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
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

(** Unicode lambda abstraction, does not work with factorization of lambdas. *)

Notation  " 'λ' x : T , y " := (fun x:T => y) (at level 100, x,T,y at level 10, no associativity) : program_scope.

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

(** n-ary exists ! *)

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

(* Notation " 'Σ' x : T , p" := (sigT (fun x : T => p)) *)
(*   (at level 200, x ident, y ident, right associativity) : program_scope. *)

(* Notation " 'Π' x : T , p " := (forall x : T, p) *)
(*   (at level 200, x ident, right associativity) : program_scope. *)