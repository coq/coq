(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Here are collected some results about the type sumbool (see INIT/Specif.v)
   [sumbool A B], which is written [{A}+{B}], is the informative
   disjunction "A or B", where A and B are logical propositions.
   Its extraction is isomorphic to the type of booleans. *)

(** A boolean is either [true] or [false], and this is decidable *)

Definition sumbool_of_bool : (b:bool) {b=true}+{b=false}.
Proof.
  NewDestruct b; Auto.
Defined.

Hints Resolve sumbool_of_bool : bool.

Definition bool_eq_rec : (b:bool)(P:bool->Set)
                    ((b=true)->(P true))->((b=false)->(P false))->(P b).
NewDestruct b; Auto.
Defined.

Definition bool_eq_ind : (b:bool)(P:bool->Prop)
                    ((b=true)->(P true))->((b=false)->(P false))->(P b).
NewDestruct b; Auto.
Defined.


(*i pourquoi ce machin-la est dans BOOL et pas dans LOGIC ?  Papageno i*)

(** Logic connectives on type [sumbool] *)

Section connectives.

Variables A,B,C,D : Prop.

Hypothesis H1 : {A}+{B}.
Hypothesis H2 : {C}+{D}.

Definition sumbool_and : {A/\C}+{B\/D}.
Proof.
Case H1; Case H2; Auto.
Defined.

Definition sumbool_or : {A\/C}+{B/\D}.
Proof.
Case H1; Case H2; Auto.
Defined.

Definition sumbool_not : {B}+{A}.
Proof.
Case H1; Auto.
Defined.

End connectives.

Hints Resolve sumbool_and sumbool_or sumbool_not : core.


(** Any decidability function in type [sumbool] can be turned into a function
    returning a boolean with the corresponding specification: *)

Definition bool_of_sumbool : 
  (A,B:Prop) {A}+{B} -> { b:bool | if b then A else B }.
Proof.
Intros A B H.
Elim H; [ Intro; Exists true; Assumption
        | Intro; Exists false; Assumption ].
Defined.
Implicits bool_of_sumbool.
