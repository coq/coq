(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** Here are collected some results about the type sumbool (see INIT/Specif.v)
   [sumbool A B], which is written [{A}+{B}], is the informative
   disjunction "A or B", where A and B are logical propositions.
   Its extraction is isomorphic to the type of booleans. *)

(** A boolean is either [true] or [false], and this is decidable *)

Lemma sumbool_of_bool : (b:bool) {b=true}+{b=false}.
Proof.
  Induction b; Auto.
Save.

Hints Resolve sumbool_of_bool : bool.

Lemma bool_eq_rec : (b:bool)(P:bool->Set)
                    ((b=true)->(P true))->((b=false)->(P false))->(P b).
Induction b; Auto.
Save.

Lemma bool_eq_ind : (b:bool)(P:bool->Prop)
                    ((b=true)->(P true))->((b=false)->(P false))->(P b).
Induction b; Auto.
Save.


(*i pourquoi ce machin-la est dans BOOL et pas dans LOGIC ?  Papageno i*)

(** Logic connectives on type [sumbool] *)

Section connectives.

Variables A,B,C,D : Prop.

Hypothesis H1 : {A}+{B}.
Hypothesis H2 : {C}+{D}.

Lemma sumbool_and : {A/\C}+{B\/D}.
Proof.
Case H1; Case H2; Auto.
Save.

Lemma sumbool_or : {A\/C}+{B/\D}.
Proof.
Case H1; Case H2; Auto.
Save.

Lemma sumbool_not : {B}+{A}.
Proof.
Case H1; Auto.
Save.

End connectives.

Hints Resolve sumbool_and sumbool_or sumbool_not : core.
