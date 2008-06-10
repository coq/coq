(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Term
open Proof_type
open Topconstr
open Names
open Termops

type relation =
   { rel_a: constr ;
     rel_aeq: constr;
     rel_refl: constr option;
     rel_sym: constr option;
     rel_trans : constr option;
     rel_quantifiers_no: int  (* it helps unification *);
     rel_X_relation_class: constr;
     rel_Xreflexive_relation_class: constr
   }

type 'a relation_class =
   Relation of 'a    (* the [rel_aeq] of the relation or the relation*)
 | Leibniz of constr option  (* the [carrier] (if [eq] is partially instantiated)*)

type 'a morphism =
    { args : (bool option * 'a relation_class) list;
      output : 'a relation_class;
      lem : constr;
      morphism_theory : constr
    }

type morphism_signature = (bool option * constr_expr) list * constr_expr

val pr_morphism_signature : morphism_signature -> Pp.std_ppcmds

val register_replace : (tactic option -> constr -> constr -> tactic) -> unit
val register_general_rewrite : (bool -> occurrences -> constr -> tactic) -> unit

val print_setoids : unit -> unit

val equiv_list : unit -> constr list
val default_relation_for_carrier :
  ?filter:(relation -> bool) -> types -> relation relation_class 
(* [default_morphism] raises [Not_found] *)
val default_morphism :
  ?filter:(constr morphism -> bool) -> constr -> relation morphism

val setoid_replace :
  tactic option -> constr option -> constr -> constr -> new_goals:constr list -> tactic
val setoid_replace_in :
  tactic option -> 
 identifier -> constr option -> constr -> constr -> new_goals:constr list ->
  tactic

val general_s_rewrite :
  bool -> occurrences -> constr -> new_goals:constr list -> tactic
val general_s_rewrite_in :
  identifier -> bool -> occurrences -> constr -> new_goals:constr list -> tactic

val setoid_reflexivity : tactic
val setoid_symmetry : tactic
val setoid_symmetry_in : identifier -> tactic
val setoid_transitivity : constr -> tactic

val add_relation :
 Names.identifier -> constr_expr -> constr_expr -> constr_expr option ->
  constr_expr option -> constr_expr option -> unit

val add_setoid :
 Names.identifier -> constr_expr -> constr_expr -> constr_expr -> unit

val new_named_morphism :
 Names.identifier -> constr_expr -> morphism_signature option -> unit

val relation_table_find : constr -> relation
val relation_table_mem : constr -> bool

val prrelation : relation -> Pp.std_ppcmds
