open Names
open Pp

(*
   The mk_?_id function build different name w.r.t. a function
   Each of their use is justified in the code
*)
val mk_rel_id : Id.t -> Id.t
val mk_correct_id : Id.t -> Id.t
val mk_complete_id : Id.t -> Id.t
val mk_equation_id : Id.t -> Id.t


val msgnl : std_ppcmds -> unit

val fresh_id : Id.t list -> string -> Id.t
val fresh_name : Id.t list -> string -> Name.t
val get_name : Id.t list -> ?default:string -> Name.t -> Name.t

val array_get_start : 'a array -> 'a array

val id_of_name : Name.t -> Id.t

val locate_ind : Libnames.reference -> inductive
val locate_constant : Libnames.reference -> constant
val locate_with_msg :
  Pp.std_ppcmds -> (Libnames.reference -> 'a) ->
  Libnames.reference -> 'a

val filter_map : ('a -> bool) -> ('a -> 'b) -> 'a list -> 'b list
val list_union_eq :
  ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
val list_add_set_eq :
  ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list

val chop_rlambda_n : int -> Glob_term.glob_constr ->
  (Name.t*Glob_term.glob_constr*bool) list * Glob_term.glob_constr

val chop_rprod_n : int -> Glob_term.glob_constr ->
  (Name.t*Glob_term.glob_constr) list * Glob_term.glob_constr

val def_of_const : Term.constr -> Term.constr
val eq : Term.constr Lazy.t
val refl_equal : Term.constr Lazy.t
val const_of_id: Id.t -> constant
val jmeq : unit -> Term.constr
val jmeq_refl : unit -> Term.constr

val save : bool -> Id.t -> Entries.definition_entry  -> Decl_kinds.goal_kind ->
  unit Lemmas.declaration_hook Ephemeron.key -> unit

(* [get_proof_clean do_reduce] : returns the proof name, definition, kind and hook and
   abort the proof
*)
val get_proof_clean : bool ->
  Names.Id.t *
    (Entries.definition_entry * Decl_kinds.goal_kind)



(* [with_full_print f a] applies [f] to [a] in full printing environment.

   This function preserves the print settings
*)
val with_full_print : ('a -> 'b) -> 'a -> 'b


(*****************)

type function_info =
    {
      function_constant : constant;
      graph_ind : inductive;
      equation_lemma : constant option;
      correctness_lemma : constant option;
      completeness_lemma : constant option;
      rect_lemma : constant option;
      rec_lemma : constant option;
      prop_lemma : constant option;
      is_general : bool;
    }

val find_Function_infos : constant -> function_info
val find_Function_of_graph : inductive -> function_info
(* WARNING: To be used just after the graph definition !!! *)
val add_Function : bool -> constant -> unit

val update_Function : function_info -> unit


(** debugging *)
val pr_info : function_info -> Pp.std_ppcmds
val pr_table : unit -> Pp.std_ppcmds


(* val function_debug : bool ref  *)
val do_observe : unit -> bool
val do_rewrite_dependent : unit -> bool

(* To localize pb *)
exception Building_graph of exn
exception Defining_principle of exn
exception ToShow of exn

val is_strict_tcc : unit -> bool

val h_intros: Names.Id.t list -> Proof_type.tactic
val h_id :  Names.Id.t
val hrec_id :  Names.Id.t
val acc_inv_id :  Term.constr Util.delayed
val ltof_ref : Globnames.global_reference Util.delayed
val well_founded_ltof : Term.constr Util.delayed
val acc_rel : Term.constr Util.delayed
val well_founded : Term.constr Util.delayed
val evaluable_of_global_reference : Globnames.global_reference -> Names.evaluable_global_reference
val list_rewrite : bool -> (Term.constr*bool) list -> Proof_type.tactic
