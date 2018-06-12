open Names

(*
   The mk_?_id function build different name w.r.t. a function
   Each of their use is justified in the code
*)
val mk_rel_id : Id.t -> Id.t
val mk_correct_id : Id.t -> Id.t
val mk_complete_id : Id.t -> Id.t
val mk_equation_id : Id.t -> Id.t


val msgnl : Pp.t -> unit

val fresh_id : Id.t list -> string -> Id.t
val fresh_name : Id.t list -> string -> Name.t
val get_name : Id.t list -> ?default:string -> Name.t -> Name.t

val array_get_start : 'a array -> 'a array

val id_of_name : Name.t -> Id.t

val locate_ind : Libnames.qualid -> inductive
val locate_constant : Libnames.qualid -> Constant.t
val locate_with_msg :
  Pp.t -> (Libnames.qualid -> 'a) ->
  Libnames.qualid -> 'a

val filter_map : ('a -> bool) -> ('a -> 'b) -> 'a list -> 'b list
val list_union_eq :
  ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
val list_add_set_eq :
  ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list

val chop_rlambda_n : int -> Glob_term.glob_constr ->
  (Name.t*Glob_term.glob_constr*Glob_term.glob_constr option) list * Glob_term.glob_constr

val chop_rprod_n : int -> Glob_term.glob_constr ->
  (Name.t*Glob_term.glob_constr) list * Glob_term.glob_constr

val def_of_const : Constr.t -> Constr.t
val eq : EConstr.constr Lazy.t
val refl_equal : EConstr.constr Lazy.t
val const_of_id: Id.t ->  GlobRef.t(* constantyes *)
val jmeq : unit -> EConstr.constr
val jmeq_refl : unit -> EConstr.constr

val save : bool -> Id.t -> Safe_typing.private_constants Entries.definition_entry  -> Decl_kinds.goal_kind ->
  unit Lemmas.declaration_hook CEphemeron.key -> unit

(* [get_proof_clean do_reduce] : returns the proof name, definition, kind and hook and
   abort the proof
*)
val get_proof_clean : bool ->
  Names.Id.t *
    (Safe_typing.private_constants Entries.definition_entry * Decl_kinds.goal_kind)



(* [with_full_print f a] applies [f] to [a] in full printing environment.

   This function preserves the print settings
*)
val with_full_print : ('a -> 'b) -> 'a -> 'b


(*****************)

type function_info =
    {
      function_constant : Constant.t;
      graph_ind : inductive;
      equation_lemma : Constant.t option;
      correctness_lemma : Constant.t option;
      completeness_lemma : Constant.t option;
      rect_lemma : Constant.t option;
      rec_lemma : Constant.t option;
      prop_lemma : Constant.t option;
      is_general : bool;
    }

val find_Function_infos : Constant.t -> function_info
val find_Function_of_graph : inductive -> function_info
(* WARNING: To be used just after the graph definition !!! *)
val add_Function : bool -> Constant.t -> unit

val update_Function : function_info -> unit


(** debugging *)
val pr_info : function_info -> Pp.t
val pr_table : unit -> Pp.t


(* val function_debug : bool ref  *)
val do_observe : unit -> bool
val do_rewrite_dependent : unit -> bool

(* To localize pb *)
exception Building_graph of exn
exception Defining_principle of exn
exception ToShow of exn

val is_strict_tcc : unit -> bool

val h_intros: Names.Id.t list -> Tacmach.tactic
val h_id :  Names.Id.t
val hrec_id :  Names.Id.t
val acc_inv_id :  EConstr.constr Util.delayed
val ltof_ref : GlobRef.t Util.delayed
val well_founded_ltof : EConstr.constr Util.delayed
val acc_rel : EConstr.constr Util.delayed
val well_founded : EConstr.constr Util.delayed
val evaluable_of_global_reference : GlobRef.t -> Names.evaluable_global_reference
val list_rewrite : bool -> (EConstr.constr*bool) list -> Tacmach.tactic

val decompose_lam_n : Evd.evar_map -> int -> EConstr.t ->
  (Names.Name.t * EConstr.t) list * EConstr.t
val compose_lam : (Names.Name.t * EConstr.t) list -> EConstr.t -> EConstr.t
val compose_prod : (Names.Name.t * EConstr.t) list -> EConstr.t -> EConstr.t

type tcc_lemma_value =
  | Undefined
  | Value of Constr.t
  | Not_needed

val funind_purify : ('a -> 'b) -> ('a -> 'b)
