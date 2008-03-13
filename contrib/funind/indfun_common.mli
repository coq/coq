open Names
open Pp

(* This map is used to deal with debruijn linked indices. *)
module Link : Map.S with type key = int

(* 
   The mk_?_id function build different name w.r.t. a function 
   Each of their use is justified in the code 
*) 
val mk_rel_id : identifier -> identifier
val mk_correct_id : identifier -> identifier
val mk_complete_id : identifier -> identifier
val mk_equation_id : identifier -> identifier


val msgnl : std_ppcmds -> unit

val invalid_argument : string -> 'a

val fresh_id : identifier list -> string -> identifier
val fresh_name : identifier list -> string -> name 
val get_name : identifier list -> ?default:string -> name -> name 

val array_get_start : 'a array -> 'a array

val id_of_name : name -> identifier

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

val chop_rlambda_n : int -> Rawterm.rawconstr ->
  (name*Rawterm.rawconstr*bool) list * Rawterm.rawconstr

val chop_rprod_n : int -> Rawterm.rawconstr ->
  (name*Rawterm.rawconstr) list * Rawterm.rawconstr

val def_of_const : Term.constr -> Term.constr
val eq : Term.constr Lazy.t
val refl_equal : Term.constr Lazy.t
val const_of_id: identifier -> constant


(* [save_named] is a copy of [Command.save_named] but uses 
   [nf_betaiotazeta] instead of [nf_betaiotaevar_preserving_vm_cast] 
   


   DON'T USE IT if you cannot ensure that there is no VMcast in the proof

*)

(* val nf_betaiotazeta : Reductionops.reduction_function *)

val new_save_named : bool -> unit 

val save : bool -> identifier ->  Entries.definition_entry  -> Decl_kinds.goal_kind -> 
  Tacexpr.declaration_hook -> unit 

(* [get_proof_clean do_reduce] : returns the proof name, definition, kind and hook and 
   abort the proof 
*)
val get_proof_clean : bool ->     
  Names.identifier *
    (Entries.definition_entry * Decl_kinds.goal_kind *
       Tacexpr.declaration_hook)
    


(* [with_full_print f a] applies [f] to [a] in full printing environment 
   
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

(* To localize pb *)
exception Building_graph of exn 
exception Defining_principle of exn

