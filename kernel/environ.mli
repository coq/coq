
(* $Id$ *)

(*i*)
open Names
open Term
open Declarations
open Univ
open Sign
(*i*)

(*s Unsafe environments. We define here a datatype for environments. 
   Since typing is not yet defined, it is not possible to check the
   informations added in environments, and that is why we speak here
   of ``unsafe'' environments. *)

type context
type env

val empty_context : context
val empty_env : env

val universes : env -> universes
val context : env -> context
val rel_context : env -> rel_context
val named_context : env -> named_context

(* This forgets named and rel contexts *)
val reset_context : env -> env

(*s This concerns only local vars referred by names [named_context] *)
val push_named_decl : named_declaration -> env -> env
val push_named_assum : identifier * types -> env -> env
val push_named_def : identifier * constr * types -> env -> env
val change_hyps : (named_context -> named_context) -> env -> env
val instantiate_named_context  : named_context -> constr list -> (identifier * constr) list
val pop_named_decl : identifier -> env -> env

(*s This concerns only local vars referred by indice [rel_context] *)
val push_rel : rel_declaration -> env -> env
val push_rel_assum : name * types -> env -> env
val push_rel_def : name * constr * types -> env -> env
val push_rels : rel_context -> env -> env
val names_of_rel_context : env -> names_context

(*s Returns also the substitution to be applied to rel's *)
val push_rel_context_to_named_context : env -> constr list * env

(*s Push the types of a (co-)fixpoint *)
val push_rec_types : rec_declaration -> env -> env

(* Gives identifiers in [named_context] and [rel_context] *)
val ids_of_context : env -> identifier list
val map_context : (constr -> constr) -> env -> env

(*s Recurrence on [named_context] *)
val fold_named_context : (env -> named_declaration -> 'a -> 'a) -> env -> 'a -> 'a
val process_named_context : (env -> named_declaration -> env) -> env -> env

(* Recurrence on [named_context] starting from younger decl *)
val fold_named_context_reverse : ('a -> named_declaration -> 'a) -> 'a -> env -> 'a

(* [process_named_context_both_sides f env] iters [f] on the named
   declarations of [env] taking as argument both the initial segment, the
   middle value and the tail segment *)
val process_named_context_both_sides :
  (env -> named_declaration -> named_context -> env) -> env -> env 

(*s Recurrence on [rel_context] *)
val fold_rel_context : (env -> rel_declaration -> 'a -> 'a) -> env -> 'a -> 'a
val process_rel_context : (env -> rel_declaration -> env) -> env -> env

(*s add entries to environment *)
val set_universes : universes -> env -> env
val add_constraints : constraints -> env -> env
val add_constant : 
  section_path -> constant_body -> env -> env
val add_mind : 
  section_path -> mutual_inductive_body -> env -> env
val new_meta : unit -> int

(*s Looks up in environment *)

(* Looks up in the context of local vars referred by names ([named_context]) *)
(* raises [Not_found] if the identifier is not found *)
val lookup_named_type : identifier -> env -> types
val lookup_named_value : identifier -> env -> constr option
val lookup_named : identifier -> env -> constr option * types

(* Looks up in the context of local vars referred by indice ([rel_context]) *)
(* raises [Not_found] if the index points out of the context *)
val lookup_rel_type : int -> env -> name * types
val lookup_rel_value : int -> env -> constr option

(* Looks up in the context of global constant names *)
(* raises [Not_found] if the required path is not found *)
val lookup_constant : section_path -> env -> constant_body

(* Looks up in the context of global inductive names *)
(* raises [Not_found] if the required path is not found *)
val lookup_mind : section_path -> env -> mutual_inductive_body

(*s Miscellanous *)
val id_of_global : env -> global_reference -> identifier

val make_all_name_different : env -> env

(*s Functions creating names for anonymous names *)

val id_of_name_using_hdchar : env -> constr -> name -> identifier

(* [named_hd env t na] just returns [na] is it defined, otherwise it
   creates a name built from [t] (e.g. ["n"] if [t] is [nat]) *)

val named_hd : env -> constr -> name -> name

(* [lambda_name env (na,t,c)] builds [[[x:t]c] where [x] is created
   using [named_hd] if [na] is [Anonymous]; [prod_name env (na,t,c)]
   works similarly but build a product; for [it_lambda_name env c
   sign] and [it_prod_name env c sign], more recent types should come
   first in [sign]; none of these functions substitute named
   variables in [c] by de Bruijn indices *)

val lambda_name : env -> name * types * constr -> constr
val prod_name : env -> name * types * constr -> constr

val it_mkLambda_or_LetIn_name : env -> constr -> rel_context -> constr
val it_mkProd_or_LetIn_name : env -> constr -> rel_context -> constr

val it_mkProd_wo_LetIn : constr -> rel_context -> constr
val it_mkLambda_or_LetIn : constr -> rel_context -> constr
val it_mkProd_or_LetIn : constr -> rel_context -> constr

val it_mkNamedLambda_or_LetIn : constr -> named_context -> constr
val it_mkNamedProd_or_LetIn : constr -> named_context -> constr

(* [lambda_create env (t,c)] builds [[x:t]c] where [x] is a name built
   from [t]; [prod_create env (t,c)] builds [(x:t)c] where [x] is a
   name built from [t] *)

val lambda_create : env -> types * constr -> constr
val prod_create : env -> types * constr -> constr

val defined_constant : env -> constant -> bool
val evaluable_constant : env -> constant -> bool

(*s Modules. *)

type compiled_env

val export : env -> string -> compiled_env
val import : compiled_env -> env -> env

(*s Unsafe judgments. We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type unsafe_judgment = { 
  uj_val : constr;
  uj_type : types }

type unsafe_type_judgment = { 
  utj_val : constr;
  utj_type : sorts }
