(* This module is modified and extracted from Meta-Prl. *)

(* Definitions of [jterm]: *)
type param = param'
and operator = operator'
and term = term'
and bound_term = bound_term'
and param' =
  | Number of int
  | String of string
  | Token of string
  | Var of string
  | ParamList of param list
and operator' = { op_name : Opname.opname; op_params : param list; } 
and term' = { term_op : operator; term_terms : bound_term list; } 
and bound_term' = { bvars : string list; bterm : term; } 
type term_subst = (string * term) list

type error_msg = TermMatchError of term * string | StringError of string

exception RefineError of string * error_msg

(* Collect free variables: *)
val free_vars_list : term -> string list

(* Substitutions: *)
val subst_term : term list -> string list list -> string list -> term -> term
val subst : term -> string list -> term list -> term
val subst1 : term -> string -> term -> term
val var_subst : term -> term -> string -> term
val apply_subst : term -> (string * term) list -> term

(* Unification: *)
val unify_mm : term -> term -> 'a -> (string * term) list

val xnil_term : term'

(* Testing functions: *)
val is_xnil_term : term' -> bool
val is_var_term : term' -> bool
val is_true_term : term' -> bool
val is_false_term : term' -> bool
val is_all_term : term' -> bool
val is_exists_term : term' -> bool
val is_or_term : term' -> bool
val is_and_term : term' -> bool
val is_cor_term : term' -> bool
val is_cand_term : term' -> bool
val is_implies_term : term' -> bool
val is_iff_term : term' -> bool
val is_not_term : term' -> bool
val is_fun_term : term -> bool
val is_const_term : term -> bool


(* Constructors for [jterms]: *)
val var_ : string -> term'
val fun_ : string -> term list -> term'
val const_ : string -> term'
val pred_ : string -> term list -> term'
val not_ : term -> term'
val and_ : term -> term -> term'
val or_ : term -> term -> term'
val imp_ : term -> term -> term'
val cand_ : term -> term -> term'
val cor_ : term -> term -> term'
val iff_ : term -> term -> term'
val false_ : term'
val true_ : term'
val nil_term : term'
val forall : string -> term -> term'
val exists : string -> term -> term'


(* Destructors for [jterm]: *)
val dest_var : term -> string
val dest_fun : term -> string * term list
val dest_const : term -> string
val dest_not : term -> term
val dest_iff : term -> term * term
val dest_implies : term -> term * term
val dest_cand : term -> term * term
val dest_cor : term -> term * term
val dest_and : term -> term * term
val dest_or : term -> term * term
val dest_exists : term -> string * term * term
val dest_all : term -> string * term * term

(* Wide-logical connectives: *)
val wand_ : term list -> term
val wor_ : term list -> term
val wimp_ : term list -> term

(* Printing and debugging tools: *)
val fprint_str_list : out_channel -> string list -> unit
val mbreak : string -> unit
val print_strs : string list -> unit
val print_term : out_channel -> term -> unit
val print_error_msg : exn -> unit

(* Other exported functions for [jall.ml]: *)
val make_term : 'a -> 'a
val dest_term : 'a -> 'a
val make_op : 'a -> 'a
val dest_op : 'a -> 'a
val make_bterm : 'a -> 'a
val dest_bterm : 'a -> 'a
val dest_param : 'a -> 'a
val mk_var_term : string -> term'
val mk_string_term : Opname.opname -> string -> term'
