(*

  linear_constraints over Numbers.t (unbounded integers and fractions)

*)

(*

\subsection{Abstract data type for variables}

variables are abstract, may only be built with [make_var]. 

*)

type var_id;;

val make_var : string -> var_id

(* Same as [make_var] but the generated name is prepended with unique number.*)

val make_var_uniq_name : string -> var_id

val var_name : var_id -> string

(*

\subsection{Abstract data type for expressions}

  [zero] is $0$, [one] is $1$, [(cte n)] is the constant $n$, [(var
  v)] is the variable [v], [(add e1 e2)] is $e_1+e_2$, [(sub e1 e2)]
  is $e_1-e_2$, [(minus e)] is $-e$, [(times n e)] is $ne$.

*)

type expr;;

val zero : expr;;
val one : expr;;
val minus_one : expr;;
val cte : Numbers.t -> expr;;
val var : var_id -> expr;;
val add_cte : expr -> Numbers.t -> expr;;
val add : expr -> expr -> expr;;
val sub : expr -> expr -> expr;;
val minus : expr -> expr;;
val times : Numbers.t -> expr -> expr;;
val div : expr -> Numbers.t -> expr;;

val is_cte : expr -> bool;;
val val_of_cte : expr -> Numbers.t;;

val get_coef : expr -> var_id -> Numbers.t;;
val remove_coef : expr -> var_id -> expr;;


(*

  [common_denominator e] returns the least common multiple of
  denominators in [e].

*)

val common_denominator : expr -> Numbers.t;;

(*

*)

module VarMap : Inttagmap.IntTagMapModule 
  with type 'a key = var_id;;

type substitution = (unit,expr) VarMap.t;;

(*

\subsection{Abstract data type for formulas}

Formulas are hashconsed for efficiency. All formulas should be build
using given constructor below.

The internal structure is exported for pattern-matching purpose only.

*)

type formula = formula_struct Hcons.hash_consed

and formula_struct = 
  | True 
  | False
  | Null of expr            
  | PositiveOrNull of expr            
  | Divisible of expr * Numbers.t
  | And of substitution * formula_struct Ptset.t
  | Or of formula_struct Ptset.t
  | Not of  formula
  | Implies of formula * formula
  | Equiv of formula * formula
  | Exists of var_id list * formula
  | Forall of var_id list * formula
;;


(*

  \subsection{Atomic formulas}
  
  [(eq e1 e2)] is $e_1=e_2$, 
  [(ne e1 e2)] is $e_1\neq e_2$, 
  [(ge e1 e2)] is $e_1\geq e_2$, 
  [(gt e1 e2)] is $e_1>e_2$, 
  [(le e1 e2)] is $e_1\leq e_2$, 
  [(lt e1 e2)] is $e_1<e_2$. 
  
  [(divides n e)] is $n$ divides $e$, where $n$ should be non null.
  
*)

val true_formula : formula;;
val false_formula : formula;;

val null : expr -> formula;;
val positive : expr -> formula;;
val positive_or_null : expr -> formula;;
val negative : expr -> formula;;
val eq : expr -> expr -> formula;;
val ne : expr -> expr -> formula;;
val ge : expr -> expr -> formula;;
val gt : expr -> expr -> formula;;
val le : expr -> expr -> formula;;
val lt : expr -> expr -> formula;;
val divides : Numbers.t -> expr -> formula;;

val is_atom : formula -> bool;;

(*

  \subsection{Propositional connectors}

*)


(*

  [hash_disj s] (resp. [hash_conj]) builds the disjunction (resp
  conjunction) of formulas in [s], assuming they are already hash
  consed.

  these functions take in account the basic cases where [s] is empty
  or has only one elements.

*)

val hash_disj : formula_struct Ptset.t -> formula;;

val hash_conj : substitution -> formula_struct Ptset.t -> formula;;

(*

  [neg f] builds $\neg f$, [conj f1 f2] builds $f1\wedge f2$, [disj f1
  f2] builds $f1\vee f2$. [conj_list l] builds the conjunct of all
  formulas in list [l], [disj_list l] builds the disjunct of all
  formulas in list [l]. [implies f1 f2] builds [f1\rightarrow f2], [equiv
  f1 f2] builds $f1\leftrightarrow f2$.

*)

val neg : formula -> formula;;
val conj : formula -> formula -> formula;;
val disj : formula -> formula -> formula;;
val conj_list : formula list -> formula;;
val disj_list : formula list -> formula;;
val implies : formula -> formula -> formula;;
val equiv : formula -> formula -> formula;;

(*

  \subsection{Iterators for conjunction and disjunction}

  [map_conj_subst f sigma s] computes 
  $$  % $ for camlweb
  \bigwedge_{x=e\in [sigma]} f (x=e) \wedge \bigwedge_{h\in [s]} f s
  $$  % $ for camlweb

  [map_conj_no_subst f sigma s] computes 
  $$  % $ for camlweb
  \bigwedge_{x=e\in [sigma]} x=e \wedge \bigwedge_{h\in [s]} f s
  $$  % $ for camlweb

  [map_disj_set f s] computes 
  $$  % $ for camlweb
  \bigvee_{h\in [s]} f s
  $$  % $ for camlweb

*)

val map_conj_subst :
  (formula -> formula) -> substitution -> formula_struct Ptset.t -> formula 

val map_conj_no_subst :
  (formula -> formula) -> substitution -> formula_struct Ptset.t -> formula 

val map_disj_set : 
  (formula -> formula) -> formula_struct Ptset.t -> formula 
;;

(*


  \subsection{Quantifiers}

  [exists x f] builds formula $\exists x.f$.  [forall x f] builds
  formula $\forall x.f$.

*)

val exists : var_id -> formula -> formula;;
val forall : var_id -> formula -> formula;;

val exists_s : var_id list -> formula -> formula;;
val forall_s : var_id list -> formula -> formula;;



(*

  \subsection{Translation from abstract formulas}

  [from_abstract_formula f] builds the linear formula from the
  abstract formula [f]. returns also first the environment of free
  variables.  Raises [Not_linear] of [f] is not linear.

*)

exception Not_linear;;

type var_env = (string * var_id) list;;

val from_abstract_expr : 
  var_env -> Abstract_constraint.expr -> var_env * expr;;

val from_abstract_formula : 
  var_env -> Abstract_constraint.formula -> var_env * formula;;


(*

  \subsection{Free vars of formula}

  [free_vars f] returns the list of free variables of [f]

  [free_vars_env s f] returns the union of s and the list of free
  variables of [f]

*)

val free_vars : formula -> var_id list

val free_vars_env : var_id list -> formula -> var_id list

val var_occurs : var_id -> formula -> bool

(*


  \subsection{Instanciation, substitution}

  [inst f x n] returns the formula obtained by replace the variable [x]
  by number [n] in [f].
  
  [subst f x e] returns the formula obtained by substituting the
  variable [x] by expression [e] in [f].

*)


type instantiation = (unit,Numbers.t) VarMap.t;;

val inst1 : var_id -> Numbers.t -> formula -> formula;;

val subst1 : var_id -> expr -> formula -> formula;;

val inst : instantiation -> formula -> formula;;

val subst : substitution -> formula -> formula;;

(*

  \subsection{Renaming}

*)

(* Type of the renaming tables *)

type var_renaming = (unit,var_id) VarMap.t

(* Rename all variables in a formula. *)
val rename_formula :  var_renaming -> formula -> formula

(* Rename all variables in an expression.*)
val rename_expr : var_renaming -> expr -> expr

(* [build_renaming l] builds a fresh renaming for the variables of
   [l]. *) 
 
val build_renaming : var_id list -> var_renaming


(*

  \subsection{Printing}

  [(print f)] prints the formula [f] on [Format.std_formatter] channel.

*)

val fprint_expr : Format.formatter -> expr -> unit;;
val print_expr : expr -> unit;;
val fprint : Format.formatter -> formula -> unit;;
val print : formula -> unit;;


(*

*)

val remove_denominators : formula -> formula;;

