(***************************************************************************

This module provides an abstract data type for first-order variables. 

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



(*

  This module provides an abstract data type for first-order
  variables. In an abstract point of view, a set of variables is any
  set equipped with total order (an equality is enough in theory, but
  we require a total order because we want to provide efficient
  implementation of finite sets of variables and finite maps indexed
  by variables. Finally a set of variables have to be infinite: it is
  always possible to find a variable that do not belong to a given
  finite set.

  Variables have no readable representation by default. If you need a
  set of variables where some variables have a ``name'', for user
  interaction purpose, you can use the class [user_variables].

*)


(*

  [var_id] is the abstract type for a variable.

  [string_of_var_id x] displays a variable identifier in a raw
  way. The result is not supposed to be parse again. Mainly for
  debugging purpose. See [user_variables] class below for a better way
  of printing variable ids.

*)

type var_id;;

val string_of_var_id : var_id -> string;;

val leftify_var : var_id -> var_id

val rightify_var : var_id -> var_id

(*

  [VarOrd] is a module that provides a total order on variables.

*)

module VarOrd : Ordered_types.OrderedType with type t = var_id;;

(*

  [VarSet] is a module that provides finite sets of variables.

*)

module VarSet : Ordered_sets.OrderedSet with type 'a elt = var_id;;

(*

  [VarMap] is a module that provides finite maps indexed by variables.

*)

module VarMap : Inttagmap.IntTagMapModule with type 'a key = var_id;;


val canonical_renaming : var_id VarSet.t -> (unit,var_id) VarMap.t

(*

  [(fresh_variables n)] returns a list of [n] variables. Here, the
  word ``fresh'' does not means anything else that these are [n]
  distinct variables. Use the next function if you need to obtain a
  variable distinct from some others.

*)

val fresh_variables : int -> var_id list;;

(*

  [(var_outside_set s)] returns a variable that do not belong to the set [s].

*)

val var_outside_set : var_id VarSet.t -> var_id;;


(*

  [(init_for_unif s)] initializes the set of variables for unification.
  The intended meaning of [s] is the set of variables occurring in the
  initial unification problem.

*)

val init_for_unif : var_id VarSet.t -> unit;;



(* 

   [fresh_var_for_unif ()] generates a variable at each call.  In a
   session starting by a call to [(init_for_unif s)], these variables
   are pairwise distinct, and do not occur in [s].

*)

val fresh_var_for_unif : unit -> var_id;;

val print_unif_var : var_id -> unit

(* 

   [(user_variables l)] returns an object that provides two functions
   for converting a variable into a readable name and vice-versa. [l]
   is a list of strings that give a list of name that you would like
   to use. Example : 
   \begin{verbatim} 
     let my_vars = new Variables.from_string "x y z"
   \end{verbatim}

*)

exception Syntax_error of string;;

(*

  [(var_of_string s)] returns the variable whose name is [s]. Raises
  exception [Not_found] is no variable corresponds.

*)

class type user_variables =
object
  method string_of_var : var_id -> string 
  method var_of_string : string -> var_id
    (*i
      method print_all : unit -> unit
      i*)
end;;

val from_list : string list -> user_variables;;

val from_string : string -> user_variables;;

val default : user_variables;;
