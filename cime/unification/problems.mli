(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Signatures
open Variables
open Gen_terms
open Theory


module UnifElemThMap : Ordered_maps.OrderedMap 
  with type 'a key = 'a unif_elem_theory

type status =
    Unsolved
  | Merged
  | Marked
  | Solved

type 'symbol mark = 
    No_mark
  | Erasable
  | Permanent of 'symbol elem_theory

type 'symbol elem_pb = 
    {
      key : 'symbol unif_elem_theory;
      status : status;
      size : int option;
      elem_th : 'symbol elem_theory;
      inst_variables : (unit, 'symbol term) VarMap.t;
      marked_variables : (unit, 'symbol mark) VarMap.t;
      edges : (var_id * var_id) list;
      equations : ('symbol term * 'symbol term) list
    }

type 'symbol problem =
    {
      unif_kind : unif_kind;
      global_status : status;
      sign : 'symbol signature;
      find_th : 'symbol -> 'symbol unif_elem_theory;
      vars_for_eqe : var_id VarSet.t;
      first_vars : var_id VarSet.t;
      var_var : (unit,var_id) VarMap.t;
      elem_pbs : ('symbol, 'symbol elem_pb) UnifElemThMap.t;
      solved_part : ('symbol term * 'symbol term) list
    }

val print_elem_pb :
  'symbol #signature -> Variables.user_variables -> 'symbol elem_pb -> unit

val print_problem : 
  'symbol #signature -> Variables.user_variables -> 'symbol problem -> unit

val replace_a_var_by_a_var_in_an_eq : 
  var_id -> var_id -> ('symbol term * 'symbol term) -> 
    ('symbol term * 'symbol term)


val add_an_equation_between_variables :
  'symbol problem -> var_id -> var_id -> 'symbol problem


val init : 
  unif_kind -> 'symbol #signature -> ('symbol -> 'symbol unif_elem_theory) ->
    'symbol term -> 'symbol term -> 
      'symbol problem 



val insert_solved_elem_pbs : 
  'symbol #signature -> (*i user_variables -> i*) 
    'symbol problem -> 
      'symbol unif_elem_theory -> 
	('symbol term * 'symbol term) list list -> 
	  'symbol problem list
