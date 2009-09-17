open Names;;
open Sign;;
open Util;;
open Term;;
open Pp;;
open Libobject;;
open Library;;
open Vernacinterp;;
open Tacmach;;
open Pfedit;;
open Parsing;;
open Evd;;
open Evarutil;;

open Xlate;;
open Vtp;;
open Ascent;;
open Environ;;
open Proof_type;;

(*translates a formula into a centaur-tree --> FORMULA *)
let translate_constr at_top env c =
  xlate_formula (Constrextern.extern_constr at_top env c);;

(*translates a named_context into a centaur-tree --> PREMISES_LIST *)
(* this code is inspired from printer.ml (function pr_named_context_of) *)
let translate_sign env =
  let l =
    Environ.fold_named_context
      (fun env (id,v,c) l ->
	 (match v with
	      None ->
	       	CT_premise(CT_ident(string_of_id id), translate_constr false env c)
	    | Some v1 ->
		CT_eval_result
		  (CT_coerce_ID_to_FORMULA (CT_ident (string_of_id id)),
		   translate_constr false env v1,
		   translate_constr false env c))::l)
      env ~init:[]
  in
  CT_premises_list l;;

(* the function rev_and_compact performs two operations:
   1- it reverses the list of integers given as argument
   2- it replaces sequences of "1" by a negative number that is
      the length of the sequence. *)
let rec rev_and_compact l = function
    [] -> l
  | 1::tl ->
      (match l with
              n::tl' ->
        if n < 0 then
          rev_and_compact ((n - 1)::tl') tl
        else
          rev_and_compact ((-1)::l) tl
      |       [] -> rev_and_compact [-1] tl)
  | a::tl ->
      if a < 0 then
      (match l with
        n::tl' ->
          if n < 0 then
            rev_and_compact ((n + a)::tl') tl
          else
            rev_and_compact (a::l) tl
      | [] -> rev_and_compact (a::l) tl)
      else
      rev_and_compact (a::l) tl;;

(*translates an int list into a centaur-tree --> SIGNED_INT_LIST *)
let translate_path l =
 CT_signed_int_list
 (List.map (function n -> CT_coerce_INT_to_SIGNED_INT (CT_int n))
    (rev_and_compact [] l));;

(*translates a path and a goal into a centaur-tree --> RULE *)
let translate_goal (g:goal) =
 CT_rule(translate_sign (evar_env g), translate_constr true (evar_env g) g.evar_concl);;

let translate_goals (gl: goal list) =
 CT_rule_list (List.map translate_goal gl);;
