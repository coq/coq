open Names;;
open Sign;;
open Util;;
open Ast;;
open Term;;
open Pp;;
open Libobject;;
open Library;;
open Vernacinterp;;
(* dead code: open Proof_trees;; *)
open Termast;;
open Tacmach;;
open Pfedit;;
open Parsing;;
open Evd;;
open Evarutil;;

open Xlate;;
open Ctast;;
open Vtp;;
open Ascent;;
open Environ;;
open Proof_type;;

(* dead code: let rel_reference gt k oper = 
 if is_existential_oper oper then ope("XTRA", [str "ISEVAR"])
 else begin
  let id = id_of_global oper in
  let oper', _ = global_operator (Nametab.sp_of_id k id) id in
  if oper = oper' then nvar (string_of_id id)
  else failwith "xlate"
end;;
*)

(* dead code: 
let relativize relfun =
 let rec relrec =
  function
     | Nvar (_, id) -> nvar id
     | Slam (l, na, ast) -> Slam (l, na, relrec ast)
     | Node (loc, nna, l) as ast -> begin
       try relfun ast
       with
       | Failure _ -> Node (loc, nna, List.map relrec l)
     end
     | a -> a in
 relrec;;
*)

(* dead code:
let dbize_sp =
 function
    | Path (loc, sl, s) -> begin
      try section_path sl s
      with
      | Invalid_argument _ | Failure _ ->
      anomaly_loc
       (loc, "Translate.dbize_sp (taken from Astterm)",
       [< str "malformed section-path" >])
    end
    | ast ->
     anomaly_loc
      (Ast.loc ast, "Translate.dbize_sp (taken from Astterm)",
      [< str "not a section-path" >]);;
*)

(* dead code:
let relativize_cci gt = relativize (function
    | Node (_, "CONST", (p :: _)) as gt ->
     rel_reference gt CCI (Const (dbize_sp p))
    | Node (_, "MUTIND", (p :: ((Num (_, tyi)) :: _))) as gt ->
     rel_reference gt CCI (MutInd (dbize_sp p, tyi))
    | Node (_, "MUTCONSTRUCT", (p :: ((Num (_, tyi)) :: ((Num (_, i)) :: _)))) as gt ->
     rel_reference gt CCI (MutConstruct (
      (dbize_sp p, tyi), i))
    | _ -> failwith "caught") gt;;
*)

let coercion_description_holder = ref (function _ -> None : t -> int option);;

let coercion_description t = !coercion_description_holder t;;

let set_coercion_description f =
 coercion_description_holder:=f; ();;

let rec nth_tl l n = if n = 0 then l
 else (match l with
 | a :: b -> nth_tl b (n - 1)
 | [] -> failwith "list too short for nth_tl");;

let rec discard_coercions =
 function
    | Slam (l, na, ast) -> Slam (l, na, discard_coercions ast)
    | Node (l, ("APPLIST" as nna), (f :: args as all_sons)) ->
     (match coercion_description f with
     | Some n ->
      let new_args =
       try nth_tl args n
       with
       | Failure "list too short for nth_tl" -> [] in
      (match new_args with
       | a :: (b :: c) -> Node (l, nna, List.map discard_coercions new_args)
       | a :: [] -> discard_coercions a
       | [] -> Node (l, nna, List.map discard_coercions all_sons))
     | None -> Node (l, nna, List.map discard_coercions all_sons))
    | Node (l, nna, all_sons) ->
     Node (l, nna, List.map discard_coercions all_sons)
    | it -> it;;

(*translates a formula into a centaur-tree --> FORMULA *)
let translate_constr assumptions c =
 let com = ast_of_constr true assumptions c in
(* dead code:  let rcom = relativize_cci (discard_coercions com) in *)
 xlate_formula (Ctast.ast_to_ct com) (* dead code: rcom *);;

(*translates a named_context into a centaur-tree --> PREMISES_LIST *)
(* this code is inspired from printer.ml (function pr_named_context_of) *)
let translate_sign env =
  let l = 
    fold_named_context
      (fun env (id,v,c) l -> 
	 (CT_premise(CT_ident(string_of_id id), translate_constr env c))::l)
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
 CT_rule(translate_sign (evar_env g), translate_constr (evar_env g) g.evar_concl);;
