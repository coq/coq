(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Positions
open Signatures
open Variables

type 'symbol term = 
  | Term of 'symbol * 'symbol term list
  | Var of var_id
;;


let rec leftify_term = function
    Term (f,l) -> Term (f,List.map leftify_term l)
  | Var x -> Var (leftify_var x)

let rec rightify_term = function
    Term (f,l) -> Term (f,List.map rightify_term l)
  | Var x -> Var (rightify_var x)

(*

  [(root_symbol t)] returns the root symbol of [t], raises [Not_found]
  if [t] is a variable

*)

let root_symbol = function
    Var(_) -> raise Not_found
  | Term(f,_) -> f
;;

let rec flatten_term_list f = function
  [] -> []
| (Term(g,l) as t)::m -> 
    if g=f
    then l @ (flatten_term_list f m)
    else t::(flatten_term_list f m)
| v::m -> 
    v::(flatten_term_list f m);;

let head_flatten sigma f l =
  if sigma#is_ac f
      then Term(f,(flatten_term_list f l))
      else Term(f,l)
;;

let head_flatten_term sigma = function
    Term(f,l) as t -> 
      if sigma#is_ac f
      then Term(f,(flatten_term_list f l))
      else t
  | v -> v
;;

let rec flatten_term sigma = function
    Term(f,l) ->
      head_flatten sigma f (List.map (flatten_term sigma) l)
  | v -> v
;;


(*

  [(make_term sigma f l)] builds the term whose top symbol is [f] and
  list of subterms from left to right is [l]. Verifies the
  compatibility with the arity of [f] as given in [sigma]. Raises
  [Bad_arity "f"] in case of incompatibility.

  To avoid this tests for efficiency, simply use [Term] directly,
  together with [flatten_term]

*)


exception Bad_arity of string;;


let make_term sigma f l =
  if sigma#is_ac f & List.length l >= 2
    or sigma#arity f = List.length l
  then head_flatten_term sigma (Term(f,l))
  else raise (Bad_arity (sigma#string_of_symbol f))
;;


let rec make_term_from_string_term sigma t =
  match t with
    | Term(f,l) -> 
	let g = sigma#symbol_of_string f in
	make_term sigma g (List.map (make_term_from_string_term sigma) l)
    | Var x ->  Var x
;;


(*
  
  [(subterm_at_position p t)] returns the subterm of the term [t] at the
  position [p].
  
*)

exception No_subterm;;

let rec subterm_at_position p t =
  match p with
      Top -> t
    | Pos (i,p') -> 
	match t with
	    Var _ -> raise No_subterm
	  | Term (_,l) ->
	      begin
		try
		  let t' = List.nth l i in
		    subterm_at_position p' t'
		with Failure "nth" -> raise No_subterm
	      end


let rec replace_subterm_at_position_in_term u p t =
  match p with
      Top -> u
    | Pos (i,p') ->
	begin
	  match t with
	      Var _ -> raise No_subterm
	    | Term (f,l) -> 
		let l' = 
		  Listutils.mapi 
		    (fun n s -> 
		       if n=i 
		       then replace_subterm_at_position_in_term u p' s
		       else s) 
		    l in
		  Term (f,l')
	end

(*

  [(set_of_symbols t)] returns the set of symbols occuring in [t]

*)

let rec set_of_symbols = function
    Var(x) -> SymbolSet.empty
  | Term(f,l) ->
      SymbolSet.add f
      	(List.fold_left
	   (fun s t ->
	      SymbolSet.union s (set_of_symbols t))
	   SymbolSet.empty
	   l)
;;



let rec set_of_variables = function
    Var x -> VarSet.add x VarSet.empty
  | Term (_,l) ->
      List.fold_left
	(fun s t -> VarSet.union s (set_of_variables t))
	VarSet.empty
	l

let rec var_occurs_in_term x t = 
  match t with
    | Var y -> x=y
    | Term(_,l) -> var_occurs_in_term_list x l

and var_occurs_in_term_list x l = 
  match l with
    | [] -> false
    | s::l -> 
	if var_occurs_in_term x s 
	then true 
      	else var_occurs_in_term_list x l

let check_for_right_regularity t1 t2 =
  let vars_of_t1 = set_of_variables t1
  and vars_of_t2 = set_of_variables t2 in
    VarSet.filter 
      (function v2 -> not (VarSet.mem v2 vars_of_t1))
      vars_of_t2

let build_a_term_for_a_right_regular_pair a t1 t2 =
  let vars_of_t1 = set_of_variables t1
  and vars_of_t2 = set_of_variables t2 in
  let vars =  check_for_right_regularity t1 t2 in
    if (VarSet.is_empty vars)
    then raise Exit
    else
      let rec substitute = function
	  Var y as var_y -> if VarSet.mem y vars then a else var_y
	| Term(f,l) -> Term(f,List.map substitute l) in
	substitute t2;;

let rec size sigma = function
    Var x -> 1
  | Term(f,l) ->
      let size_of_l = 
	List.fold_left
	  (fun s t -> s + (size sigma t)) 0 l in
	if sigma#is_ac f
	then (pred (List.length l)) + size_of_l
	else 1 + size_of_l

let rec compare_terms t1 t2 =
  match (t1,t2) with
    | (Term(f1,l1),Term(f2,l2)) ->
        let x = Pervasives.compare f1 f2 in
        if x<>0 then x
	else 
          let rec compare_lists l1 l2 = 
	    match l1,l2 with
	      | ([],[]) -> 0
	      | ([],_) -> 1
	      | (_,[]) -> -1
	      | (s1::l1,s2::l2) -> 
		  let x = compare_terms s1 s2 in
		  if x<>0 then x
		  else compare_lists l1 l2
	  in compare_lists l1 l2 
    | (Var _,Term _) -> 1
    | (Term _ ,Var _) -> -1
    | (Var x1,Var x2) -> Pervasives.compare x1 x2
;;

let rec sort_term sigma t = 
  match t with
    | Var _ -> t
    | Term(f,l) -> 
	let ls = List.map (sort_term sigma) l in
	if sigma#is_free f
        then Term(f,ls)
        else Term(f,List.sort compare_terms ls)
;;

let rec equals sigma t1 t2 =
  match t1,t2 with
    | (Var x1,Var x2) -> x1=x2
    | (Var _,Term _) -> false
    | (Term _,Var _) -> false
    | (Term(f1,l1),Term(f2,l2)) ->
	if f1<>f2 or List.length l1<>List.length l2
	then false
	else
	  if sigma#is_free f1
	  then List.for_all2 (equals sigma) l1 l2
	  else
	    (sort_term sigma t1)=(sort_term sigma t2)
;;

(*


[(print_term sigma t)] prints to standard output the term [t] over the
signature [sigma].

*)

open Format;;
open Signature_syntax;;

let print_term sigma vars t = 

  let rec print_term_rec is_deep = function
      Term(f,[]) ->
      	print_string (sigma#string_of_symbol f);
    | Term(f,t::l) ->
	open_box 0;
	begin
	  match sigma#symbol_fix f with
	      Default | Prefix ->
	      	begin
      	      	  print_string (sigma#string_of_symbol f);
      		  print_string "(";
      		  print_term_rec false t;
      		  print_end_term_list l
	      	end
	    | Postfix ->
	      	begin
      		  print_string "(";
      		  print_term_rec false t;
      		  print_end_term_list l;
      	      	  print_string (sigma#string_of_symbol f);
	      	end
	    | Infix ->
	      	begin
		  if is_deep then print_string "(";
		  print_term_rec true t;
      		  print_infix_list f l;
		  if is_deep then print_string ")"
	      	end
	end;
	close_box();
    | Var(x) ->
	print_string (vars#string_of_var x)
	  
  and print_end_term_list = function
      [] -> 
      	print_string ")"
    | t::l ->
      	print_string ",";
      	print_term_rec false t;
      	print_end_term_list l
	  
  and print_infix_list f = function
      [] -> ()
    | t::l ->
	print_string " ";
      	print_string (sigma#string_of_symbol f);
	print_string " ";
      	print_term_rec true t;
      	print_infix_list f l
	  
  in
    print_term_rec false t
;;


let print_equation sigma vars (s,t) =
  printf "@[<hov>";
  print_term sigma vars s;
  printf "@ =@ ";
  print_term sigma vars t;
  printf "@]"
;;
  
let print_equation_list sigma vars = function
    []   -> (print_string "{}")
  | r::l ->
      let rec print_end_list n = function
	  [] -> 
	    begin
              print_string " }";
              print_break 1 0;
              print_string "(";
              print_int n;
              print_string " equation(s))"                 
	    end
	| (r::l) -> 
	    begin
              print_string  ",";
              force_newline ();
              print_equation sigma vars r;
              print_end_list (succ n) l
            end
      in 
	begin
	  print_string "{ ";
	  open_hovbox 0;
	  print_equation sigma vars r;
	  print_end_list 1 l;
	  close_box ()
	end
;;

 
