

open Signatures
open Variables
open Gen_terms
open Lazy_list
open Lazy_controle

type 'symbol protect_var_sig =
 | Original of 'symbol
 | Protected_var of Variables.var_id 
;;

(*
class ['symbol] protected_signature (orig_sig) =
  object

    val original_sig = (orig_sig : 'symbol #Signatures.signature)
			 
    method arity (f : 'symbol protect_var_sig) = 
      match f with
	| Original f -> original_sig#arity f
	| Protected_var _ -> 0
	      
    method is_ac (f : 'symbol protect_var_sig) = 
      match f with
	| Original f -> original_sig#is_ac f
	| Protected_var _ -> false
	      
    method is_commutative (f : 'symbol protect_var_sig) = 
      match f with
      	| Original f -> original_sig#is_commutative f
	| Protected_var _ -> false
	      
    method is_free (f : 'symbol protect_var_sig) = 
      match f with
      	| Original f -> original_sig#is_free f
	| Protected_var _ -> true
	
    method contains_ac_symbols = original_sig#contains_ac_symbols

    method contains_only_free_symbols = original_sig#contains_only_free_symbols

    method string_of_symbol (f : 'symbol protect_var_sig) = 
      match f with
      	| Original f -> original_sig#string_of_symbol f
	| Protected_var x -> Variables.string_of_var_id x
	      
    method symbol_fix (f : 'symbol protect_var_sig) = 
      match f with
	| Original f -> original_sig#symbol_fix f
	| Protected_var _ -> Signatures.Prefix

    method smallest_constant o = 
      let c = 
	original_sig#smallest_constant 
	  (fun f g -> o (Original f) (Original g)) in
	    (Original c)
  end
*)

let rec protect_var_and_sort sign t = 
(*i
  let _ = Format.print_string "toto"; Format.print_newline (); Format.print_flush () in
i*)
  match t with
    | Var(x) -> Term(Protected_var x,[])
    | Term(f,l) -> 
	let ls = List.map (protect_var_and_sort sign) l in
	  if sign#is_free f
	  then Term(Original f, ls)
	  else Term(Original f, List.sort compare_terms ls)


let rec simple_copy_and_sort sign t = 
  match t with
    | Var x as var_x -> var_x
    | Term(f,l) -> 
	let ls = List.map (simple_copy_and_sort sign) l in
	  if sign#is_free f
	  then Term(Original f, ls)
	  else Term(Original f, List.sort compare_terms ls)


let rec unprotect t =
  match t with
    | Var _ -> assert false
    | Term(Original f,l) -> 
	Term(f,List.map unprotect l)
    | Term(Protected_var x,[]) ->
	Var x
    | _ -> assert false


exception No_match;;

type 'symbol problem =
    {
      (*i
	clef : int list;
      i*)
      unsolved_part : ('symbol term * 'symbol term) list;
      solved_part : 'symbol Substitution.substitution;
    }

let print_pb sign pb =
(*i
  Printf.printf "clef = ";
  List.iter (function i -> Printf.printf " %d;" i) pb.clef;
  Printf.printf "\n";
i*)
  Printf.printf "solved equations =\n";
  Substitution.print sign default pb.solved_part;
  Printf.printf "unsolved equations =\n";
  List.iter
    (fun (s,t) ->
       print_term sign default s;
       Format.print_flush ();
       Printf.printf " = ";
       print_term sign default t;
       Format.print_flush ();
       Printf.printf "\n")
    pb.unsolved_part


let rec remove a = function
    [] -> raise Not_found
  | b::l -> if a = b then l else b::(remove a l)

let one_level_sort_term sign t =
  match t with 
    | Term ((Original f as original_f),l) as t -> 
	if sign#is_free f
	then t
	else Term (original_f, List.sort compare_terms l)
    | _ -> t


let rec substitute sign subst t = 
  match t with
    | Var id -> 
	begin
	  try 
	    Variables.VarMap.find id subst
	  with Not_found -> t
	end
    | Term ((Protected_var _),[]) -> t
    | Term ((Original f as original_f),l) -> 
	if sign#is_ac f 
	then
	  let reverted_list_of_substituted_subterms = 
	    List.fold_left
	      (fun acc x -> 
		 let x_subst = substitute sign subst x in
		   begin
		     match x_subst with 
			 Term (s,l2) -> 
			   if s = original_f then l2 @ acc else x_subst :: acc
		       | Var _ -> x_subst::acc
		   end)
	      [] l in
	    Term(original_f,List.rev reverted_list_of_substituted_subterms) 

	else Term(original_f, List.map (substitute sign subst) l)
    | _ -> assert false
;;

let apply_subst_to_match_eq sign subst (s,t) =
  (one_level_sort_term sign (substitute sign subst s), t)

let apply_subst_to_match_eqs sign subst = 
  List.map (apply_subst_to_match_eq sign subst)

let solve sign pb =
(*i
  let _ = 
    Format.print_string "solve est appele sur le probleme";
    Format.print_newline();
    print_pb sign pb
  in
i*)
  match pb.unsolved_part with
      [] -> raise Not_appliable

    | (Var x,t) :: list_of_equations ->
	let x_mapsto_t = VarMap.add x t VarMap.empty in
	let new_pb =
	  {
	    (*i
	    clef = pb.clef @ [1];
	    i*)
	    unsolved_part = 
	     apply_subst_to_match_eqs sign x_mapsto_t list_of_equations;
	    solved_part = 
	     VarMap.add x t 
	       (VarMap.map 
		  (substitute sign x_mapsto_t) 
		  pb.solved_part)
	  } in
	  Cons {head = new_pb; tail = Val Nil}

    | (Term ((Protected_var x as protected_x),[]) ,Term (f',l')) :: list_of_equations ->
	if protected_x <> f'
	then raise No_solution
	else 
	  let _ = assert (l' = []) in
	  let new_pb = 
	    {
	      unsolved_part = list_of_equations;
	      solved_part = pb.solved_part;
	    } in
	    Cons {head = new_pb; tail = Val Nil}

    | (Term ((Original f as original_f),l), Term (f',l')) :: list_of_equations ->
	if original_f <> f'
	then raise No_solution
	else 
	  if sign#is_free f
	  then 
	    let new_pb =
	      try
		{
		  (*i
		  clef = pb.clef @ [1];
		  i*)
		  unsolved_part = 
		   List.fold_left2
		     (fun current_list_of_eqs s t -> 
			(s,t)::current_list_of_eqs)
		     list_of_equations l l';
		  solved_part = pb.solved_part;
		} 
	      with 
		  Invalid_argument "List.fold_left2" -> raise No_solution in
	      Cons {head = new_pb; tail = Val Nil}
	  else 
	    if sign#is_ac f
	    then 
	      begin
		if (List.length l) > (List.length l')
		then raise No_solution
		else 
		  match l with
		      (Term (g,_) as s) :: list_of_terms ->
			begin
			  (*i
			  let cmpt = ref 0 in
			  i*)
			  Lazy_list.map
			    (function t ->
			       match t with
				   Var _ -> assert false
				 | Term (h,_) ->
				     if g = h
				     then 
				       let s' = Term (original_f, list_of_terms)
				       and l'_without_t = remove t l' in
				       let t' = Term (original_f,l'_without_t) in  
					 {
					   (*i
					   clef = (let _ = cmpt := !cmpt + 1 in
					     pb.clef @ [!cmpt]);
					   i*)
					   unsolved_part = 
					    (s,t)::(s',t')::list_of_equations;
					   solved_part = pb.solved_part;
					 }
				     else raise Exit) 
			    l' 
			end
		    | (Var _) :: list_of_terms  ->
			(begin
			   (*i
			   let cmpt = ref 0 in
			   i*)
			   match l' with 
			       t :: l'' ->
				 Lazy_list.map2_without_repetition
				   (function v ->
				      match v with
					  Var x ->
					    let y = fresh_var_for_unif () in
					    let y_plus_t = 
					      Term (original_f, [(Var y);t]) in
					    let x_mapsto_t =
					      VarMap.add x t VarMap.empty 
					    and x_mapsto_y_plus_t =
					      VarMap.add x y_plus_t VarMap.empty in
					    let l_without_v = remove v l in		
					    let new_pb =
					      {
						(*i
						clef = (let _ = cmpt := !cmpt + 1 in
						  pb.clef @ [!cmpt]);
						i*)
						unsolved_part =
						 begin
						   let new_list_of_equations =
						     (Term (original_f,l_without_v),Term (original_f,l'')) ::
						     list_of_equations in
						     apply_subst_to_match_eqs sign x_mapsto_t 
						       new_list_of_equations
						 end;
						solved_part = 
						 VarMap.add x t
						   (VarMap.map 
						      (substitute sign x_mapsto_t) 
						      pb.solved_part)
					      }
					    and  new_pb' =
					      {
						(*i
						clef = (let _ = cmpt := !cmpt + 1 in
						  pb.clef @ [!cmpt]);
						i*)
						  unsolved_part =
						 begin
						   let new_list_of_equations =
						     (Term (original_f,(Var y)::(remove v l)), 
						      Term (original_f,l'')) :: list_of_equations in
						     apply_subst_to_match_eqs sign x_mapsto_y_plus_t 
						       new_list_of_equations
						 end;
						solved_part = 
						 VarMap.add x y_plus_t
						   (VarMap.map (substitute sign x_mapsto_y_plus_t) 
						      pb.solved_part)
					      } in
					      (new_pb, new_pb')
					   
					| Term _ -> assert false)
				   l 
			     | [] -> Nil 
			 end)
		    | [] -> 
			if l' <> []
			then raise No_solution
			else 
			  let new_pb = 
			    {
			      (*i
			      clef = pb.clef @ [1];
			      i*)
			      unsolved_part = list_of_equations;
			      solved_part = pb.solved_part;
			    } in
			    Cons {head = new_pb; tail = Val Nil}
	      end
	    else (*i sign#is_commutative f i*)
	      begin
		match l,l' with
		    [s1;s2], [t1;t2] ->
		      let new_pb1 =
			{
			  (*i
			  clef = pb.clef @ [1];
			  i*)
			  unsolved_part = (s1,t1)::(s2,t2)::list_of_equations;
			  solved_part = pb.solved_part;
			}
		      and new_pb2 =
			{
			  (*i
			  clef = pb.clef @ [2];
			  i*)
			  unsolved_part = (s1,t2)::(s2,t1)::list_of_equations;
			  solved_part = pb.solved_part;
			} in 
			Cons {head = new_pb1; 
			      tail = Val (Cons {head = new_pb2; tail = Val Nil})}
			  
		  | _,_ -> assert false
	       end

    | (Term _, Var _) :: _ -> assert false
    | (Term (Protected_var _, _::_),_) :: _ -> assert false
	      

let matching sign t1 t2 = 
(*i
  let _ = 
    begin
      Format.print_string "matching sur ";
      Gen_terms.print_term sign default t1;
      Format.print_string " = ";
      Gen_terms.print_term sign default t2;
      Format.print_newline();
      Format.print_flush () 
    end in
i*)    
    let t1' = simple_copy_and_sort sign t1
    and t2' = protect_var_and_sort sign t2 in
    let vars_of_t1 = (set_of_variables t1) in
    let _ = init_for_unif vars_of_t1 in
    let init_pb = 
      {
	(*i
	clef = [];
	i*)
	unsolved_part = [t1',t2'];
	solved_part = VarMap.empty
      } in
    let list_of_solutions =
    repeat (solve sign) init_pb in
    try 
      let solved_pb = Lazy_list.hdl list_of_solutions in
      let sol = Variables.VarMap.map unprotect solved_pb.solved_part in
(*i
      let _ = 
	begin
	  if sol = Variables.VarMap.empty
	  then 
	    begin
	      Format.print_string "{}";
	      Format.print_newline()
	    end
	  else Substitution.print sign default sol;
	  Format.print_flush ()
	end in
i*)
	sol
    with
	Failure "hdl" -> 
	  begin 
(*i
	    Format.print_string "no solution";
	    Format.print_newline();
	    Format.print_flush ();
i*)
	    raise No_match 
	  end

let all_matchs sign vars t1 t2 =
    let t1' = simple_copy_and_sort sign t1
    and t2' = protect_var_and_sort sign t2 in
    let vars_of_t1 = (set_of_variables t1) in
    let _ = init_for_unif vars_of_t1 in
    let init_pb = 
      {
	unsolved_part = [t1',t2'];
	solved_part = VarMap.empty
      } in
    let list_of_solutions =
      repeat (solve sign) init_pb in
    let rec print_solved_pbs n = function
	Nil -> 
	  print_int n;
	  print_string " solutions";
	  print_newline()
      | Cons {head = solved_pb; tail = Val l} ->
	  let sol = Variables.VarMap.map unprotect solved_pb.solved_part in
(*
	    print_string "-------- solution ";
	    print_int n;
	    print_string " --------";
	    print_newline ();
	    Substitution.print sign vars sol;
*)
	    print_solved_pbs (n+1) l
      | Cons ({head = solved_pb; tail = Freeze th} as cell) ->
	  let sol = Variables.VarMap.map unprotect solved_pb.solved_part in
(*
	    print_string "-------- solution ";
	    print_int n;
	    print_string " --------";
	    print_newline ();
	    Substitution.print sign vars sol;
*)
	    let tail = th () in
	      cell.tail <- Val tail;
	      print_solved_pbs (n+1) tail in
      print_solved_pbs 0 list_of_solutions

