(***************************************************************************

  Boolean unification with Buttner-Simonis' algorithm.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

Obsolete header:

  CiME Project - Démons research team - LRI - Université Paris XI
  
  $Id$

***************************************************************************)

open Theory
open Variables
open Gen_terms
open Problems
open Substitution

(*
open Llist
open Symbols
open Terms
open Ac_rewriting
open Type_de_donnees
open Theorie
open Var
open Orderings
*)


exception Trivial_equation
exception Identifications_needed

(*
  
  normalization modulo the theory of Boolean Rings.

*)

let normalize_first_pass th u =
  match th with
      BR(plus,zero,mult,one) ->
	begin
	  let term_zero = Term (zero,[])
	  and term_one = Term (one,[]) in
	  let rec rec_normalize = function
	      Var _ as v -> v
	    | Term (f,l) ->		  
		let l' = List.map (function t -> rec_normalize t) l in
		  if f = plus
		  then 
		    let l'' = 
		      List.fold_left
			(fun accu t ->
			   match t with
			       Var _ -> t :: accu
			     | Term (g,k) ->
				 if g = plus
				 then k @ accu
				 else 
				   if g = zero
				   then accu
				   else t :: accu)
			[] l' in
		      begin
			match l'' with
			    [] -> term_zero
			  | t::[] -> t
			  | _::_ -> Term (plus,l'')
		      end
		  else 
		    if f = mult
		    then 
		      begin
			if List.exists (function t -> t = term_zero) l'
			then term_zero
			else 
			  let l'' = 
			    List.filter (function t -> t <> term_one) l' in
			  let l''' = 
			  List.sort 
			    (fun t1 t2 ->
			       match t1,t2 with
				   Var x, Var y -> compare x y
				 | Var _, Term _ -> 1
				 | Term _, Var _ -> -1
				 | Term (f,_), Term (g,_) ->
				     if f=g
				     then 0
				     else 
				       if f = plus
				       then -1
				       else 1)
			    l'' in
			    match l''' with
				[] -> term_one
			      | t :: [] -> t
			      | Term (g,k) :: (_ :: _ as rest) ->
				  if g = plus
				  then 
				    let k' = 
				      List.map 
					(function ki -> Term (mult,ki::rest))
					k in
				      rec_normalize (Term (plus,k'))
				  else 
				    if g = mult 
				    then
				      rec_normalize  (Term (mult,k @ rest))
				    else assert false
			      | (Var _ as v) :: (_ :: _ as rest) -> 
				  Term (mult,l''')
		      end
		    else Term (f,l') in
	    rec_normalize u
	end
    | _ -> assert false


let remove_doubles_idem l =
  let rec rec_remove list_without_doubles current_item = function
      [] -> current_item :: list_without_doubles
    | i :: l -> 
	if i = current_item
	then rec_remove list_without_doubles current_item l
	else rec_remove (current_item :: list_without_doubles) i l in
  let l' = List.sort compare l in
    match l' with
	[] -> []
      | i :: l'' -> rec_remove [] i l''


let normalize_idempotency mult = function
    Var _ as v -> v
  | Term (f,l) as t ->
      if f = mult
      then 
	begin
	  let l' = remove_doubles_idem l in
	    match l' with
		t' :: [] -> t'
	      | _ :: _ :: _ -> Term (mult,l')
	      | _ -> assert false
	end
      else t

let remove_doubles_nil l = 
  let rec rec_remove list_without_doubles current_item = function
      [] -> current_item :: list_without_doubles
    | i :: [] -> 
	if i = current_item
	then list_without_doubles
	else i :: current_item :: list_without_doubles 
    | i1 :: (i2 :: l as i2_l) ->
	if i1 = current_item
	then rec_remove list_without_doubles i2 l
	else rec_remove (current_item :: list_without_doubles) i1 i2_l in
  let l' = List.sort compare l in
    match l' with
	[] -> []
      | i :: l'' -> rec_remove [] i l''


let normalize_nilpotency plus term_zero = function
    Var _ as v -> v
  | Term (f,l) as t ->
      if f = plus
      then 
	begin
	  let l' = remove_doubles_nil l in
	    match l' with
		[] -> term_zero
	      | t' :: [] -> t'
	      | _ :: _ :: _ -> Term (plus, l')
	end
      else t

let normalize br t = 
  match br with
      BR (plus,zero,mult,one) ->
	begin
	  let t1 = normalize_first_pass br t in
	    match t1 with
		Var _ -> t1
	      | Term (f,l) ->
		  if f = plus
		  then 
		  let t2 = 
		    Term (plus, List.map (normalize_idempotency mult) l) in
		    normalize_nilpotency plus (Term (zero,[])) t2
		  else 
		    if f = mult
		    then normalize_idempotency mult t1
		    else t1
	end
    | _ -> assert false

(*

  Elementary mutation rule for solving a variable.

*)

let select_var_for_dec elem_pb var_set = 
  VarSet.find
    (function x -> 
       (not (VarMap.mem x elem_pb.marked_variables)) &&
       (not (VarSet.exists 
	       (function y -> List.mem (y,x) elem_pb.edges) var_set)))
    var_set

let snd_select_var_for_dec elem_pb var_set =
  VarSet.find 
    (function x -> not (VarMap.mem x elem_pb.marked_variables))
    var_set

(*
  [decompose BR(+,0,*,1) x u] decomposes [u] under the form [x*s + t], where
  [x] does not occur in [s], neither in [t].
*)

let decompose br x u =
  match br with
      BR(plus,zero,mult,one) ->
	begin 
	  (* dec is called with 2 args (s,t) and u' such that *)
	  (* (x*s + t + u' = u                                *)
	  (* and returns with (s',t') such that x*s' + t' = u *)
	  let rec dec (s,t) = function
	      Var y as v -> 
		if x = y
		then (Term(plus,[Term(one,[]);s]),t)
		else (s,Term(plus,[v;t]))
		  
	    | Term(f,[]) as c -> (s,Term(plus,[c;t]))
		  
	    | Term(f,l) as u' -> 
		if f=mult
		then 
		  let v = Var x in
		    begin
		      if (List.mem v l) 
		      then 
			let l' = Listutils.except v l in
			  match l' with
			      v' :: [] -> (Term(plus,[s;v']),t) 
			    | _ :: _ :: _ -> (Term(plus,[s;Term(mult,l')]),t)
			    | [] -> assert false
		      else (s,Term(plus,[t;u']))
		    end
		else 
		  if f=plus
		  then List.fold_left dec (s,t) l
		  else assert false in
	  let term_zero = Term(zero,[]) in
	    dec (term_zero,term_zero) u
	end
    | _ -> assert false
	  

let mutate elem_pb u = 
  match elem_pb.elem_th with
      BR(plus,zero,mult,_) ->
	begin
	  let br = elem_pb.elem_th in
	  let u' = normalize br u in
	    if u' = Term(zero,[])
	    then raise Trivial_equation
	    else 
	      let vars_of_u' = set_of_variables u' in
	      let x = 
		try 
		  select_var_for_dec elem_pb vars_of_u' 
		with 
		    Not_found -> 
		      try 
			snd_select_var_for_dec elem_pb vars_of_u'
		      with 
			  Not_found -> raise Identifications_needed in
	      let (s,t) = decompose br x u'
	      and v' = Var (fresh_var_for_unif ()) in
	      let value_of_x = 
		normalize br (Term (plus,[v';Term(mult,[v';s]);t])) 
	      and t' = normalize br (Term(plus,[Term(mult,[s;t]);t])) in
		(t', (x, value_of_x))
	end
    | _ -> assert false


(*

  Solving the unification problem without taking care of identifications

*)

let elem_solve sign elem_pb list_of_equations = 
  match elem_pb.elem_th with
      BR(plus,zero,mult,one) ->
	let term_zero = Term(zero,[]) in
	let rec rec_elem_solve res = function
	    [] -> res
	  | (Var x as v,t as eq)::l -> 
	      let variables_of_t = set_of_variables t in
		if ((VarSet.mem x variables_of_t) ||
		    (VarMap.mem x elem_pb.marked_variables))
		then 
		  begin
		    try 
		      let t',(y,s) = mutate elem_pb (Term (plus,[v;t])) in
		      let sigma = VarMap.add y s VarMap.empty
		      and e = (Var y, s) in
		      let l' = apply_subst_to_eqs sign sigma l in
			rec_elem_solve (res@[e]) ((t',term_zero)::l') 
		    with 
			Trivial_equation -> rec_elem_solve res l
		  end
		else 
		  let sigma = VarMap.add x t VarMap.empty in
		  let l'= apply_subst_to_eqs sign sigma l in
		    rec_elem_solve (res@[eq]) l'

	  | (s,t)::l -> 
	      try 
		let t',(y,s') = mutate elem_pb (Term (plus,[s;t])) in
		let sigma =  VarMap.add y s' VarMap.empty
		and e = (Var y, s') in
		let l' = apply_subst_to_eqs sign sigma l in
		  rec_elem_solve (res@[e]) ((t',term_zero)::l') 
	      with 
		  Trivial_equation -> rec_elem_solve res l in
	  rec_elem_solve [] list_of_equations
    | _ -> assert false

(*

  Solving the problem with the identifications.

*)

let rec merge marks = function 
    [] -> []

  | (x :: _ as vars_ident_with_x) :: list_of_idents -> 
      let mark_of_x = VarMap.find x marks in
      let rec merge_with_x partial_result start_of_idents = function
	  [] -> partial_result
	| (y :: _ as vars_ident_with_y) :: end_of_idents ->
	    let mark_of_y = VarMap.find y marks in
              if mark_of_x = mark_of_y 
	      then
		let new_idents = 
		  (vars_ident_with_x @ vars_ident_with_y) :: 
		  (start_of_idents @ end_of_idents) in
		  merge_with_x 
		    (new_idents :: partial_result) 
		    (vars_ident_with_y :: start_of_idents) 
		    end_of_idents
	      else 
		merge_with_x 
		  partial_result
		  (vars_ident_with_y :: start_of_idents) 
		  end_of_idents 
	| _ -> assert false in

	(List.map 
	   (function new_list_of_idents -> 
	      vars_ident_with_x :: new_list_of_idents) 
	   (merge marks list_of_idents)) @ 
	(merge_with_x [] [] list_of_idents)

  | _ -> assert false


let is_included l1 l2 = List.for_all (function x -> List.mem x l2) l1


let is_a_finer_partition p1 p2 = 
  List.for_all 
    (function s -> (List.exists (function s' -> is_included s s') p2)) p1



let update_wrt_merge list_of_idents list_of_equations =
  let representative x = 
    let class_of_x = List.find (function c -> List.mem x c) list_of_idents in
      match class_of_x with
	  y :: _ -> y
	| [] -> assert false in

  let rec update_wrt_merge_term = function
      Var x -> Var (representative x)
    | Term (f,l) -> Term (f, (List.map update_wrt_merge_term l)) in
    
    List.map 
      (function (s,t) -> (update_wrt_merge_term s, update_wrt_merge_term t))
      list_of_equations


let rec solve_with_ident sign elem_pb success failures = function
    [] ->
      begin
	match failures with  
	    [] -> success  
	  | _::_ ->  solve_with_ident sign elem_pb success [] failures
      end
  |  (idents,list_of_equations) :: to_develop ->
       let is_redundant i = 
	 List.exists (function (i',_) -> is_a_finer_partition i' i) success in
	 
	 if is_redundant idents
	 then solve_with_ident sign elem_pb success failures to_develop
	 else 
	   try 
	     let new_list_of_eqs = elem_solve sign elem_pb list_of_equations in
               solve_with_ident sign elem_pb 
		 ((idents,new_list_of_eqs) :: success) 
		 failures to_develop
           with 
	       Identifications_needed -> 
		 let new_list_of_idents = 
		   merge elem_pb.marked_variables idents in
		 let new_pbs_after_id = 
		   Listutils.map_filter
		     (function new_idents -> 
			let new_equations = 
			  update_wrt_merge new_idents list_of_equations in
			  (new_idents,new_equations))
		     (function new_idents -> not (is_redundant new_idents))
		     new_list_of_idents in
		   solve_with_ident sign elem_pb
		     success (failures @ new_pbs_after_id) to_develop


let rec oc_instanciate sign res = function
    []  -> res
  | (Var x, t as eq) :: ll -> 
      let theta = VarMap.add x t VarMap.empty in
      let res' = apply_subst_to_eqs sign theta res in
        oc_instanciate sign (eq::res') ll
  | _ -> assert false

(*

  Elimination of constants.

*)


let rec cst_to_elim elem_pb = function
    [] -> raise Not_found
  | (Var x, t) :: list_of_equations ->
      begin
	let variables_of_t = set_of_variables t in
          try  
	    let (y,_) = 
	      List.find
		(function (y,z) -> (z = x) && (VarSet.mem y variables_of_t))
		elem_pb.edges in
	      (y,t)
          with Not_found -> cst_to_elim elem_pb list_of_equations 
      end
  | _ -> assert false


let rec eliminate_cst sign  elem_pb (list_of_idents,list_of_equations as pb) = 
  match elem_pb.elem_th with
      BR(plus,zero,mult,one) ->
	begin
	  let new_list_of_equations = 
	    oc_instanciate sign [] list_of_equations in
	    try 
	      let c, t = cst_to_elim elem_pb new_list_of_equations
	      and lv = 
		List.fold_left
		  (fun set_of_vars (_,s) -> 
		     VarSet.union (set_of_variables s) set_of_vars)
		  VarSet.empty new_list_of_equations in
		
	      let theta = 
		VarSet.fold 
		  (fun x partial_subst -> 
		     let x1 = Var (fresh_var_for_unif ())
		     and x2 = Var (fresh_var_for_unif ()) in
		     let x1_plus_x2_mult_c = 
		       Term(plus,[x1;Term(mult,[x2;Var c])]) in
		       VarMap.add x x1_plus_x2_mult_c partial_subst)
		  lv VarMap.empty in

	      let new_list_of_equations_inst = 
		apply_subst_to_eqs sign theta new_list_of_equations
	      and t_theta = substitute sign theta t in

	      let (s,_) = decompose elem_pb.elem_th c t_theta in
	      let new_list_of_equations_to_be_solved = 
		(s,Term(zero,[])) :: new_list_of_equations_inst in
	      
	      let new_pbs = 
		solve_with_ident sign elem_pb 
		  [] [] [list_of_idents,new_list_of_equations_to_be_solved] in
		
		List.fold_left 
		  (fun partial_res pb' ->
		     let new_pbs' =
		       eliminate_cst sign elem_pb pb' in
		       new_pbs' @ partial_res)
		  [] new_pbs

	    with Not_found -> [list_of_idents,new_list_of_equations]
	end

    | _ -> assert false


let build_var_var list_of_identifications = 
  List.fold_left
    (fun list_of_var_var_eqs ident_vars -> 
       match ident_vars with
	   x :: list_of_vars ->
	     let vx = Var x in
	       List.fold_left
		 (fun lvv y -> (vx,Var y) :: lvv)
		 list_of_var_var_eqs 
		 list_of_vars
	 | [] -> list_of_var_var_eqs)
    []
    list_of_identifications


let solve sign elem_pb = 
  let vars = 
    List.fold_left 
      (fun partial_set_of_vars (s,t) ->
	 VarSet.union (set_of_variables s) 
	   (VarSet.union (set_of_variables t) partial_set_of_vars))
      VarSet.empty elem_pb.equations in

  let marked_vars = 
    VarMap.fold 
      (fun x _ partial_set_of_marked_vars ->
	 if VarSet.mem x vars
	 then VarSet.add x partial_set_of_marked_vars
	 else partial_set_of_marked_vars)
      elem_pb.marked_variables VarSet.empty in

  let idents = 
    VarSet.fold
      (fun x partial_idents -> [x]::partial_idents)
      marked_vars [] in

  let res1 = solve_with_ident sign elem_pb [] [] [idents,elem_pb.equations] in

  let res2 = Listutils.flat_map (eliminate_cst sign elem_pb) res1 in
    List.map 
      (function (ident,eqs) ->
	 List.rev_append
	   (build_var_var ident) 
	   (List.map 
	      (function (s,t) -> 
		 (normalize elem_pb.elem_th s, normalize elem_pb.elem_th t))
	      eqs))
      res2
      
