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
open Variable_abstraction

module UnifElemThMap = Ordered_maps.MakePoly (OrderedUnifElemTheory)

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

let print_elem_pb sign vars elem_pb =
  Printf.printf "key = %s\n" 
    (string_of_unif_elem_theory sign elem_pb.key);
  Printf.printf "status = %s\n" (match elem_pb.status with
				     Solved -> "solved"
				   | Marked -> "marked"
				   | Merged -> "merged"
				   | Unsolved -> "unsolved");
  Printf.printf "elem_th = %s\n" 
    (string_of_elem_theory sign elem_pb.elem_th);
  Printf.printf "inst_variables = \n";
  Substitution.print sign vars elem_pb.inst_variables;
  Printf.printf "marked_variables = \n";
  VarMap.iter
    (fun x m ->
       Printf.printf "%s is marked by %s\n"
	 (vars#string_of_var x)
	 (match m with 
	      No_mark -> "No_mark"
	    | Erasable -> "Erasable"
	    | Permanent th -> "Permanent"^(string_of_elem_theory sign th)))
    elem_pb.marked_variables;
  Printf.printf "edges = \n";
  List.iter
    (fun (x,y) ->
       Printf.printf "(%s,%s)" (vars#string_of_var x) (vars#string_of_var y))
    elem_pb.edges;
  Printf.printf "\n";
  Printf.printf "equations =\n";
  List.iter
    (fun (s,t) ->
       print_term sign vars s;
       Format.print_flush ();
       Printf.printf " = ";
       print_term sign vars t;
       Format.print_flush ();
       Printf.printf "\n")
    elem_pb.equations
  

let print_problem sign vars pb =
  Printf.printf "*******************************************\n";
  Printf.printf "unif_kind = %s\n" (match pb.unif_kind with
					PLAIN -> "PLAIN"
				      | AC_COMPLETE -> "AC_COMPLETE"
				      | AC_ONLY -> "AC_ONLY");
  Printf.printf "global_status = %s\n" (match pb.global_status with
					    Solved -> "solved"
					  | Marked -> "marked"
					  | Merged -> "merged"
					  | Unsolved -> "unsolved");
  Printf.printf "first_variables = { ";
  VarSet.iter 
    (function x -> Printf.printf "%s " (vars#string_of_var x))
    pb.first_vars;
  Printf.printf "}\n";
  Printf.printf "equations between variables = \n";
  VarMap.iter 
    (fun x y ->
       Printf.printf "%s = %s\n" (vars#string_of_var x) (vars#string_of_var y))
    pb.var_var;
  UnifElemThMap.iter
    (fun _ elem_pb -> 
       Printf.printf "--------------------------------------------\n";
       print_elem_pb sign vars elem_pb)
    pb.elem_pbs;
  Printf.printf "--------------------------------------------\n";
  Printf.printf "solved_part = \n";
  List.iter
    (fun (s,t) ->
       print_term sign vars s;
       Format.print_flush ();
       Printf.printf " = ";
       print_term sign vars t;
       Format.print_flush ();
       Printf.printf "\n")
    pb.solved_part;
  Printf.printf "*******************************************\n"

(*

  Treatment for the equations between variables.

*)


let representative x pb = 
  try
    VarMap.find x pb.var_var
  with 
      Not_found -> x

let rec replace_a_var_by_a_var_in_a_term var rep = function 
    Var x as v -> if x = var then Var rep else v
  | Term (f,l) -> 
      let l' = List.map (replace_a_var_by_a_var_in_a_term var rep) l in
	Term (f,l')

let rec replace_a_var_by_a_var_in_an_eq var rep (s,t) = 
  let s' = replace_a_var_by_a_var_in_a_term var rep s
  and t' = replace_a_var_by_a_var_in_a_term var rep t in
    (s',t')

let add_an_equation_between_variables pb x y = 
  if x = y 
  then pb
  else
    begin
      let (var,rep) = 
	let x' = representative x pb
	and y' = representative y pb in
	  if (VarOrd.compare x' y') > 0
	  then (x',y')
	  else (y',x') in
	  
	let new_var_var = 
	  VarMap.add var rep 
	    (VarMap.map (function r -> if r = var then rep else r) pb.var_var) 

	and new_elem_pbs = 
	  UnifElemThMap.map 
	    (function elem_pb ->
	       let new_status = 
		 match elem_pb.status with
	             Solved ->
		       begin
			 try 
			   let _ = VarMap.find var elem_pb.inst_variables
			   and _ = VarMap.find rep elem_pb.inst_variables in
			     Merged
			 with Not_found -> Solved
		       end
		   | status -> status
			 
	       and new_inst_variables = 
		 try
		   let _ = VarMap.find var elem_pb.inst_variables in
		     VarMap.fold
		       (fun v value current_inst_variables -> 
			  if v = var 
			  then VarMap.add rep value current_inst_variables
			  else VarMap.add v value current_inst_variables)
		       elem_pb.inst_variables VarMap.empty 
		 with Not_found -> elem_pb.inst_variables 
		     
	       and new_marked_variables = 
		 try
		   let _ = VarMap.find var elem_pb.marked_variables in
		     VarMap.fold
		       (fun v th current_marked_variables -> 
			  if v = var 
			  then VarMap.add rep th current_marked_variables
			  else VarMap.add v th current_marked_variables)
		       elem_pb.marked_variables VarMap.empty 
		 with Not_found -> elem_pb.marked_variables
		     
	       and new_edges = 
		 List.map 
		   (function (u,v) -> 
		      ((if u = var then rep else u),
		       (if v = var then rep else v)))
		   elem_pb.edges
		   
	       and new_equations = 
		 List.map 
		   (replace_a_var_by_a_var_in_an_eq var rep) 
		   elem_pb.equations in

		 {
		   elem_pb with
		   status = new_status;
		   inst_variables = new_inst_variables;
		   marked_variables = new_marked_variables;
		   edges = new_edges;
		   equations = new_equations
	          })
	    pb.elem_pbs in
      
	  {
	    pb with
	    global_status = Unsolved;
	    var_var = new_var_var;
	    elem_pbs = new_elem_pbs;
	    solved_part = []
          }
    end


(*

  Treatment for the other equations

*)

let unif_elem_theory_of_eq e find_th = 
  match e with
      Var _, Term (f,_) -> find_th f
    | Term (f,_), _ -> find_th f
    | Var _, Var _ -> assert false


(*

  General treatment of equations

*)

let add_a_pure_eq_to_pb pb = function
    Var x, Var y as e -> add_an_equation_between_variables pb x y
  | e ->
      let uth_for_e = unif_elem_theory_of_eq e pb.find_th in
      let new_elem_pb_for_e = 
	try 
	  let elem_pb_for_e = UnifElemThMap.find uth_for_e pb.elem_pbs in
	    {
	      elem_pb_for_e with
	      size = None;
	      inst_variables = 
	       begin
		 match e with
		     Var x, t -> VarMap.add x t elem_pb_for_e.inst_variables
		   | t, Var x -> VarMap.add x t elem_pb_for_e.inst_variables
		   | _, _ -> elem_pb_for_e.inst_variables
	       end;
	      equations = e::elem_pb_for_e.equations
	    } 
	with 
	    Not_found -> 
          {
	    key = uth_for_e;
	    status = Unsolved;
	    size = None;
	    elem_th = snd uth_for_e;
	    inst_variables = 
	     begin
	       match e with
		   Var x, t -> VarMap.add x t VarMap.empty
		 | t, Var x -> VarMap.add x t VarMap.empty
		 | _, _ -> VarMap.empty
	     end;
	    marked_variables = VarMap.empty;
	    edges = [];
	    equations = [e]
	  } in

      let new_elem_pbs = 
	UnifElemThMap.add uth_for_e new_elem_pb_for_e pb.elem_pbs in
	{
	  pb with
	  global_status = Unsolved;
	  elem_pbs = new_elem_pbs;
	  solved_part = []
	}



(*

  Initialisation of the unification problem : [(init sign th t1 t2)]
  builds the data structucture for solving [t1 = t2] modulo the
  equational theory [th], where [t1] and [t2] are some terms built
  over the signature [sign].

*)

let init unif_k sign find_th t1 t2 = 
  let vars_of_t1_and_t2 =  
    VarSet.union (set_of_variables t1) (set_of_variables t2) in
  let _ = init_for_unif vars_of_t1_and_t2 in
  let list_of_pure_eqs = purify_list_of_equations unif_k find_th [(t1,t2)] in
  let first_vars = 
    List.fold_left 
      (fun partial_set_of_vars (s,t) ->
	 VarSet.union (set_of_variables s) 
	   (VarSet.union (set_of_variables t) partial_set_of_vars))
      VarSet.empty list_of_pure_eqs in

    List.fold_left
      (fun pb e -> add_a_pure_eq_to_pb pb e)
      {
	unif_kind = unif_k;
	global_status = Unsolved;
	sign = (sign :> 'a Signatures.signature);
	find_th = find_th;
	vars_for_eqe = vars_of_t1_and_t2;
	first_vars = first_vars;
	var_var = VarMap.empty;
	elem_pbs = UnifElemThMap.empty;
	solved_part = []
      }
      list_of_pure_eqs


(*
  
  Update of a unification problem.

*)


let sort_list_of_equations list_of_equations =
  List.partition 
    (function
	 (Var _, Var _) -> true
       | (Var _, Term _) -> false
       | _ -> assert false)
    list_of_equations

let insert_a_solved_elem_pb sign (*i vars i*) pb key list_of_equations =
(*
  let _ = 
    begin
      Printf.printf "Liste des equations a inserer\n";
      List.iter
	(fun (s,t) ->
	   print_term sign vars s;
	   Format.print_flush ();
	   Printf.printf " = ";
	   print_term sign vars t;
	   Format.print_flush ();
	   Printf.printf "\n")
	list_of_equations;
      Printf.printf "Le probleme avant\n";
      print_problem sign vars pb
    end in
*)

  let is_regular_collapse_free, is_ac =
    match key with
	_, (Empty _) -> true, false
      | _, (AC _) -> true, true
      | _, _ -> false, false in

  let list_of_var_var_eqs, list_of_var_term_eqs =
    sort_list_of_equations list_of_equations in

  let elem_pb_of_key = UnifElemThMap.find key pb.elem_pbs in

  let new_inst_vars = 
    List.fold_left
      (fun partial_inst_vars eq ->
	 match eq with
	     Var x, (Term _ as t) -> VarMap.add x t partial_inst_vars
	   | _, _ -> assert false)
      VarMap.empty list_of_var_term_eqs in

  let new_elem_pb_of_key =
    {
      elem_pb_of_key with
      status = Solved;
      size = None;
      inst_variables = new_inst_vars;
      equations = list_of_var_term_eqs
    } in

  let new_elem_pbs =
    let update_elem_pb elem_pb =
      if is_regular_collapse_free
      then 
	let new_marked_vars = 
	  if is_ac
	  then 
	    let mark_to_set = Permanent (snd key) in
	      VarMap.fold 
		(fun x _ marked_vars -> VarMap.add x mark_to_set marked_vars) 
		new_inst_vars 
		elem_pb.marked_variables
	  else 
	    VarMap.fold
	      (fun x t marked_vars ->
		 match t with
		     Term (f,_) -> 
		       VarMap.add x (Permanent (Empty (Some f))) marked_vars
		   | Var _ -> assert false)
	      new_inst_vars
	      elem_pb.marked_variables in
	  {
	    elem_pb with
	    marked_variables = new_marked_vars
	  }
      else elem_pb in

      UnifElemThMap.mapi
	(fun k elem_pb ->
	   if k = key
	   then new_elem_pb_of_key
	   else update_elem_pb elem_pb)
	pb.elem_pbs in

  let new_pb = 
    {pb with 
       global_status = Unsolved;
       elem_pbs = new_elem_pbs;
       solved_part = []} in

  let result_pb = 
    List.fold_left
      (fun pb' eq ->
	 match eq with
	     (Var x, Var y) -> add_an_equation_between_variables pb' x y
	   | _ -> assert false)
      new_pb list_of_var_var_eqs in
(*
  let _ =
    begin
      Printf.printf "Le probleme apres\n";
      print_problem sign vars result_pb
    end in
*)
    result_pb

let insert_solved_elem_pbs sign (*i vars i*) pb key solved_elem_pbs =
  List.map (insert_a_solved_elem_pb sign (*i vars i*) pb key) solved_elem_pbs



