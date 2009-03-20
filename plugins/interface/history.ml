open Paths;;

type tree = {mutable index : int;
             parent : tree option;
             path_to_root : int list;
             mutable is_open : bool;
             mutable sub_proofs : tree list};;

type prf_info = {
    mutable prf_length : int;
    mutable ranks_and_goals : (int * int * tree) list;
    mutable border : tree list;
    prf_struct : tree};;

let theorem_proofs = ((Hashtbl.create 17): 
			(string, prf_info) Hashtbl.t);;


let rec mk_trees_for_goals path tree rank k n =
  if k = (n + 1) then
    []
  else
    { index = rank;
      parent = tree;
      path_to_root = k::path;
      is_open = true;
      sub_proofs = [] } ::(mk_trees_for_goals  path tree rank (k+1) n);;


let push_command s rank ngoals =
  let ({prf_length = this_length;
 	ranks_and_goals = these_ranks;
	border = this_border} as proof_info) =
         Hashtbl.find theorem_proofs s in
  let rec push_command_aux n = function
      [] -> failwith "the given rank was too large"
    | a::l ->
	if n = 1 then
	 let {path_to_root = p} = a in
	 let new_trees = mk_trees_for_goals p (Some a) (this_length + 1) 1 ngoals in
	 new_trees,(new_trees@l),a
	else
	  let new_trees, res, this_tree = push_command_aux (n-1) l in
	  new_trees,(a::res),this_tree in
  let new_trees, new_border, this_tree =
      push_command_aux rank this_border in
  let new_length = this_length + 1 in
  begin
    proof_info.border <- new_border;
    proof_info.prf_length <- new_length;
    proof_info.ranks_and_goals <- (rank, ngoals, this_tree)::these_ranks;
    this_tree.index <- new_length;
    this_tree.is_open <- false;
    this_tree.sub_proofs <- new_trees
  end;;

let get_tree_for_rank thm_name rank = 
  let {ranks_and_goals=l;prf_length=n} = 
         Hashtbl.find theorem_proofs thm_name in
  let rec get_tree_aux = function
      [] ->
 	failwith 
         "inconsistent values for thm_name and rank in get_tree_for_rank"
    | (_,_,({index=i} as tree))::tl ->
	if i = rank then
	  tree
	else
	  get_tree_aux tl in
  get_tree_aux l;;

let get_path_for_rank thm_name rank =
  let {path_to_root=l}=get_tree_for_rank thm_name rank in
  l;;

let rec list_descendants_aux l tree =
  let {index = i; is_open = open_status; sub_proofs = tl} = tree in
  let res = (List.fold_left list_descendants_aux  l tl) in
  if open_status then i::res else res;;

let list_descendants thm_name rank =
  list_descendants_aux [] (get_tree_for_rank thm_name rank);;

let parent_from_rank thm_name rank =
  let {parent=mommy} = get_tree_for_rank thm_name rank in
  match mommy with
   Some x -> Some x.index
  | None -> None;;

let first_child_command thm_name rank =
  let {sub_proofs = l} = get_tree_for_rank thm_name rank in
  let rec first_child_rec = function 
      [] -> None
    | {index=i;is_open=b}::l -> 
	if b then
	  (first_child_rec l)
	else
 	  Some i in
  first_child_rec l;;

type index_or_rank = Is_index of int | Is_rank of int;;

let first_child_command_or_goal thm_name rank =
  let proof_info = Hashtbl.find theorem_proofs thm_name in
  let {sub_proofs=l}=get_tree_for_rank thm_name rank in
  match l with
    [] -> None
  | ({index=i;is_open=b} as t)::_ -> 
      if b then
	let rec get_rank n = function
	    [] -> failwith "A goal is lost in first_child_command_or_goal"
	  | a::l ->
	      if a==t then
		n
	      else
		get_rank (n + 1) l in
	Some(Is_rank(get_rank 1 proof_info.border))
      else
	Some(Is_index i);;

let next_sibling thm_name rank =
  let ({parent=mommy} as t)=get_tree_for_rank thm_name rank in
  match mommy with
    None -> None
  |  Some real_mommy ->
  let {sub_proofs=l}=real_mommy in
  let rec next_sibling_aux b = function
      (opt_first, []) -> 
	if b then
	  opt_first
	else
	  failwith "inconsistency detected in next_sibling"
    | (opt_first, {is_open=true}::l) -> 
	next_sibling_aux b (opt_first, l)
    | (Some(first),({index=i; is_open=false} as t')::l) ->
	if b then
	  Some i
	else
	  next_sibling_aux (t == t') (Some first,l)
    | None,({index=i;is_open=false} as t')::l ->
  	next_sibling_aux (t == t') ((Some i), l)
  in
  Some (next_sibling_aux false (None, l));;


let prefix l1 l2 =
  let l1rev = List.rev l1 in
  let l2rev = List.rev l2 in
  is_prefix l1rev l2rev;;

let rec remove_all_prefixes p = function
    [] -> []
  | a::l -> 
      if is_prefix p a then
 	(remove_all_prefixes p l)
      else
	a::(remove_all_prefixes p l);;

let recompute_border tree =
  let rec recompute_border_aux tree acc =
    let {is_open=b;sub_proofs=l}=tree in
    if b then
      tree::acc
    else
      List.fold_right recompute_border_aux l acc in
  recompute_border_aux tree [];;
 
   
let historical_undo thm_name rank =
  let ({ranks_and_goals=l} as proof_info)=
       Hashtbl.find theorem_proofs thm_name in
  let rec undo_aux acc = function
      [] ->  failwith "bad rank provided for undoing in historical_undo"
    | (r, n, ({index=i} as tree))::tl  ->
	let this_path_reversed = List.rev tree.path_to_root in
	let res = remove_all_prefixes this_path_reversed acc in
	if i = rank then
	  begin
	    proof_info.prf_length <- i-1;
	    proof_info.ranks_and_goals <- tl;
	    tree.is_open <- true;
	    tree.sub_proofs <- [];
	    proof_info.border <- recompute_border proof_info.prf_struct;
            this_path_reversed::res 
	  end
	else
	  begin
	    tree.is_open <- true;
	    tree.sub_proofs <- [];
	    undo_aux (this_path_reversed::res) tl
	  end
  in
  List.map List.rev (undo_aux [] l);;

(* The following function takes a list of trees and compute the
   number of elements whose path is lexically smaller or a suffixe of
   the path given as a first argument.  This works under the precondition that
   the list is lexicographically order. *)

let rec logical_undo_on_border the_tree rev_path = function
    [] -> (0,[the_tree])
  | ({path_to_root=p}as tree)::tl ->
    let p_rev = List.rev p in
    if is_prefix rev_path p_rev then
      let (k,res) = (logical_undo_on_border the_tree rev_path tl) in
          (k+1,res)
    else if lex_smaller p_rev rev_path then
      let (k,res) = (logical_undo_on_border the_tree rev_path tl) in
          (k,tree::res)
    else
          (0, the_tree::tree::tl);;
   

let logical_undo thm_name rank =
  let ({ranks_and_goals=l; border=last_border} as proof_info)=
           Hashtbl.find theorem_proofs thm_name in
  let ({path_to_root=ref_path} as ref_tree)=get_tree_for_rank thm_name rank in
  let rev_ref_path = List.rev ref_path in
  let rec logical_aux lex_smaller_offset family_width = function
      [] -> failwith "this case should never happen in logical_undo"
    | (r,n,({index=i;path_to_root=this_path; sub_proofs=these_goals} as tree))::
        tl ->
        let this_path_rev = List.rev this_path in
        let new_rank, new_offset, new_width, kept =
	  if is_prefix rev_ref_path this_path_rev then
	    (r + lex_smaller_offset), lex_smaller_offset,
              (family_width + 1 - n), false 
	  else if lex_smaller this_path_rev rev_ref_path then
            r, (lex_smaller_offset -  1 + n), family_width, true
          else
            (r + 1 - family_width+ lex_smaller_offset),
	    lex_smaller_offset, family_width, true in
        if i=rank then
	  [i,new_rank],[], tl, rank
        else
          let ranks_undone, ranks_kept, ranks_and_goals, current_rank =
	    (logical_aux new_offset new_width tl) in
          begin
	    if kept then
	      begin
	      	tree.index <- current_rank;
	    	ranks_undone, ((i,new_rank)::ranks_kept),
	    	((new_rank, n, tree)::ranks_and_goals), 
                (current_rank + 1)
	      end
	    else
	      ((i,new_rank)::ranks_undone), ranks_kept,
	      ranks_and_goals, current_rank
	  end in
  let number_suffix, new_border = 
     logical_undo_on_border ref_tree rev_ref_path last_border in
  let changed_ranks_undone, changed_ranks_kept, new_ranks_and_goals,
    new_length_plus_one = logical_aux 0 number_suffix l in
  let the_goal_index =
    let rec compute_goal_index n = function
	[] -> failwith "this case should never happen in logical undo (2)"
      |	{path_to_root=path}::tl ->
	  if List.rev path = (rev_ref_path) then
	    n
	  else
	    compute_goal_index (n+1) tl in
    compute_goal_index 1 new_border in
  begin
    ref_tree.is_open <- true;
    ref_tree.sub_proofs <- [];
    proof_info.border <- new_border;
    proof_info.ranks_and_goals <- new_ranks_and_goals;
    proof_info.prf_length <- new_length_plus_one - 1;
    changed_ranks_undone, changed_ranks_kept, proof_info.prf_length, 
    the_goal_index
  end;;
	
let start_proof thm_name =
   let the_tree = 
      {index=0;parent=None;path_to_root=[];is_open=true;sub_proofs=[]} in
   Hashtbl.add theorem_proofs thm_name
     {prf_length=0;
      ranks_and_goals=[];
      border=[the_tree];
      prf_struct=the_tree};;
      
let dump_sequence chan s =
    match (Hashtbl.find theorem_proofs s) with
    {ranks_and_goals=l}->
      let rec dump_rec = function
	  [] -> ()
  	| (r,n,_)::tl ->
	    dump_rec tl;
	    output_string chan (string_of_int r);
	    output_string chan ",";
	    output_string chan (string_of_int n);
	    output_string chan "\n" in
      begin
      	dump_rec l;
	output_string chan "end\n"
      end;;

      
let proof_info_as_string s =
  let res = ref "" in
  match (Hashtbl.find theorem_proofs s) with
  {prf_struct=tree} ->
  let open_goal_counter = ref 0 in
  let rec dump_rec = function
    {index=i;sub_proofs=trees;parent=the_parent;is_open=op} ->
    begin
      (match the_parent with
         None ->
	   if op then
	     res := !res ^  "\"open goal\"\n"
       | Some {index=j} -> 
           begin
             res := !res ^  (string_of_int j);
             res := !res ^  " -> ";
	     if op then
	       begin
		 res := !res ^  "\"open goal ";
		 open_goal_counter := !open_goal_counter + 1;
		 res := !res ^  (string_of_int !open_goal_counter);
		 res := !res ^  "\"\n";
	       end
	     else
	       begin
		 res := !res ^  (string_of_int i);
		 res := !res ^  "\n"
	       end
           end);
      	List.iter dump_rec trees
     end in
  dump_rec tree;
  !res;;


let dump_proof_info chan s = 
  match (Hashtbl.find theorem_proofs s) with
  {prf_struct=tree} ->
  let open_goal_counter = ref 0 in
  let rec dump_rec = function
    {index=i;sub_proofs=trees;parent=the_parent;is_open=op} ->
    begin
      (match the_parent with
         None ->
	   if op then
	     output_string chan "\"open goal\"\n"
       | Some {index=j} -> 
           begin
             output_string chan (string_of_int j);
             output_string chan " -> ";
	     if op then
	       begin
		 output_string chan "\"open goal ";
		 open_goal_counter := !open_goal_counter + 1;
		 output_string chan (string_of_int !open_goal_counter);
		 output_string chan "\"\n";
	       end
	     else
	       begin
		 output_string chan (string_of_int i);
		 output_string chan "\n"
	       end
           end);
      	List.iter dump_rec trees
     end in
  dump_rec tree;;

let get_nth_open_path s n =
  match Hashtbl.find theorem_proofs s with
    {border=l} ->
    let {path_to_root=p}=List.nth l (n - 1) in
    p;;

let border_length s =
  match Hashtbl.find theorem_proofs s with
    {border=l} -> List.length l;;
