
module type Confluence = 
sig
  type symbol
  type signature 
  type variables
  type simple_rule 
  val is_confluent : signature -> variables -> simple_rule list -> bool 
  val print_all_critical_pairs : 
    signature -> variables -> simple_rule list -> unit
end
  


module Make (R : Abstract_rewriting.AbstractRewriting) =
struct
  type symbol = R.symbol
  type signature = R.signature
  type variables = R.variables
  type simple_rule = R.rule
   
  let check_joignable sigma vars rc r1 r2 (t1,t2) =
    let nf1 = R.normalize sigma vars rc t1
    and nf2 = R.normalize sigma vars rc t2
    in
    if R.equals sigma nf1 nf2
    then () 
    else
      match R.canonize_pairs [(t1,t2)] with
	| [(t1,t2)] ->
	    Format.printf "Found non-joignable pair:@ @[(";
	    R.print_t sigma vars t1;
	    Format.printf ",@ ";
	    R.print_t sigma vars t2;
	    Format.printf ")@]@ from rule@ ";
	    R.print_rewrite_rule sigma vars r1;
	    begin
	      match r2 with 
		| None -> Format.printf "@ on itself@.";	  
		| Some(r) -> 
		    Format.printf "@ and rule@ ";
		    R.print_rewrite_rule sigma vars r;
		    Format.printf "@.";	  
	    end;
	    raise Exit
	| _ -> assert false
  
      
  let rec check_all_non_self_pairs sigma vars r rl rc accu =
    match rl with
      | [] -> accu
      | r1::l1 ->
	  (* Format.printf "Computing critical pairs@."; *)	  
	  let e = R.critical_pairs sigma r r1 in
	  let n = List.length e in
	  if n > 0 
	  then
	    begin
	      (* Format.printf "Checking %d critical pairs@." n; *)
	      List.iter (check_joignable sigma vars rc r (Some r1)) e;
	    end;
	  check_all_non_self_pairs sigma vars r l1 rc (n+accu)

		
  let rec check_all_criticals_pairs sigma vars rl rc accu =
    match rl with
      | [] -> accu
      | r::l ->
	  (* Format.printf "Computing self critical pairs@."; *)	  
	  let e1 = R.self_critical_pairs sigma r in
	  let n = List.length e1 in
	  if n > 0 
	  then
	    begin	      
	      (* Format.printf "Checking %d critical pairs@." n; *)
	      List.iter (check_joignable sigma vars rc r None) e1;
	    end;
	  let e2 = check_all_non_self_pairs sigma vars r l rc 
		     (n+accu) 
	  in
	  check_all_criticals_pairs sigma vars l rc e2

  
  let is_confluent sigma vars r =
    let rc = R.compile sigma r in
      try
	let e = check_all_criticals_pairs sigma vars r rc 0 in
	  Format.printf 
	    "System is confluent (%d critical pair(s) tested).@." e;
	  true
      with
	  Exit -> false

  let rec compute_all_non_self_pairs sigma vars r rl accu =
    match rl with
      | [] -> accu
      | r1::l1 ->
	  let e = R.critical_pairs sigma r r1 in
	    compute_all_non_self_pairs sigma vars r l1 
	      ((r,(Some r1),e) :: accu)

  let rec compute_all_critical_pairs sigma vars rl accu =
    match rl with
      | [] -> accu
      | r::l ->
	  let e1 = R.self_critical_pairs sigma r in
	  let e2 = compute_all_non_self_pairs sigma vars r l accu in
	  compute_all_critical_pairs sigma vars l ((r,None,e1) :: e2)
    

  let print_all_critical_pairs sigma vars r =
    let rc = R.compile sigma r in
    let cp = compute_all_critical_pairs sigma vars r [] in
      List.iter
	(function (r1,r2,cp_list) ->
	   List.iter
	     (function
		  (t1,t2 as t1_t2) ->
		    try 
		      check_joignable sigma vars rc r1 r2 t1_t2
		    with 
			Exit -> Format.print_newline();
	     )
	     cp_list
	)
	cp
end



module User_symbol = struct type t = User_signatures.symbol_id end

module StandardConfluence = 
  Make (Abstract_rewriting.MakeStandardRewriting (User_symbol))

module ACConfluence = 
  Make (Abstract_rewriting.MakeACRewriting (User_symbol))
   
