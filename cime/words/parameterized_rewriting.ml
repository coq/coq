(**************************************************************************

  This module defines parameterized string rewriting.

  CiME Project - Démons research team - LRI - Université Paris XI

  $Id$

***************************************************************************)


open Parameterized_words

type rewrite_rule = 
    {rrule :
       (Parameterized_words.factor list * Parameterized_words.factor list);
     rconstr : Linear_constraints.formula;
     renv :  Linear_constraints.var_id list
    }

type srs = rewrite_rule list

(*


pretty print

*)

open Format

let print_rule {rrule = (g,d) ; rconstr = c ; renv = env } =
  printf "@[";
  User_parameterized_words.print_env env;
  User_parameterized_words.print_letters g;
  printf " -> ";
  User_parameterized_words.print_letters d;
  printf "|@ { ";
  Linear_constraints.print c;
  printf "}@]"
;;


let pretty_print c = 
  printf "@[<hov 2>{ ";
  List.iter (fun r -> print_rule r; printf " ;@ ") c;
  printf "} <%d rules>" (List.length c)
;;

(*

  decompositions

*)

type c_triple = (Parameterized_words.factor list * 
		 Parameterized_words.factor list *
		 Parameterized_words.factor list *
		 Linear_constraints.formula
		)


let add_in_decomposition phi0 w ((c1,c2,c3,phi) as d2) = 
  let new_phi = Linear_constraints.conj phi0 phi in
    if w = [] then [(c1,c2,c3,phi) ] else
      match d2 with 
	| [],[],c3,phi ->
	    [[],[],w@c3, new_phi; [],w,c3,new_phi ; w, [], c3, new_phi ; ] 
	| [],c2,c3,phi -> 
	    [ [], w@c2, c3, new_phi ; w, c2, c3, new_phi;] 
	| c1,c2,c3,phi -> [ w@c1, c2, c3, new_phi; ]

let add_in_decompositions phi w d2 =
  List.fold_left 
    (fun acc x -> (add_in_decomposition phi w x)@acc)
    []
    d2

let catenate_decomposition (c1,c2,c3,phi) d2 =
  add_in_decompositions Linear_constraints.true_formula c1 
    (add_in_decompositions Linear_constraints.true_formula
       c2 (add_in_decomposition phi c3 d2))

let catenate_decompositions d1 d2 =
  Listutils.flat_map (fun x -> catenate_decomposition d1 x ) d2

let full_catenate_decompositions d1 d2 =
  Listutils.flat_map 
    (fun y -> Listutils.flat_map (fun x -> catenate_decomposition y x ) d2)
    d1

    
let display_dec (u,v,w,aleph) =
    printf "====DEC======@.";
    printf "Prefix:@ ";
    User_parameterized_words.print_letters u;
    printf "@.Factor:@ ";
    User_parameterized_words.print_letters v;
    printf "@.Suffix:@ ";
    User_parameterized_words.print_letters w;
    printf "@.Constraint:@ ";
    Linear_constraints.print aleph;
    printf "@.=============@."


let split_2 l1 = 
  let rec f l1 l2 = match l1 with
    | [] -> [List.rev l2,[]]
    | x::r -> ((List.rev l2),l1)::(f r (x::l2))
  in
    f l1 []

let split_again l1 = 
  Listutils.flat_map
    (fun (x,y) -> 
       List.map (fun (a,b) -> a,b,y) (split_2 x ))	
    l1
    
let split_3 l = split_again (split_2 l)


let letters_to_factor l = 
  match l with 
    | [] -> []
    | l ->  [{base = l ; operator = No}]

let cte0 = Linear_constraints.zero 
let cte1 = Linear_constraints.one
let cte2 = Linear_constraints.cte Numbers.two

let rec decompose ({env = old_env ; 
		    letters = l ;
		    constr = phi } as w) = 
  match l with
    | [] -> [],[[],[],[],phi] (* left,middle,right, constraint,new_vars *)
    | {base = [] ; operator = No}::r -> 
	(decompose {w with letters = r})
    | {base = a1::l ; operator = No}::r -> 
	let new_vars,dec = 
	  (decompose {w with 
			letters = {base = l ; operator = No}::r}) in
	  new_vars,(Listutils.flat_map
		      (fun x -> add_in_decomposition 
			 phi
			 [{base = [a1] ; operator = No}] x)
		      dec)
	    
    | {base = b ; operator = Power e}::r -> 
	if Linear_constraints.is_cte e then
	  let i = Linear_constraints.val_of_cte e in
	    if Numbers.le i Numbers.zero 
	    then decompose {w with letters = r} 
	    else decompose 
	      {w with 
		 letters = {base = b ; operator = No}::
			     {base = b ; operator = 
				Power (Linear_constraints.cte (Numbers.pred i))}
			   ::r}
	else
	  let new_vars,end_dec = decompose {w with letters = r} in
	    
	  (* Do not cut the power at all *)
	  let dec1 = add_in_decompositions 
		       phi
		       [{base = b ; operator = Power e}]
		       end_dec
	  in
	    (* Cut once in the power *)
	  let split2 = split_2 b in
	  let pv = Linear_constraints.make_var_uniq_name "p" 
	  and qv = Linear_constraints.make_var_uniq_name "q" 
	  and rv = Linear_constraints.make_var_uniq_name "r" 
	  in
	  let p = Linear_constraints.var pv
	  and q = Linear_constraints.var qv
	  and r = Linear_constraints.var rv
	  in
	  let new_constr0 = 
	    (Linear_constraints.conj
	       (Linear_constraints.eq
		  (Linear_constraints.add 
		     p 
		     ((Linear_constraints.add 
			 q 
			 r
		      )))
		  e
	       )
	       (Linear_constraints.conj
		  (Linear_constraints.positive_or_null p)
		  (Linear_constraints.conj
		     (Linear_constraints.positive_or_null q)
		     (Linear_constraints.positive_or_null r)))
	    )
	    
	  in

	  let new_constr1 = 
	    (Linear_constraints.conj
	       (Linear_constraints.eq
		  (Linear_constraints.add 
		     p 
		     ((Linear_constraints.add 
			 q 
			 cte1
		      )))
		  e
	       )
	       (Linear_constraints.conj
		  (Linear_constraints.positive_or_null p)
		  (Linear_constraints.positive_or_null q)
	       )
	    )
	  in
	  let new_constr2 = 
	    (Linear_constraints.conj
	       (Linear_constraints.eq
		  (Linear_constraints.add 
		     p
		     ((Linear_constraints.add 
			 q 
			 (Linear_constraints.add 
			    r 
			    cte1))))
		  e
	       ))
	    (Linear_constraints.conj
	       (Linear_constraints.positive_or_null p)
	       (Linear_constraints.conj
		  (Linear_constraints.positive_or_null q)
		  (Linear_constraints.positive_or_null r)
	       )
	    )
	  in
	  let dec2 = 
	    List.fold_left 
	      (fun acc x -> match x with
		 | ([],[],e,phi) -> 
		     (Listutils.flat_map 
			(fun (l1,l2) ->
			   [
			     (* b^p l1 , l2 b^q , b^r *)
			     ([{base = b ; operator = Power p}]
			      @letters_to_factor l1,

			      (letters_to_factor l2) 
			      @[{base = b ; operator = Power q}],

			      {base = b ; operator = Power r}::e,

			      Linear_constraints.conj new_constr2 phi);

			     (* b^p , b^q l1 , l2 b^r *)
			     ([{base = b ; operator = Power p}],

			      [{base = b ; operator = Power q}] 
			      @letters_to_factor l1,

			      (letters_to_factor l2) 
			      @{base = b ; operator = Power r}::e,
			      
			      Linear_constraints.conj new_constr2 phi);


			     (* b^p  , b^q , b^r *)
			     ([{base = b ; operator = Power p}],

			      [{base = b ; operator = Power q}],

			      {base = b ; operator = Power r}::e,
			      
			      Linear_constraints.conj new_constr0 phi);
			     
			   ]
			)
			split2)
		     @acc
		 | ([],e,e',phi) -> 
		     (List.map 
			(fun (l1,l2) -> 
			   ([{base = b ; operator = Power p}]
			    @(letters_to_factor l1),

			    (letters_to_factor l2)@
			    ({base = b ; operator = Power q}::e),

			    e',
			    Linear_constraints.conj new_constr1 phi))
			split2)@acc

		 | (e1,e2,e3,phi) -> acc
	      )
	      []
	      end_dec 
	  in
	    (* Cut twice in the same power *)
	  let split3 = split_again split2 in
	  let dec3 = 
	    List.fold_left 
	      (fun acc x -> match x with
		 | ([],[],e,phi) -> 
		     (List.map 
			(fun (l1,l2,l3) ->
			   ([{base = b ; operator = Power p}]
			    @(letters_to_factor l1),

			    (letters_to_factor l2),

			    (letters_to_factor l3)@
			    {base = b ; operator = Power q}::e,
			    Linear_constraints.conj new_constr1 phi)
			)
			split3)
		     @acc
		 | _ -> acc
	      )
	      []
	      end_dec 

	  (* Cut twice in two different powers *)
	  in
	  let new_constr3 = 
	    Linear_constraints.conj
	      (Linear_constraints.eq
		 (Linear_constraints.add 
		    p (Linear_constraints.add 
			 q (Linear_constraints.add 
			      r cte2)))
		 e
	      )
	      (Linear_constraints.conj
		 (Linear_constraints.positive_or_null p)
		 (Linear_constraints.conj
		    (Linear_constraints.positive_or_null q)
		    (Linear_constraints.positive_or_null r)
		 )
	      )

	  in
	  let dec4 =
	    List.fold_left 
	      (fun acc x -> match x with
		 | ([],[],e,phi) -> 
		     (Listutils.flat_map 
			(fun (l1,l2) ->
			   List.map 
			   (fun (l1',l2') ->
			      ([{base = b ; operator = Power p}]
			       @(letters_to_factor l1'),
			       
			       (letters_to_factor l2')@
			       {base = b ; operator = Power r}::
			       (letters_to_factor l1),

			       (letters_to_factor l2)@
			       {base = b ; operator = Power q}::e,

			       Linear_constraints.conj new_constr3 phi))
			   split2
			)
			split2)
		     @acc
		 | _ -> acc
	      )
	      []
	      end_dec 
	      
	  in pv::qv::rv::new_vars,dec1@dec2@dec3@dec4

    | {base=_ ; operator = Fp(_,_,_) }::r -> 
	failwith "No fp yet in decompose."


let add_in_decomposition2 phi0 w ((c1,c2,phi) as d2) = 
  let new_phi = Linear_constraints.conj phi0 phi in
    if w = [] then [(c1,c2,phi) ] else
      match d2 with 
	| [],c2,phi -> [[],w@c2, new_phi; w,c2,new_phi ;] 
	| c1,c2,phi -> [ w@c1, c2, new_phi; ]

let add_in_decompositions2 phi w d2 =
  List.fold_left 
    (fun acc x -> (add_in_decomposition2 phi w x)@acc)
    []
    d2

let rec decompose2 ({letters = l ;constr = phi } as w) = 
  match l with
    | [] -> [],[[],[],phi]
    | {base = [] ; operator = No}::r -> 
	(decompose2 {w with letters = r})
    | {base = a1::l ; operator = No}::r -> 
	let new_vars,dec = (decompose2 
			      {w with letters = {base = l ; operator = No}::
						  r})
	in
	  new_vars,
	  Listutils.flat_map
	    (fun x -> 
	       add_in_decomposition2 phi[{base = [a1] ; operator = No}] x)
	    dec
    | {base = b ; operator = Power e}::r -> 
	if Linear_constraints.is_cte e then
	  let i = Linear_constraints.val_of_cte e in
	    if Numbers.le i Numbers.zero 
	    then decompose2 {w with letters = r} 
	    else decompose2
	      {w with 
		 letters = {base = b ; operator = No}::
			     {base = b ; 
			      operator = Power 
					   (Linear_constraints.cte 
					      (Numbers.pred i))
			     }
			   ::r}
	else 
	  let new_vars,end_dec = decompose2  {w with letters = r} in

	  (* Do not cut the power at all *)
	  let dec1 = add_in_decompositions2
		       phi
		       [{base = b ; operator = Power e}]
		       end_dec
	  in
	    (* Cut once in the power *)
	  let split2 = split_2 b in
	  let pv = Linear_constraints.make_var_uniq_name "p" 
	  and qv = Linear_constraints.make_var_uniq_name "q" 
	  in
	  let p = Linear_constraints.var pv
	  and q = Linear_constraints.var qv
	  in

	  let new_constr0 = 
	    (Linear_constraints.conj
	       (Linear_constraints.eq
		  (Linear_constraints.add 
		     p 
		     ((Linear_constraints.add 
			 q 
			 cte0
		      )))
		  e
		)
	       (Linear_constraints.conj
		  (Linear_constraints.positive_or_null
		     p)
		  (Linear_constraints.positive_or_null
		     q)
	       )
	    )
	  in
	  let new_constr1 = 
	    (Linear_constraints.conj
	       (Linear_constraints.eq
		  (Linear_constraints.add 
		     p 
		     ((Linear_constraints.add 
			 q 
			 cte1
		      )))
		  e
		)
	       (Linear_constraints.conj
		  (Linear_constraints.positive_or_null p)
		  (Linear_constraints.positive_or_null q)
	       )
	    )
	  in
	  let dec2 = 
	    List.fold_left 
	      (fun acc x -> match x with
		 | ([],e,phi) -> 
		     (Listutils.flat_map 
			(fun (l1,l2) ->
			   [
			     (* b^p l1 , l2 b^q  *)
			     ([{base = b ; operator = Power p}]
			      @letters_to_factor l1,

			      (letters_to_factor l2) 
			      @[{base = b ; operator = Power q}]@e,

			      Linear_constraints.conj new_constr1 phi);
			   ]
			)
			split2)
		     @acc
		 | (e,e',phi) -> acc 
	      )
	      []
	      end_dec 
	  in 
	  let dec3 = 
	    List.fold_left 
	      (fun acc x -> match x with
		 | ([],e,phi) -> 
		     (* b^p , b^q  *)
		     ([{base = b ; operator = Power p}]
			,
			[{base = b ; operator = Power q}]@e,
			Linear_constraints.conj new_constr0 phi)::acc
		 | (e,e',phi) -> acc)
	      []
	      end_dec 
	  in pv::qv::new_vars,dec1@dec2@dec3

    | {base=_ ; operator = _}::r -> 
	failwith "No fp yet in decompose2."

exception No_match
exception Result of 
  Linear_constraints.formula * 
  c_triple * 
  rewrite_rule * 
  Linear_constraints.var_id list

module C = Presburger

let rename_letters renaming l = 
  List.map 
    (function f -> match f with
       | {base = b ; operator = No} ->
	   {base = 
	      List.map 
		(function { a = s ; index = i} ->
		   { a = s ; 
		     index = List.map 
			       (Linear_constraints.rename_expr renaming) i }
		) 
		b ; 
	    operator = No
	   }
       |  {base = b ; operator = Power e} ->
	    {base = 
	       List.map (function {a=s; index = i} ->
			   {a=s; 
			    index = 
			      List.map 
				(Linear_constraints.rename_expr renaming) i}) 
		 b ; 
	     operator = Power (Linear_constraints.rename_expr renaming e)
	    }
	    
       |  {base = b ; operator = _ } ->
	    failwith "TODO in parameterized_rewriting.ml: renaming."
    )
    l
  

let clone_rule {renv = env ; rrule = (g,d)  ; rconstr =  xi} =
  let renaming = Linear_constraints.build_renaming env in
  {rrule = (rename_letters renaming g,
	    rename_letters renaming d)  ; 
   rconstr = Linear_constraints.rename_formula renaming xi;
   renv = List.map (function x -> 
		   try Linear_constraints.VarMap.find x renaming
		   with Not_found -> x)
	    env}

let udecompose w =
(*
  printf " Starting udecompose@."; 
*)
  let free_psi = w.env in
  let new_vars,all_dec_l = decompose w in
(*
    printf " %d decomposition(s) found (non uniform)@." 
      (List.length all_dec_l);
*)
  (*    List.iter (display_dec display sigma) all_dec_l ;*)
  
  (* now keep the uniform decompositions.*)
    new_vars,
let udec = List.filter 
	     (fun (_,_,_,zeta) ->
		(*
		  printf "New_vars = %d@." (List.length new_vars); 
		*)
		let f = 
		  Linear_constraints.equiv
		    w.constr
		    (Linear_constraints.exists_s new_vars zeta)
		in
		  (*
		    printf "@[<hov 2>formula to check :@ %a@]@." Linear_constraints.fprint f; 
		  *)
		  (new_vars = []) or (C.is_valid f)
	     )
	     all_dec_l
in  
(* I SHOULD SORT THIS LIST WHILE BUILDING IT !!! *)
  List.sort (fun (a,b,c,d) (x,y,z,t) -> 
	       let ty = List.length y - List.length b in
	       let tx = List.length x - List.length a in
	       let tz = List.length z - List.length c in
		 if tx+tz <0 then 
		   19 else
		     if tx+tz=0 then 
		       if ty > 0 then 
			 19 
		       else
			 if ty=0 then 
			   if tx < 0 then
			     19 
			   else 
			     if tx = 0 then 
			       if tz < 0 then
				 19 
			       else 
				 if tz=0 then 
				   0 
				 else -19
			     else -19
			 else -19
		     else -19)
    udec


let udecompose2 w =
  let free_psi = w.env in
  let new_vars,all_dec_l = decompose2 w in
(*    printf " %d bidecomposition(s) found@." (List.length all_dec_l);*)
(*    List.iter (display_dec display sigma) all_dec_l ;*)

    (* now keep the uniform decompositions.*)
    new_vars,
    List.filter 
      (fun (_,_,zeta) -> 
	   (new_vars = []) or 
	   (C.is_valid 
	      (Linear_constraints.equiv
		 w.constr
		 (Linear_constraints.exists_s new_vars zeta)
		 ))
	     )
      all_dec_l



let filter_one_rule

  (* The word to filter*) 
  ({env = free_psi ; letters = l ;constr = psi } as w)
  (* The rule to apply *) 
  r 
  (* We assume that the word and the rule do not share variables in their env*)
  =
  let ({renv = free_xi ; rrule = (g,d)  ; rconstr =  xi} as r) = clone_rule r 
  in
    (* printf "Filtering with the rule : "; 
       pretty_print sigma [r];
       printf "@."; 
    *)
    let new_vars,dec_l = udecompose w in
      (*  printf "Decomposition to try :@."; 
	  List.iter (display_dec display sigma) dec_l;
	  printf "@."; 
      *)
    let new_env = new_vars@w.env in
      try List.iter 
	(function (p,l',s,zeta) as position -> 
	   (*
	     printf "Trying decomposition :@.";
	     display_dec display sigma position;
	     printf "@.";
	     printf "Computing similitude formula@."; 
	   *)
	   let sim_constr = 
	     Parameterized_similitude.compute_similitude 
	       {letters = l' ;constr =
		  (* zeta *) (* C'est bizare ici... BUG ?*)
		  Linear_constraints.true_formula ;
		env = new_env
			(* zeta *) }
	       {letters = g ;
		constr =  Linear_constraints.true_formula ;
		env = new_env
			(* xi*) }
	   in
	     (*
	       fprintf std_formatter "sim_constr = %a@." Linear_constraints.fprint sim_constr;
	       fprintf std_formatter "xi = %a@." Linear_constraints.fprint xi;
	       fprintf std_formatter "zeta = %a@." Linear_constraints.fprint zeta;
	     *)
	   let aleph = 
	     Linear_constraints.conj zeta 
	       (Linear_constraints.conj xi sim_constr)
	       
	   in
	     (*
	       fprintf std_formatter "aleph = %a@." Linear_constraints.fprint aleph;
	     *)
	   let existentials = new_vars@free_xi
	   in
	   let filter_condition =
	     Linear_constraints.implies
	       psi
	       (Linear_constraints.exists_s existentials aleph)
	   in
	     (*
	       printf " is_valid ? :@.  ";
	       Linear_constraints.print filter_condition;
	       printf "@.";
	     *)
	     if C.is_valid filter_condition
	     then (
	       (*
		 printf "true@.";
	       *)
	       printf "Applying the rule : "; 
	       pretty_print [r];
	       printf "@.At position :@ ";
	       display_dec position ;
	       printf "@.";
	       raise (Result(aleph,position,r,new_env@free_xi)))
	     else 
	       (* printf "false@."; *) ()
	)
	dec_l;
	(* printf "No match@.";*)
	raise No_match
      with Result (x,y,r,e) -> x,y,r,e

exception Reducible

let is_reducible r w =
  try
    List.iter (function x ->
		 try
		   ignore(filter_one_rule w x);
		   raise Reducible
		 with
		     No_match -> ()
	      )
      r;
    false
  with
    | Reducible -> true

let is_nf w r = not (is_reducible w r)


exception Nf of Parameterized_words.word

let reduce r w = 
    try
      List.iter (function x ->
		   try
		     let x,y,z,e = filter_one_rule w x in
		       raise (Result(x,y,z,e))
		   with
		       No_match -> ()
		) 
	r;
      raise (Nf w)
    with
      | Result (aleph,(p,l',s,zeta),rule,env) -> 
	  { letters = p@(snd rule.rrule)@s;
	    constr = aleph;
	    env = env
	  }

let rec local_normalize depth r w = 
  printf "Normalizing step %d.@." depth ;
  User_parameterized_words.pretty_print w;
  printf "@.";
  try 
    local_normalize (depth+1)  r 
      (let w' = reduce r w in
	 {letters = w'.letters;
	  constr = w'.constr;
	  env = w'.env })
  with 
      Sys.Break -> 
	printf "Stopped normalization at step %d." depth;
	raise (Nf w)

let normalize r w = 
  try 
    local_normalize 1 r w;
    assert false
  with
      Nf w -> w
	
let display_cp (u,v,aleph) =
  
    printf "====CP====@.";
     User_parameterized_words.print_letters u;
    printf "@.AND@.";
    User_parameterized_words.print_letters v;
    printf "@.Constraint:@ ";
    Linear_constraints.print aleph;
    printf "@.=========@."
 
let compute_critical_pairs rule1 rule2 = match rule1 with
  | ({rrule = (l1,r1)  ; rconstr =  c1 ; renv = env1}) ->
      let {rrule = (l2,r2)  ; rconstr =  c2 ; renv = env2} = clone_rule rule2 
      in
      let new_vars_dec_1,dec1 = udecompose 
				  {letters = l1 ;constr = c1 ; env = env1} 
      in
      let new_vars_d1,d1 = udecompose2 
			     {letters = l1 ;constr = c1 ; env  = env1} 
      in
      let new_vars_d2,d2 = udecompose2
			     {letters = l2 ;constr = c2 ; env = env2} 
      in
      let free_vars_dec1 = new_vars_dec_1@env1 in
      let free_vars_d1 = new_vars_d1@env1 in
      let free_vars_d2 = new_vars_d2@env2 in
      let all_free_vars = free_vars_d1@free_vars_d2 in
      let pc1 =
	let aleph = Parameterized_similitude.compute_similitude 
		      {letters = l2 ;constr = c2; env = env2}
		      {letters = l1 ;constr = c1; env = env1}
	in if C.is_satisfiable aleph then [(r1,r2,aleph,env1@env2,
					    (rule1,rule2,"pc1"))]
	  else []
      in let pc2 =
	  List.fold_left 
	    (fun acc (x1,y1,phi1) ->
	       let raw_aleph = Parameterized_similitude.compute_similitude 
				 {letters = l2;
				  constr = c2;
				  env = env2}
				 {letters = y1;
				  constr = phi1; 
				  env = free_vars_d1}
	       in let x1_is_epsilon = 
		   Parameterized_similitude.is_epsilon 
		     {letters = x1; constr = Linear_constraints.true_formula; env = free_vars_d1} 
	       in let aleph = Linear_constraints.conj 
				raw_aleph
				(Linear_constraints.neg x1_is_epsilon)
	       in
		 if C.is_satisfiable aleph then 
		   (x1@r2,r1,aleph,free_vars_d1@env2,(rule1,rule2,"pc2"))::acc
		 else acc)
	    pc1 d1
      in let pc3 =
	   List.fold_left 
	    (fun acc1 (x1,y1,phi1) ->
	       List.fold_left
	     (fun acc2 (x2,y2,phi2) ->
		let raw_aleph = Parameterized_similitude.compute_similitude 
				 {letters = x2;
				  constr = phi2;
				  env = free_vars_d2}
				 {letters = y1;
				  constr = phi1; 
				  env = free_vars_d1}
	       in let x1_is_epsilon = 
		   Parameterized_similitude.is_epsilon 
		     {letters = x1; constr = Linear_constraints.true_formula; env = free_vars_d1} 
	       in let y1_is_epsilon = 
		    Parameterized_similitude.is_epsilon 
		      {letters = y1; constr = Linear_constraints.true_formula; env = free_vars_d1} 
	       in let y2_is_epsilon = 
		   Parameterized_similitude.is_epsilon 
		     {letters = y2; constr = Linear_constraints.true_formula; env = free_vars_d2} 
	       in let x2_is_epsilon = 
		    Parameterized_similitude.is_epsilon 
		     {letters = x2; constr = Linear_constraints.true_formula; env = free_vars_d2} 
	       in let aleph = Linear_constraints.conj 
				(Linear_constraints.conj 
				   (Linear_constraints.conj 
				      (Linear_constraints.conj 
					 (Linear_constraints.neg x1_is_epsilon)
					 (Linear_constraints.neg y2_is_epsilon)
				      )
				      (Linear_constraints.neg y1_is_epsilon))
				   (Linear_constraints.neg x2_is_epsilon))
				raw_aleph
	       in
		 if C.is_satisfiable aleph then 
		   (r1@y2,x1@r2,aleph,all_free_vars,(rule1,rule2,"pc3"))::acc2
		 else acc2)
	       acc1 d2)
	    pc2 d1

      in let pc4 =
	  List.fold_left 
	    (fun acc (x2,y2,phi2) ->
	       let raw_aleph = Parameterized_similitude.compute_similitude 
				 {letters = l1;
				  constr = c1;
				  env = env1}
				 {letters = x2;
				  constr = phi2; 
				  env = free_vars_d2}
	       in let y2_is_epsilon = 
		   Parameterized_similitude.is_epsilon 
		     {letters = y2; constr = Linear_constraints.true_formula ; env = free_vars_d2} 
	       in let x2_is_epsilon = 
		   Parameterized_similitude.is_epsilon 
		     {letters = x2; constr = Linear_constraints.true_formula ; env = free_vars_d2} 
	      in let aleph = Linear_constraints.conj
				raw_aleph
			       (Linear_constraints.conj
				  (Linear_constraints.neg y2_is_epsilon)
				  (Linear_constraints.neg x2_is_epsilon)
			       )
	       in
		 if C.is_satisfiable aleph then 
		   (r1@y2,r2,aleph,free_vars_d2@env1,(rule1,rule2,"pc4"))::acc
		 else acc)
	    pc3 d2

      in let pc5 = 
	  List.fold_left 
	    (fun acc (x1,x2,y1,phi1) -> 
	       let raw_aleph = 
		 Parameterized_similitude.compute_similitude 
		   {letters = l2 ;constr = c2; env = env2}
		   {letters = x2 ;constr = phi1; env = free_vars_dec1}
   in let y1_is_epsilon = 
		   Parameterized_similitude.is_epsilon 
   {letters = y1; 
   constr = Linear_constraints.true_formula ; 
   env = free_vars_dec1} 
	       in let x1_is_epsilon = 
		   Parameterized_similitude.is_epsilon 
		     {letters = x1; constr = Linear_constraints.true_formula ; env = free_vars_dec1} 
	       in let aleph = Linear_constraints.conj
				(Linear_constraints.conj
				   (Linear_constraints.neg y1_is_epsilon)
				   (Linear_constraints.neg x1_is_epsilon))
				raw_aleph
	       in
	       if C.is_satisfiable aleph then
		 begin
		   (*		   printf "---------------------------@.";
				   fprintf std_formatter "y1_is_eps =@ %a@." Linear_constraints.fprint y1_is_epsilon;
				   fprintf std_formatter "x1_is_eps =@ %a@." Linear_constraints.fprint x1_is_epsilon;
				   fprintf std_formatter "aleph =@ %a@." Linear_constraints.fprint aleph;
				   display_cp display sigma (r1,x1@r2@y1,aleph); 
		   *)		   
		   (r1,x1@r2@y1,aleph,free_vars_dec1,(rule1,rule2,"pc5"))::acc
		 end
		 else acc)
	    pc4 dec1
      in
	pc5


let critical_pairs r1 r2 = 
  let internal_cp = compute_critical_pairs r1 r2 in
    List.map (function (l,r,c,e,_) -> 
		{env=e;letters=l;constr=c},
		{env=e;letters=r;constr=c}) internal_cp

let all_CP r = 
  printf "Computing CP.@.";
  let c = Listutils.flat_map
    (function x -> Listutils.flat_map 
	 (function y -> compute_critical_pairs x y) r) r 
  in 
    printf "Found %d CP.@." (List.length  c);
    c

let is_joinable r =
  let trivial = ref 0 in
  let hard = ref 0 in
    fun (u,v,aleph,env,(r1,r2,pc_kind)) ->
      let w1 = {letters = u ;constr = aleph ; env = env }  in
      let w2 = {letters = v ;constr = aleph ; env = env }  in
	display_cp (u,v,aleph); 
	printf "Comes from rules : @.";
	print_rule r1;
	printf "@.";
	print_rule r2;
	printf "@.This pc is of kind %s.@." pc_kind;
	printf "Testing similitude of cp.@.";
	if (Parameterized_similitude.test_weak_similitude 
	      w1 
	      {w2 with constr = Linear_constraints.true_formula }
	   )
	then 
	  begin 
	    incr trivial ; 
	    printf "TRIVIALIZED(trivial cp %d/non trivial %d)@." 
	      !trivial 
	      !hard;
	    true 
	  end
	else begin 
	  incr hard;
	  printf "Not a trivial cp(non trivial cp %d/trivial %d)@." 
	    !hard !trivial;
	  let nw1 = (normalize r w1) in
	    printf "Normalized branch one.@.";
	    let nw2 = (normalize r w2) in
	      printf "Normalized branch two.@.";
	      if (Parameterized_similitude.test_weak_similitude nw1 nw2)
	      then
		begin 
		  (* display_cp display sigma 
		    (nw1.letters,nw2.letters,nw1.constr); *)
		  printf "Normalized cp.@.";
		  true end
	      else
		begin 
		  printf "Cannot join words:@.";
		  User_parameterized_words.pretty_print nw1;
		  printf "@.And:@.";
		  User_parameterized_words.pretty_print nw2;
		  printf "@.";
		  false
		end
	end

let count_trivial display sigma r env = 
  let trivial = ref 0 in
  let hard = ref 0 in
    fun (u,v,aleph) ->
      let w1 = {letters = u ; constr = aleph ; env = env } in
      let w2 = {letters = v ; constr = aleph ; env = env } in
	display_cp (u,v,aleph); 
	printf "Testing similitude@.";
	if (Parameterized_similitude.test_weak_similitude 
	      w1 {w2 with constr = Linear_constraints.true_formula }
	   )
	then 
	  begin incr trivial ; printf "TRIVIALIZED(%d)@." !trivial; true end
	else begin 
	  incr hard ; printf "Not a trivial cp(%d)@." !hard ; true
	end

let is_localy_confluent r =
  List.for_all (is_joinable r) (all_CP r)

let is_localy_confluent_extended r1 r2 =
  List.for_all (is_joinable (r2@r1)) (all_CP r1)

let from_abstract_srs s l =
  let params = s#parameters#parameters in
    List.map 
      (function l,r,constr -> 
	 let env,c = Linear_constraints.from_abstract_formula params constr in
	 let env,l' = Listutils.fold_right_env 
			Parameterized_words.from_abstract_factor env l in
	 let env,r' = Listutils.fold_right_env from_abstract_factor env r in
	 let local_vars = Listutils.map_filter 
		     snd
		     (function x -> not (List.memq x params))
		     env
	 in
	   { renv = local_vars ;  
	     rrule = l',r' ; 
	     rconstr = c }
      )
      l
      
(*i
Local Variables:
compile-command: "make -C .. opt"
End:
i*)
