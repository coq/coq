open Parameterized_words
open Linear_constraints

let verbose = ref 0

let debug n s = 
  if n <= !verbose
  then Format.printf "\tdebug:%s@." s

let compare_letter b c = 
  if b.a = c.a && (List.length b.index)=(List.length c.index) then 
    conj_list (List.map2 Linear_constraints.eq b.index c.index)
  else 
    false_formula

let compare_letters b c =
  assert (List.length b = List.length c);
  conj_list (List.map2 (fun x y -> compare_letter x y) b c)


(* Choose here the constraint solver you want.
   It must provide :
   \begin{itemize}
   \item [from_abstract_formula : Abstract_constraint.formula -> t]
   \item [is_valid : t -> bool]
   \end{itemize}
*)

open Linear_constraints


let rec isprefix (x',u',phi) = 
  match (x',u') with
    | [],u -> phi
    | ai::x,{base = [] ; operator = _ }::r1 -> isprefix(x',r1,phi)
    | ai::x,[] -> false_formula
    | ai::x, 
      {base = aj::l ; operator = No }::u-> 
	isprefix (x,{base = l ; operator = No }::u,
		  conj (compare_letter ai aj) phi)
    | ai::x, 
      {base = aj::y ; operator = (Power n)}::u -> 
	disj 
	  (isprefix (x',u,
		     conj (null n) phi))
	  (isprefix (x,{base = y@[aj] ; 
			operator = Power(sub n Linear_constraints.one)}::
		       {base = y; 
			operator = No}::
		       u,
		     conj (conj 
			     (positive n)
			     (compare_letter ai aj)) phi))

    | _::_, {base=_::_; operator=Fp (_, _, _)}::_
	-> failwith "TODO : no fp yet in isprefix."

let rec removeprefix (x',u',phi) = 
  match (x',u') with
    | [],u -> [u,phi]
    | ai::x,{base = [] ; operator = _ }::r1 -> removeprefix(x',r1,phi)
    | ai::x,[] -> []
    | ai::x, 
      {base = aj::l ; operator = No }::u-> 
	removeprefix (x,{base = l ; operator = No }::u,
		      conj (compare_letter ai aj) phi)
    | ai::x, 
      {base = aj::y ; operator = (Power n)}::u -> 

	(removeprefix (x',u,
		       conj (null n) phi))
	@
	(removeprefix (x,{base = y@[aj] ; 
			  operator = Power(sub n Linear_constraints.one)}::
			 {base = y; 
			  operator = No}::
			 u,
			 conj (conj 
				 (positive n)
				 (compare_letter ai aj)) phi))
	  
    | _::_, {base=_::_; operator=Fp (_, _, _)}::_
	-> failwith "TODO : no fp yet in isprefix."

let rec hd_n n l =
  let rec f n d e = 
    if n = 0 then (List.rev d),e else 
      match e with 
	| x::r -> f (n-1) (x::d) r
	| [] -> assert false
  in
    f n [] l

let pref n l = assert ((List.length l) >=n) ; fst (hd_n n l)
let suff n l = assert ((List.length l) >=n) ; fst (hd_n n (List.rev l))

let rec rotate_right n l = 
  match l with [] -> l
    | x::r ->
	match n with 
	  | 0 -> l
	  | n -> rotate_right (n-1) r@[x]


let lfact (x,u,phi) = 
  let lx = List.length x in
  let rec lfact (n,u',phi) = 
    match u' with 
	(* Normalization *)
      | {base = b1 ; operator = No}::
	  {base = b2 ; operator = No}::r ->
	  debug 5 "Normalize 1";
	  lfact (n,
		 {base = b1@b2 ; operator = No}::r,
		 phi)
      | {base = [] ; operator = No}::r ->
	  debug 5 "Normalize 2";
	  lfact (n,r,phi)
      | [] -> debug 5 "Normalize 3"; [n,u',phi]
      | {base = b1 ; operator = No}::r ->
	  if List.length b1 >= lx then (* Long simple prefix *)
	    begin
	      debug 5 "Long Simple Prefix.";
	      let b1',b1'' = hd_n lx b1 in
		(n,u',conj (neg (compare_letters b1' x)) phi)::
		(lfact ((add n one),
		      {base = b1'' ; operator = No}::r,
		      conj (compare_letters b1' x) phi))
	    end
	  else begin match r with 	 (* Short simple prefix *) 
	    | [] -> debug 5 "Short Simple Prefix (empty)."; [n,u',phi]
	    | {base = z ; operator = Power p }::v ->
		debug 5 "Short Simple Prefix (power).";
		let remove_p = removeprefix (x,u',phi) in
		(n,u',conj phi (List.fold_left 
				  (fun acc (_,f) -> conj acc (neg f) ) 
				  true_formula remove_p))::
		  (Listutils.flat_map (fun (v',phi') -> 
			       lfact (add n one,
				      v',
				     conj phi' phi)) remove_p)
	    | {base = _ ; operator = Fp(_,_,_)}::_ ->
		failwith "No fp in lfact yet."
	    | {base = _ ; operator = No }::_ ->
		assert false
	  end

      (* Starting with power *)
      | {base = y ; operator = Power p }::u -> 
	  if List.length y = lx then begin
	    debug 5 "Starting with Power same length.";
	    let c1 = compare_letters x y in
	    let c2 = null p in
	    let f1 = lfact (add n p,u, conj phi c1) in
	    let f2 = lfact (n,u, conj phi c2) in
	    let result = (n,u', conj phi (conj (neg c1) (neg c2))) in
	      result::(f1@f2)
	  end else begin
    	    debug 5 "Starting with Power different length.";
	    let ly = List.length y in
	    let tmp = Int_utils.ppcm lx ly in
	    let dx = tmp/lx in 
	    let dy = tmp/ly in
(*	    Format.printf "dx=%d dy=%d\n" dx dy; *)
	    let ydy = {base = Listutils.power y dy ; operator = No} in
	    let xdx = {base = Listutils.power x dx ; operator = No} in
	    let rec f1 acc r = if r < 0 then 
	      acc
	    else 
	      f1 (lfact(n,{base = Listutils.power y r ; operator = No}::u,
		    conj phi (eq p (cte (Numbers.of_int r))))@acc)
		(r-1)
	     
	    in
	    let rec f2 acc r = if r < 0 then acc 
	    else
	      f2 ((add n (cte (Numbers.of_int r)),
		   {base = (rotate_right dy y) ; 
		    operator = Power (add p (cte (Numbers.of_int (-r))))}::
		    {base = (suff (lx * r) ydy.base);
		     operator = No}::
		   u,
		   (conj phi 
		      (conj (ge p (cte (Numbers.of_int dy))) 
			 (conj 
			    (compare_letters 
			       (Listutils.power x r)
			       (pref (lx*r) ydy.base)
			    )
			    (neg (compare_letters 
				    (Listutils.power x (r+1))
				    (pref 
				       (lx*(r+1)) 
				       ydy.base)
			    ))
			 )
		      )
		   )
		  )
		  ::acc)
		(r-1)
	    in
	    let rec f3 acc r = if r<0 then acc else
	      f3 ((lfact(add n (Linear_constraints.div 
				   ( times 
				       (Numbers.of_int dx)
				       (add 
					  p
					  (minus(cte (Numbers.of_int r)))
				       )
				   )
				   (Numbers.of_int dy)
				),
			 {base = Listutils.power y r ; operator = No}::u,
			 conj phi 
			   (conj 
			      (compare_letters xdx.base ydy.base) 
			      (conj 
				 (ge p (cte (Numbers.of_int dy)))
				 (divides
				    (Numbers.of_int dy)
				    (add 
				       p 
				    (cte (Numbers.of_int (-r)))
				    )
				 ))))
		  )@acc) (r-1)
	    in
	      begin
		debug 5 "R3";
		let r3 = (f3 [] (dy-1)) in
		  debug 5 "R2";
		  let r2 = (f2 r3 (dx-1)) in
		    debug 5 "R1";
		  f1 r2 (dy-1)
	      end
	  end
      | {base = _ ; operator = Fp(_,_,_) }::_ -> 
	  failwith "No fp in lfact yet (2)."
  in
    lfact (Linear_constraints.zero,u,phi)

let compute_similitude w1 w2 = 
  let rec f triple = 
    match triple with 
      | (* Stop everything if the constraint is false *)
	_,
	_,
	phi when 
	  not (Presburger.is_satisfiable phi) ->  
	  debug 5 "\t\t\t\tCUT A BRANCH in similitude computation";
	  false_formula

	(* Some degenerated cases *)
      | {base = [] ; operator = _ }::r1,
	w2,
	phi -> 
	  debug 5 "Empty/Any";
	  f (r1,w2,phi)
      | w1,
	{base = [] ; operator = _ }::r2,
	phi -> 
	  debug 5 "Any/Empty";
	  f (w1,r2,phi)
	    
	    (* epsilon/epsilon *)
      | [],[],phi -> 
	  debug 5 "Epsilon/Epsilon"; 
	  phi
	    
	    (* epsilon/letter *)
      | {base = b::_ ; operator = No }::r ,[],phi  ->
	  debug 5 "Epsilon/Letter1"; 
	  false_formula

      | [],{base = b::_ ; operator = No }::r ,phi ->
	  debug 5 "Epsilon/Letter2"; 
	  false_formula

	    (* letter/letter *)
      | {base = a1::l1 ; operator = No }::r1,
	{base = a2::l2 ; operator = No }::r2,
	phi -> 
	  debug 5 "Letter/Letter";
	  f ({base = l1 ; operator = No }::r1,
	     {base = l2 ; operator = No }::r2 ,
	     conj (compare_letter a1 a2) phi;
	    )

      | {base = b ; operator = (Power n) }::r ,[],phi  ->
	  debug 5 "Epsilon/Power1"; 
	  f (r ,[], conj (eq n zero) phi)

      | [],{base = b ; operator = (Power n) }::r ,phi ->
	  debug 5 "Epsilon/Power2"; 
	  f (r ,[], conj (null n) phi)

(*i      | {base = aj::x ; operator = (Power n) }::v ,
	{base = ai::y ; operator = No }::u,phi ->
	  debug 5 "Letter/Power1"; 
	  disj 
	    (f ({base = ai::y ; operator = No }::u,
		v,
		conj phi (null n)))
	    (f({base = y ; operator = No }::u,
	       {base = x@[aj] ; 
		operator = Power(add n one)}::
	       {base = x ; operator = No }::v,
	       conj 
		 (compare_letter ai aj)
		 (conj phi (positive n)))
	    )
i*)
      | {base = aj::x ; operator = (Power n) }::v ,
	{base = ai::y ; operator = No }::u,phi
      | {base = ai::y ; operator = No }::u,
	{base = aj::x ; operator = (Power n) }::v ,phi ->
	  debug 5 "Letter/Power";
	  let cl = compare_letter ai aj in 
	  if  cl = false_formula then 
	    (f ({base = ai::y ; operator = No }::u,
		v,
		conj phi (null n)))
	  else
	    disj 
	      (f ({base = ai::y ; operator = No }::u,
		  v,
		  conj phi (null n)))
	      (f({base = y ; operator = No }::u,
	       {base = x@[aj] ; 
		operator = Power(sub n one)}::
	       {base = x ; operator = No }::v,
	       conj 
		 cl
		 (conj phi (positive n)))
	      )
	    
      | {base = y ; operator = (Power p) }::v,
	{base = x ; operator = (Power n) }::u ,phi ->
	  debug 5 "Power/Power"; 
	  begin
	    let lx = List.length x in
	    let ly = List.length y in
	    let delta_length =  lx - ly in
	    let lconstraint = delta_length = 0 in
	    let prefix_constraint = 
	      Presburger.is_valid 
		(conj (neg (isprefix(x,u,phi))) (neg (isprefix(y,v,phi))))
	    in
	  if lconstraint && prefix_constraint then begin  
	    debug 5 " Case 1.";
	    disj
	      (conj (f(u,v,phi)) 
		 (conj (eq n p) 
		    (conj(neg (null n)) 
		       (compare_letters x y))))
	      (disj
		 (f ({base = x ; operator = (Power n) }::u ,
		     v,
		     conj phi (null p)))
		 (f ({base = y ; operator = (Power p) }::v ,
		     u,
		     conj phi (null n)))
	      )
	  end else
	    if lx>ly then begin
	      debug 5 " Case 2.";
	      f({base = x ; operator = (Power n) }::u,
		{base = y ; operator = (Power p) }::v,
		phi) 
	    end else if 
	      (Presburger.is_satisfiable 
		 (disj (isprefix(x,u,phi)) 
		    (isprefix(x,{base = y ; operator = (Power p) }::v,phi))))
	    then begin
	      debug 5 (Format.sprintf" Case 3(%b)." (lx<ly));
	      let l1 = lfact (x,u,phi) in
	      let l2 = lfact 
			 (x,({base = y ; operator = (Power p) }::v), phi) in
		(*	      Format.printf 
			      "u is %d and y is %d and v is %d.\n" 
			      (List.length u) (List.length y) (List.length v) ;
			      Format.printf "Lfact1 is %d and Lfact2 is %d.\n" (List.length l1)
			      (List.length l2);
		*)	      
		List.fold_left 
		  (fun acc (n',u',phiu') -> 
		     List.fold_left 
		     (fun acc' (p',v',phiv') ->
			disj
			(f({base = x ; operator = (Power (add n n')) }::u' ,
			   {base = x ; operator = (Power p') }::v',
			   conj (conj (phiu') (phiv')) phi ))
			acc' 
		     )
		     acc
		     l2
		  )
		  false_formula l1
	    end else begin debug 5 "Stop looping case" ; false_formula end
	  end  
      | _ -> failwith "TODO : no finite products yet."
  in
    debug 5 "Starting similitude computation";
    let phi = f (w1.letters ,w2.letters , conj w1.constr w2.constr) in
      debug 5 "End of similitude computation";
      phi

      

let test_similitude w1 w2 =
  let chi = compute_similitude w1 w2 in
  let c2 = equiv w1.constr w2.constr
  in
    debug 5 "End of equivalence of similitude computation.\
               \nStarting implication."; 
    let c1 =  implies (conj w1.constr w2.constr) chi
    in
      debug 5 "End of similitude computation";
      (Presburger.is_valid c1) && (Presburger.is_valid c2)

let test_weak_similitude w1 w2 =
  let chi = compute_similitude
	      {w1  with constr = true_formula}
	      {w2  with constr = true_formula} in
  let c1 =  implies (conj w1.constr w2.constr) chi
  in
    debug 5 "Done with presburgerization. Validity starting now.";
    (*    C.print c1; *)
    let v = Presburger.is_valid c1 in
      debug 5 "Done with Validity.";
      v

let is_epsilon w =
  compute_similitude w {env = [] ; letters = [] ; constr = true_formula}
