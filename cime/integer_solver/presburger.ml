

open Hcons;;
open Linear_constraints;;


(*

\subsection{A probabilistic tautology checker, for debugging purpose}


*)


let random_instance bound vars =
  List.fold_left 
    (fun acc v -> 
       VarMap.add v (Numbers.of_int(Random.int(bound*2+1)-bound)) acc) 
    VarMap.empty vars
;;

let naive_equivalence f1 f2 bound num_tests =

  let v = free_vars_env (free_vars f1) f2 in
  let rec loop n =
    if n<0 then true 
    else
      let t = random_instance bound v in
      let g1 = inst t f1
      and g2 = inst t f2
      in 
      if g1==g2 then loop (pred n) else false
	
  in loop num_tests
;;

(*

  \subsection{Conjunction, with simplifications on the fly}

*)

exception Degenerate;;

(*

  [add_pos_in_conj ef e fs1 fs2] builds the conjunct of the formula
  [e>=0], and sets of formulas [fs1] and [fs2], checking possible
  simplifications between [e>=0] and [fs1]. It assumes
  simplifications between [e>=0] and [fs2] already checked. It also assumes
  simplifications between [fs1] and [fs2] already checked. 
  [ef] is [e>=0] kept as in hashconsed formula, for efficiency.

  It raises [Degenerate] if it is unsatisfiable, for example if [e] is
  $x$ and $fs1$ contains $x<0$.

*)


let rec add_pos_in_conj ef e fs1 fs2 =
  Ptset.case fs1
    (fun () -> Ptset.add ef fs2)
    begin
      fun f fs1' ->
	match f.node with
	 | Null(e') ->
	     let d = sub e e' in
	     if is_cte d 
	     then 
	       (* si on a  e >= 0 /\ e' = 0 avec
		  e - e' = cte :
		  si cte >= 0 : on simplifie en e' = 0
		  si cte < 0 : on degenere en False
	       *)
	       if Numbers.ge (val_of_cte d) Numbers.zero 
	       then Ptset.union fs1 fs2
	       else raise Degenerate
	     else 
	       let d = add e e' in
	       if is_cte d 
	       then 
		 (* si on a  e >= 0 /\ e' = 0 avec
		    e + e' = cte :
		    si cte >= 0 : on simplifie en e'=0
		    si cte < 0 : on degenere en False
		 *)
		 if Numbers.ge (val_of_cte d) Numbers.zero
		 then Ptset.union fs1 fs2
		 else raise Degenerate
	       else
		 add_pos_in_conj ef e fs1' (Ptset.add f fs2)
	 | PositiveOrNull(e') ->
	     let d = sub e e' in
	     if is_cte d 
	     then 
		 (* si on a  e >= 0 /\ e' >= 0 avec
		    e - e' = cte :
		    si cte >= 0 : on simplifie en e' >= 0
		    si cte < 0 : on simplifie en e >= 0
		 *)
	       if Numbers.ge (val_of_cte d) Numbers.zero 
	       then Ptset.union fs1 fs2
	       else Ptset.add ef (Ptset.union fs1' fs2)
	     else 
	       let d = add e e' in
	       if is_cte d 
	       then 
		 (* si on a  e >= 0 /\ e' >= 0 avec
		    e + e' = cte :
		    si cte > 0 : on ne simplifie rien
		    si cte = 0 : on simplifie en e'=0
		    si cte < 0 : on degenere en False
		 *)
		 if Numbers.gt (val_of_cte d) Numbers.zero
		 then add_pos_in_conj ef e fs1' (Ptset.add f fs2)
		 else
		   if Numbers.is_zero (val_of_cte d)
		   then Ptset.add (null e') (Ptset.union fs1' fs2)
		   else raise Degenerate
	       else
		 add_pos_in_conj ef e fs1' (Ptset.add f fs2)
	 | _ -> add_pos_in_conj ef e fs1' (Ptset.add f fs2)
    end
;;

	
let rec add_null_in_conj ef e fs1 fs2 =
  Ptset.case fs1
    (fun () -> Ptset.add ef fs2)
    begin
      fun f fs1' ->
	match f.node with
	 | Null(e') ->
	     let d = sub e e' in
	     if is_cte d 
	     then 
	       (* si on a  e = 0 /\ e' = 0 avec
		  e - e' = cte :
		  si cte = 0 : on simplifie en e' = 0
		  si cte <> 0 : on degenere en False
	       *)
	       if Numbers.is_zero (val_of_cte d)
	       then Ptset.union fs1 fs2
	       else raise Degenerate
	     else 
	       let d = add e e' in
	       if is_cte d 
	       then 
		 (* si on a  e = 0 /\ e' = 0 avec
		    e + e' = cte :
		    si cte = 0 : on simplifie en e'=0
		    si cte <> 0 : on degenere en False
		 *)
		 if Numbers.is_zero (val_of_cte d)
		 then Ptset.union fs1 fs2
		 else raise Degenerate
	       else
		 add_null_in_conj ef e fs1' (Ptset.add f fs2)
	 | PositiveOrNull(e') ->
	     let d = sub e e' in
	     if is_cte d 
	     then 
		 (* si on a  e = 0 /\ e' >= 0 avec
		    e - e' = cte :
		    si cte <= 0 : on simplifie en e = 0
		    si cte > 0 : on degenere en False
		 *)
	       if Numbers.le (val_of_cte d) Numbers.zero 
	       then Ptset.add ef (Ptset.union fs1' fs2)
	       else raise Degenerate
	     else 
	       let d = add e e' in
	       if is_cte d 
	       then 
		 (* si on a  e = 0 /\ e' >= 0 avec e + e' = cte :
		    cela implique e' = - e + cte = cte donc : 
		    si cte >= 0 : on simplifie en e=0
		    si cte < 0 : on degenere en False
		 *)
		 if Numbers.ge (val_of_cte d) Numbers.zero
		 then Ptset.add ef (Ptset.union fs1' fs2)
		 else raise Degenerate
	       else
		 add_null_in_conj ef e fs1' (Ptset.add f fs2)
	 | _ -> add_null_in_conj ef e fs1' (Ptset.add f fs2)
    end
;;

	
let add_in_conj f l =
  match f.node with
    | Null(e) -> add_null_in_conj f e l Ptset.empty
    | PositiveOrNull(e) -> add_pos_in_conj f e l Ptset.empty
    | Not(g) ->
	begin
	  match g.node with
	    | PositiveOrNull(e) -> 
		let e = sub minus_one e in
		let f = positive_or_null e in
	      add_pos_in_conj f e l Ptset.empty
	    | _ -> Ptset.add f l
	end
    | _ -> Ptset.add f l
;;


let conj f1 f2 = 
  let f = Linear_constraints.conj f1 f2 in
  try
    match f.node with
      | And(s,l) -> 
	  let e = Ptset.fold add_in_conj l Ptset.empty in
	  map_conj_no_subst (fun f -> f) s e
      | _ -> f
  with
      Degenerate -> false_formula

(*

  [map_conj_list f l] return the conjunction of formulas f(x) for each x in l

*)

let map_conj_list f l =
  let rec aux f l accu =
    match l with
      | [] -> accu
      | x::l -> aux f l (conj (f x) accu)
  in aux f l true_formula

let conj_list l =
  let rec aux l accu =
    match l with
      | [] -> accu
      | x::l -> aux l (conj x accu)
  in aux l true_formula


(*

  \subsection{Disjunction, with simplifications on the fly}

*)


let rec add_pos_in_disj ef e fs1 fs2 =
  Ptset.case fs1
    (fun () -> Ptset.add ef fs2)
    begin
      fun f fs1' ->
	match f.node with
	 | Null(e') ->
	     let d = sub e e' in
	     if is_cte d 
	     then 
	       (* si on a  e >= 0 \/ e' = 0 avec
		  e - e' = cte :
		  si cte >= 0 : on simplifie en e >= 0
		  si cte < 0 : on ne simplifie rien 
	       *)
	       if Numbers.ge (val_of_cte d) Numbers.zero 
	       then Ptset.add ef (Ptset.union fs1' fs2)
	       else add_pos_in_disj ef e fs1' (Ptset.add f fs2)
	     else 
	       let d = add e e' in
	       if is_cte d 
	       then 
		 (* si on a  e >= 0 \/ e' = 0 avec
1		    e + e' = cte :
		    si cte >= 0 : on simplifie en e >= 0
		    si cte < 0 : on ne simplifie rien 
		 *)
		 if Numbers.ge (val_of_cte d) Numbers.zero
		 then Ptset.add ef (Ptset.union fs1' fs2)
		 else add_pos_in_disj ef e fs1' (Ptset.add f fs2)
	       else
		 add_pos_in_disj ef e fs1' (Ptset.add f fs2)
	 | PositiveOrNull(e') ->
	     let d = sub e e' in
	     if is_cte d 
	     then 
		 (* si on a  e >= 0 \/ e' >= 0 avec
		    e - e' = cte :
		    si cte <= 0 : on simplifie en e' >= 0
		    si cte > 0 : on simplifie en e >= 0
		 *)
	       if Numbers.le (val_of_cte d) Numbers.zero 
	       then Ptset.union fs1 fs2
	       else Ptset.add ef (Ptset.union fs1' fs2)
	     else 
	       let d = add e e' in
	       if is_cte d 
	       then 
		 (* si on a  e >= 0 \/ e' >= 0 avec
		    e + e' = cte :
		    si cte >= -1 : on degenere en True
		    si cte <= -2 : on ne simplifie rien
		 *)
		 if Numbers.ge (val_of_cte d) Numbers.minus_one
		 then raise Degenerate
		 else
		   add_pos_in_disj ef e fs1' (Ptset.add f fs2)
	       else
		 add_pos_in_disj ef e fs1' (Ptset.add f fs2)
	 | _ -> add_pos_in_disj ef e fs1' (Ptset.add f fs2)
    end
;;

	
let rec add_null_in_disj ef e fs1 fs2 =
  Ptset.case fs1
    (fun () -> Ptset.add ef fs2)
    begin
      fun f fs1' ->
	match f.node with
	 | Null(e') ->
	     let d = sub e e' in
	     if is_cte d 
	     then 
	       (* si on a  e = 0 \/ e' = 0 avec
		  e - e' = cte :
		  si cte = 0 : on simplifie en e' = 0
		  si cte <> 0 : on ne simplifie rien
	       *)
	       if Numbers.is_zero (val_of_cte d)
	       then Ptset.union fs1 fs2
	       else add_null_in_disj ef e fs1' (Ptset.add f fs2)
	     else 
	       let d = add e e' in
	       if is_cte d 
	       then 
		 (* si on a  e = 0 \/ e' = 0 avec
1		    e + e' = cte :
		    si cte = 0 : on simplifie en e'=0
		    si cte <> 0 : on ne simplifie rien
		 *)
		 if Numbers.is_zero (val_of_cte d)
		 then Ptset.union fs1 fs2
		 else add_null_in_disj ef e fs1' (Ptset.add f fs2)
	       else
		 add_null_in_disj ef e fs1' (Ptset.add f fs2)
	 | PositiveOrNull(e') ->
	     let d = sub e e' in
	     if is_cte d 
	     then 
		 (* si on a  e = 0 \/ e' >= 0 avec 
		    e - e' = cte :
		    si cte <= 0 : on simplifie en e' >= 0
		    si cte > 0 : on ne simplifie rien
		 *)
	       if Numbers.le (val_of_cte d) Numbers.zero 
	       then Ptset.union fs1 fs2
	       else add_null_in_disj ef e fs1' (Ptset.add f fs2)
	     else 
	       let d = add e e' in
	       if is_cte d 
	       then 
		 (* si on a  e = 0 \/ e' >= 0 avec 
		    e + e' = cte :
		    si cte >= 0 : on simplifie en e' >= 0
		    si cte < 0 : on ne simplifie rien
		 *)
		 if Numbers.ge (val_of_cte d) Numbers.zero
		 then Ptset.union fs1 fs2
		 else add_null_in_disj ef e fs1' (Ptset.add f fs2)
	       else
		 add_null_in_disj ef e fs1' (Ptset.add f fs2)
	 | _ -> add_null_in_disj ef e fs1' (Ptset.add f fs2)
    end
;;

	
let add_in_disj f l =
  match f.node with
    | Null(e) -> add_null_in_disj f e l Ptset.empty
    | PositiveOrNull(e) -> add_pos_in_disj f e l Ptset.empty
    | Not(g) ->
	begin
	  match g.node with
	    | PositiveOrNull(e) -> 
		let e = sub minus_one e in
		let f = positive_or_null e in
		add_pos_in_disj f e l Ptset.empty
	    | _ -> Ptset.add f l
	end
    | _ -> Ptset.add f l
;;

let disj f1 f2 = 
  try
    match (f1.node,f2.node) with
      | (True,_) -> true_formula
      | (_,True) -> true_formula
      | (False,_) -> f2
      | (_,False) -> f1
      | (Or(l1),Or(l2)) -> hash_disj(Ptset.fold add_in_disj l1 l2)
      | (Or(l1),_) -> hash_disj(add_in_disj f2 l1)
      | (_,Or(l2)) -> hash_disj(add_in_disj f1 l2)
      | (_,_) -> 
	  hash_disj(add_in_disj f1 (add_in_disj f2 Ptset.empty))
  with
      Degenerate -> true_formula

let disj_set s = Ptset.fold (fun f acc -> disj f acc) s false_formula;;

let map_disj_set f s = 
  Ptset.fold (fun x accu -> disj (f x) accu) s false_formula


(*
  [map_disj f l] return the disjunction of formulas f(x) for each x in l

  [disji f n] returns the disjunction of formulas f(i) for $0\leq i\leq n-1$. 

*)

let map_disj_list f l =
  let rec aux f l accu =
   match l with
    | [] -> accu
    | x::l -> aux f l (disj (f x) accu)
  in aux f l false_formula

let disji f n =
  let rec aux f i n accu =
    if Numbers.eq i n
    then accu
    else 
      let p = Numbers.succ i in aux f p n (disj (f i) accu)
  in aux f Numbers.zero n false_formula
;;

let for_disj f a b =
  let rec aux f i n accu =
    if Numbers.gt i n
    then accu
    else 
      let p = Numbers.succ i in aux f p n (disj (f i) accu)
  in aux f a b false_formula
;;

(*
let rec simplify f =
  match f.node with
    | True | False | Null(_) | PositiveOrNull(_) | Divisible(_,_) -> f
    | And(s,l) -> map_conj_no_subst simplify s l
    | Or(l) -> map_disj_set simplify l
    | Not(f) -> 
	begin
	  let g = simplify f in
	  match g.node with
	      (* e < 0 iff e <= -1 iff -e - 1 >= 0*)
	    | PositiveOrNull(e) -> positive_or_null(sub minus_one e)
	    | _ -> neg g
	end
    | Implies(f1,f2) -> implies (simplify f1) (simplify f2)
    | Equiv(f1,f2) -> equiv (simplify f1) (simplify f2)
    | Exists(l,f) -> exists_s l (simplify f)
    | Forall(l,f) -> forall_s l (simplify f)
;;
*)



(*

\subsection{Quantifiers}

*)


(*

[conj_in_dnf : formula -> formula set -> formula set ]

[conj_in_dnf f [f1 or .. or fk]] returns
the dnf of the conjunction of f and [f1 or .. or fk]

f is assumed to be in dnf.

*)

let add_in_dnf f d =
  match f.node with
    | True -> Ptset.singleton true_formula
    | False -> d
    | _ -> Ptset.add f d
;;

let conj_in_dnf f (d : formula_struct Ptset.t) =
  match f.node with
    | True -> d
    | False -> Ptset.empty
    | Null(_) | PositiveOrNull(_) | Divisible(_,_) | And(_) -> 
	Ptset.fold (fun g accu -> add_in_dnf (conj f g) accu) d Ptset.empty
    | Implies(_,_) | Equiv(_,_) | Forall(_,_) | Exists(_,_) | Not(_) -> 
	assert false
    | Or(l) ->
	Ptset.fold
	  (fun f accu -> 
	     Ptset.fold (fun g accu' -> add_in_dnf (conj f g) accu') 
	       d accu)
	  l Ptset.empty
;;


(*

[dnf f] returns the disjunctive normal form of [f], as a set
(disjunction) of sets (conjunctions) of literals of [Divisible], [Null] or
[PositiveOrNull] kinds.

*)

let dnf_not_null e =
  (* $[e]\neq 0$ iff $[e]>0 or [e]<0$
     iff $[e]>=1 or [e]<=-1$
     iff $[e]-1 >= 0 or -[e]-1 >=0$ *)
  disj 
    (positive_or_null (sub e one)) 
    (positive_or_null (sub minus_one e))
;;

let rec dnf f =
(*
  Format.printf "computing dnf of %a@." fprint f;
*)
  match f.node with
    | True | False | Null(_) | PositiveOrNull(_) | Divisible(_,_) -> f
    | Not(f) ->
	begin
	  match f.node with
	    | Null(e) ->
		(* $[e]\neq 0$ iff $[e]>0 or [e]<0$
                               iff $[e]>=1 or [e]<=-1$
                               iff $[e]-1 >= 0 or -[e]-1 >=0$ *)
		dnf_not_null e
	    | Divisible(e,n) -> 
		(* [n] does not divide [e] iff 
		   [n] divides $[e]+1$ or ... or [n] divides $[e]+[n]-1$
		*)
		for_disj (fun i -> divides n (add e (cte i)))
		  Numbers.one (Numbers.pred n)
	    | True | False | Not(_) -> assert false 
	    | PositiveOrNull(e) -> le e minus_one
	    | Implies(f1,f2) -> dnf (conj f1 (neg f2))
	    | Equiv(f1,f2) -> 
		dnf (disj (conj (neg f1) f2) (conj f1 (neg f2)))
	    | Forall(l,f) -> assert false (*i exists_s l (dnf (neg f)) i*)
	    | Exists(l,f) -> assert false (*i forall_s l (dnf (neg f)) i*)
	    | Or(l) -> 
		disj_set
		  (Ptset.fold (fun f accu -> conj_in_dnf (dnf (neg f)) accu) 
		     l 
		     (Ptset.singleton true_formula))
	    | And(s,l) -> 
		let e = 
		  VarMap.fold 
		    (fun x e accu -> disj (dnf_not_null (sub e (var x))) accu)
		    s 
		    false_formula
		in
		disj e (map_disj_set (fun f -> dnf (neg f)) l)
	end
    | Or(l) -> map_disj_set dnf l
    | And(s,l) -> 
	let e = 
	  VarMap.fold 
	    (fun x e accu -> conj_in_dnf (eq (var x) e) accu)
	    s 
	    (Ptset.singleton true_formula)
	in
	let e = Ptset.fold (fun f accu -> conj_in_dnf (dnf f) accu) l e in 
	disj_set e
    | Implies(f1,f2) ->	dnf (disj (neg f1) f2)
    | Equiv(f1,f2) -> dnf (disj (conj f1 f2) (conj (neg f1) (neg f2)))
    | Forall(l,f) -> assert false (*i forall_s l (dnf f) i*)
    | Exists(_,_) -> assert false (*i exists_s l (dnf f) i*)
;;


(*

  [elim_in_conj x l] where [l] is a list (conjunction) of literals (of
  kind [Positive] or [Divisible] only), eliminates the (implicitly
  existentially quantified) variable [x] from [l], producing an
  equivalent formula without [x].

  first we split [l] into four parts :
  \begin{itemize}
  \item literals $L$ where $x$ does not occur in $L$
  \item literals $kx = e$ where $k>0$ and $x$ does not occur in $e$
  \item literals $kx \geq e$ where $k>0$ and $x$ does not occur in $e$
  \item literals $kx \leq e$ where $k>0$ and $x$ does not occur in $e$
  \item literals $n \mid kx+e$ where $k>0$ and $x$ does not occur in $e$
  \end{itemize}
  while doing this split, we compute the ppcm of all coefficients $k$
*)

type split_structure =
    {
      no_x : formula ;                             (*r l without x *)
      eq_x : (Numbers.t * expr) list ;             (*r (k,e) where $kx=e$ *)
      geq_x : (Numbers.t * expr) list ;            (*r (k,e) where $kx\geq e$ *) 
      leq_x : (Numbers.t * expr) list ;            (*r (k,e) where $kx\leq e$ *) 
      div_x : (Numbers.t * Numbers.t * expr) list ;(*r (n,k,e) where $n \mid kx+e$ *)
      ppcm : Numbers.t ;
    }
;;

let empty_split_structure = 
  {
    no_x = true_formula ;
    eq_x = [];
    geq_x = [];
    leq_x = [];
    div_x = [] ;
    ppcm = Numbers.one ;
  }
;;

let split x l =
    Ptset.fold
      (fun lit accu ->
	 match lit.node with
	   | Null(e) -> 
	       begin
		 try
		   let k = get_coef e x in
		   let e_no_x = remove_coef e x in
		   if Numbers.gt k Numbers.zero 
		   then 
		     { accu with 
			 eq_x = (k,minus e_no_x)::accu.eq_x ;
			 ppcm = Numbers.ppcm k accu.ppcm }
		   else 
		     let mk = Numbers.minus k in
		     { accu with 
			 eq_x = (mk,e_no_x)::accu.eq_x ;
			 ppcm = Numbers.ppcm mk accu.ppcm }
		 with
		     Not_found ->
		        { accu with no_x = conj lit accu.no_x }
	       end
	   | PositiveOrNull(e) -> 
	       begin
		 try
		   let k = get_coef e x in
		   let e_no_x = remove_coef e x in
		   if Numbers.gt k Numbers.zero 
		   then 
		     { accu with 
			 geq_x = (k,minus e_no_x)::accu.geq_x ;
			 ppcm = Numbers.ppcm k accu.ppcm }
		   else 
		     let mk = Numbers.minus k in
		     { accu with 
			 leq_x = (mk,e_no_x)::accu.leq_x ;
			 ppcm = Numbers.ppcm mk accu.ppcm }
		 with
		     Not_found ->
		        { accu with no_x = conj lit accu.no_x }
	       end
	   | Divisible(e,n) ->
	       begin
		 try
		   let k = get_coef e x in
		   let e_no_x = remove_coef e x in
		   if Numbers.gt k Numbers.zero 
		   then 
		     { accu with 
			 div_x = (n,k,e_no_x)::accu.div_x ;
			 ppcm = Numbers.ppcm k accu.ppcm }
		   else 
		     let mk = Numbers.minus k in
		     { accu with 
			 div_x = (n,mk,minus e_no_x)::accu.div_x ;
			 ppcm = Numbers.ppcm mk accu.ppcm }
		 with
		     Not_found ->
		        { accu with no_x = conj lit accu.no_x }
	       end
	   | _ -> Linear_constraints.print lit ; assert false)
      l
      empty_split_structure
;;



let multiply_ppcm dec =
  let x_equals = (*r list of formulas x = e *)
    List.rev_map (fun (k,e) -> (times (Numbers.div dec.ppcm k) e)) dec.eq_x
  and x_lower_bounds = (*r list of formulas x >= e *)
    List.rev_map (fun (k,e) -> (times (Numbers.div dec.ppcm k) e)) dec.geq_x
  and x_upper_bounds = (*r list of formulas x <= e *)
    List.rev_map (fun (k,e) -> (times (Numbers.div dec.ppcm k) e)) dec.leq_x
  and x_divs = (*r list of formulas m | x + e *)
    (dec.ppcm,zero)::
    List.rev_map 
      (fun (n,k,e) -> 
	 let p = Numbers.div dec.ppcm k in (Numbers.mult n p,times p e))
      dec.div_x
  in
  let ppcm_div = 
    List.fold_left (fun accu (k,_) -> Numbers.ppcm accu k) Numbers.one x_divs
  in
  x_equals,x_lower_bounds,x_upper_bounds,x_divs,ppcm_div,dec.no_x
  ;;




let elim_in_conj x l =
(*
  Format.printf "eliminating var %s in " (var_name x);
  let _ = 
    Ptset.fold 
      (fun f accu -> Format.printf accu fprint f;" and@ %a") l "%a"
  in
  Format.printf "@.";
*)
  let (x_equals,x_lower_bounds,x_upper_bounds,x_divs,ppcm_div,no_x) =
    multiply_ppcm (split x l)
  in
  match x_equals with
  | h::t ->
      (*
	the resulting formula is
	$$ % $
        \bigwedge_{e\in [t]}   e = [h]
	\wedge
        \bigwedge_{e\in [x_lower_bounds]}   e \leq [h]
	\wedge
        \bigwedge_{e\in [x_upper_bounds]} e \geq [h]
        \wedge
        \bigwedge_{(m,e)\in [x_divs]} m | e+[h]
	$$ % $
      *)
      conj_list 
	[ no_x ;
	  map_conj_list (fun e -> eq e h) t ;
	  map_conj_list (fun e -> le e h) x_lower_bounds ;
	  map_conj_list (fun e -> ge e h) x_upper_bounds ;
	  map_conj_list (fun (m,e) -> divides m (add e h)) x_divs ;
	]
  | [] ->
      if x_lower_bounds = [] 
      then
	(*
	  the resulting formula is
	  $$ % $
	  \bigvee_{1 \leq q \leq [ppcm_div]}
	  \left(
          \bigwedge_{(m,e)\in [x_divs]} m | e+q
	  \right)
	  $$ % $	  
	*)
	conj 
	  no_x
	  (disji
	     (fun q -> 
		(map_conj_list
		   (fun (m',e') -> divides m' (add_cte e' q))
		   x_divs))
	     ppcm_div)
      else
	(*
	  the resulting formula is
	  $$ % $
	  \bigvee_{e\in [x_lower_bounds]}
	  \left(
          \bigwedge_{e'\in [x_lower_bounds]}   e' \leq e
	  \wedge
          \bigvee_{0 \leq q \leq [ppcm_div]-1}
          \left(
          \bigwedge_{e'\in [x_upper_bounds]} e+q \leq e'
          \wedge
          \bigwedge_{(m',e')\in [x_divs]} m' | e'+e+q
          \right)
	  \right)
	  $$ % $
	  
	*)
	conj no_x
	  (map_disj_list
	     (fun e -> 
		conj
		  (map_conj_list (fun e' -> le e' e) x_lower_bounds)
		  (disji
		     (fun q -> 
			conj
			  (map_conj_list
			     (fun e' -> le (add_cte e q) e')
			     x_upper_bounds)
			  (map_conj_list
			     (fun (m',e') -> 
				divides m' (add_cte (add e e') q))
			     x_divs))
		     ppcm_div))
	     x_lower_bounds)    
	
(*

  [exists_elim x f] eliminates var [x] form [f]. Assumes [f] quantifier-free

*)

let rec exists_elim_dnf x f = 
  match f.node with
    | Or(l) ->
	Ptset.fold
	  (fun f acc -> disj (exists_elim_dnf x f) acc) 
	  l false_formula
    | And(s,l) -> 
	elim_in_conj x 
	  (VarMap.fold
	     (fun x e acc -> Ptset.add (eq (var x) e) acc) s l)
    | True -> true_formula
    | False -> false_formula
    | Divisible(_,_) | Null(_) | PositiveOrNull(_) ->
	elim_in_conj x (Ptset.singleton f)
    | _ -> assert false
;;

let exists_elim x f = exists_elim_dnf x (dnf f);;


(*

new version of exists_elim, with fewer dnf computation

*)

let exists_elim_not_null x e =
  disj
    (exists_elim x (positive_or_null (sub e one))) 
    (exists_elim x (positive_or_null (sub minus_one e)))

let rec exists_elim_in_conj x s =
  let (no_x,atom_x,with_x,has_non_atom_with_x) =
    Ptset.fold
      (fun f (acc1,acc2,acc3,b) ->
	 if var_occurs x f then
	   if is_atom f then
	     (acc1,Ptset.add f acc2,conj f acc3,b)
	   else
	     (acc1,acc2,conj f acc3,true)
	 else
	   (conj f acc1,acc2,acc3,b))
      s (true_formula,Ptset.empty,true_formula,false)
  in
  if has_non_atom_with_x then
    conj no_x (exists_elim x (dnf with_x))
  else
    conj no_x (elim_in_conj x atom_x)
    

and exists_elim x f = 
  match f.node with
    | Or(l) ->
	Ptset.fold
	  (fun f acc -> disj (exists_elim x f) acc) 
	  l false_formula
    | And(s,l) -> 
	exists_elim_in_conj x 
	  (VarMap.fold
	     (fun y e acc -> Ptset.add (eq (var y) e) acc) s l)		
    | True -> true_formula
    | False -> false_formula
    | Divisible(_,_) | Null(_) | PositiveOrNull(_) ->
	elim_in_conj x (Ptset.singleton f)
    | Not(g) ->
	begin
	  match g.node with
	    | Null(e) ->
		(* $[e]\neq 0$ iff $[e]>0 or [e]<0$
                               iff $[e]>=1 or [e]<=-1$
                               iff $[e]-1 >= 0 or -[e]-1 >=0$ *)
		exists_elim_not_null x e
	    | Divisible(e,n) -> 
		(* [n] does not divide [e] iff 
		   [n] divides $[e]+1$ or ... or [n] divides $[e]+[n]-1$
		*)
		for_disj 
		  (fun i -> (exists_elim x (divides n (add e (cte i)))))
		  Numbers.one (Numbers.pred n)
	    | True | False | Not(_) -> assert false 
	    | PositiveOrNull(e) -> 
		exists_elim x (le e minus_one)
	    | Implies(f1,f2) -> 
		exists_elim x (conj f1 (neg f2))
	    | Equiv(f1,f2) -> 
		disj 
		  (exists_elim x (conj (neg f1) f2))
		  (exists_elim x (conj f1 (neg f2)))
	    | Forall(l,f) -> assert false (*i exists_s l (dnf (neg f)) i*)
	    | Exists(l,f) -> assert false (*i forall_s l (dnf (neg f)) i*)
	    | Or(l) -> 
		let neg_l =
		  Ptset.fold (fun f acc -> Ptset.add (neg f) acc) l Ptset.empty
		in
		exists_elim_in_conj x neg_l
	    | And(s,l) ->
		let e = 
		  VarMap.fold 
		    (fun y e accu -> 
		       disj (exists_elim_not_null x (sub e (var y))) accu)
		    s 
		    false_formula
		in
		disj e (map_disj_set (fun f -> exists_elim x (neg f)) l)
	end
    | Implies(f1,f2) ->
	disj (exists_elim x (neg f1)) (exists_elim x f2)
    | Equiv(f1,f2) ->
	disj 
	  (exists_elim x (conj f1 f2)) 
	  (exists_elim x (conj (neg f1) (neg f2)))
    | _ -> assert false
;;

(*

  forall elimination

*)

let forall_elim x f = neg (exists_elim x (neg f));;


let rec eliminate_quantifiers f =
  match f.node with
    | True | False | Divisible(_,_) | Null(_) | PositiveOrNull(_) -> f
    | Not(g) -> neg(eliminate_quantifiers g)
    | And(s,l) -> 
	map_conj_no_subst eliminate_quantifiers s l
    | Or(l) -> map_disj_set eliminate_quantifiers l
    | Implies(f1,f2) ->
	implies (eliminate_quantifiers f1) (eliminate_quantifiers f2) 
    | Equiv(f1,f2) ->
	equiv (eliminate_quantifiers f1) (eliminate_quantifiers f2)
    | Exists(l,f) ->
	let g = eliminate_quantifiers f in
	List.fold_left (fun acc x -> exists_elim x acc) g l
    | Forall(l,f) ->
	let g = neg(eliminate_quantifiers f) in
	neg(List.fold_left (fun acc x -> exists_elim x acc) g l)


(*

 \subsection{Checking}

*)

let unsafe_is_satisfiable f =
  
  (*i
  Format.printf "*** Presburger satisfiability of ";
    print f;
    Format.printf "@."; 
    i*)
  
  let l = free_vars f in

   (*i  
     Format.printf "*** With %d variable to quantify.@." (List.length l); 
    i*)
  let f = exists_s l f in
  let f = eliminate_quantifiers f in
  match f.node with
    | True -> 
	(*i
	Format.printf "*** yes@."; 
	i*)true
    | False -> 
	(*i
	Format.printf "*** no@."; 
	i*)false
    | _ -> assert false


let unsafe_is_valid f =   
  not(unsafe_is_satisfiable (neg f));;

let is_satisfiable f = 
  unsafe_is_satisfiable 
    (Linear_constraints.remove_denominators f);;

let is_valid f = 
  unsafe_is_valid 
    (Linear_constraints.remove_denominators f);;





let has_finitely_many_solutions f = 
  let bound = (make_var "bound") 
  and f = remove_denominators f
  in
  let l = free_vars f in
  let f' = exists bound 
	     (List.fold_right 
		(fun x acc -> conj 
		     (conj 
			(le (var x) (var bound)) 
			(le (var x) (minus (var bound)))) acc)
		l f)
  in unsafe_is_valid f'

exception Infinite;;
exception No_solution;;

type one_var_split_structure =
    { 
      equals : Numbers.t option;
      lower_bound : Numbers.t option;
      upper_bound : Numbers.t option;
      divx : (Numbers.t * Numbers.t * Numbers.t) list;
      ppcm : Numbers.t ;
    }

let empty_one_var_split_structure =
  {
    equals = None;
    lower_bound = None;
    upper_bound = None;
    divx = [];
    ppcm = Numbers.one;
  }

module NumSet = 
  Ordered_sets.Make(struct type t = Numbers.t let compare = Numbers.compare end)

let split_one_var x l =
  Ptset.fold
    (fun lit accu ->
       match lit.node with
	 | Null(e) -> 
	     begin
	       try
		 let x_coef = get_coef e x
		 and cte = val_of_cte e
		 in
		 if Numbers.is_zero (Numbers.modulo cte x_coef)
		 then 
		   let new_val = 
		     Numbers.div (Numbers.minus cte) x_coef
		   in
		   match accu.equals with
		     | None ->
			 { accu with equals = Some new_val }
		     | Some(b) ->
			 if Numbers.eq new_val b then accu
			 else raise No_solution
		 else 
		   raise No_solution
	       with
		   Not_found -> assert false
	     end
	 | PositiveOrNull(e) -> 
	     begin
	       try
		 let x_coef = get_coef e x
		 and cte = val_of_cte e
		 in
		 if Numbers.gt x_coef Numbers.zero 
		 then 
		   let bound = 
		     Numbers.div_ceil (Numbers.minus cte) x_coef
		   in
		   match accu.lower_bound with
		     | None ->
			 { accu with lower_bound = Some bound }
		     | Some(b) ->
			 { accu with lower_bound = Some (Numbers.max b bound) }
		 else 
		   let bound = 
		     Numbers.div_floor (Numbers.minus cte) x_coef
		   in
		   match accu.upper_bound with
		     | None ->
			 { accu with upper_bound = Some bound }
		     | Some(b) ->
			 { accu with upper_bound = Some (Numbers.min b bound) }
	       with
		   Not_found -> assert false
	     end
	 | Divisible(e,n) ->
	     begin
	       try
		 let x_coef = get_coef e x
		 and cte = val_of_cte e
		 in
		 { accu with 
		     divx = (n,x_coef,cte)::accu.divx ;
		     ppcm = Numbers.ppcm n accu.ppcm ;
	       }
	       with
		   Not_found -> assert false
	     end
	 | _ -> assert false)
    l
    empty_one_var_split_structure
;;

let is_a_solution v divs =
  List.for_all 
	(fun (n,x_coef,cte) -> 
	   Numbers.is_zero 
	     (Numbers.modulo (Numbers.add (Numbers.mult x_coef v) cte) n))
	divs
;;

let rec find_sols a b divs accu =
  if Numbers.gt a b 
  then accu
  else 
    if is_a_solution a divs
    then 
      find_sols (Numbers.succ a) b divs (NumSet.add a accu)
    else 
      find_sols (Numbers.succ a) b divs accu
;;

let rec try_find_sols b divs =
  if Numbers.le b Numbers.zero 
  then NumSet.empty
  else 
    if 
      List.for_all 
	(fun (n,x_coef,cte) -> 
	   Numbers.is_zero 
	     (Numbers.modulo (Numbers.add (Numbers.mult x_coef b) cte) n))
	divs
    then raise Infinite
    else try_find_sols (Numbers.pred b) divs
;;





let solve_one_var_conjunction x f =
  let l = 
    match f.node with
    | And(s,fl) -> 
	VarMap.fold
	  (fun x e acc -> Ptset.add (eq (var x) e) acc) s fl
    | _ -> Ptset.singleton f
  in
  let s = split_one_var x l in
  match s.equals with
    | Some v ->
	begin
	  match s.lower_bound with
	    | None -> ()
	    | Some lb -> if Numbers.gt lb v then raise No_solution
	end;
	begin
	  match s.upper_bound with
	    | None -> ()
	    | Some ub -> if Numbers.lt ub v then raise No_solution
	end;
	if is_a_solution v s.divx
	then NumSet.singleton v
	else raise No_solution
    | None ->
	match s.lower_bound,s.upper_bound with
	  | (Some lb,Some ub) ->
	      find_sols lb ub s.divx NumSet.empty
	  | _ ->
	      try_find_sols s.ppcm s.divx  
;;



let solve_one_var_formula x f = 
  let dnff = dnf f 
  in
  match dnff.node with
    | Or(s) ->
	Ptset.fold
	  (fun f accu ->
	     let s = solve_one_var_conjunction x f in
	     NumSet.union s accu)
	  s
	  NumSet.empty
    | _ -> solve_one_var_conjunction x dnff
;;


let rec solve f vars =
  match vars with
    | [] ->
	begin
	  match f.node with
	    | True -> [[]]
	    | False -> raise No_solution
	    | _ -> assert false
	end
    | x::others ->
	let f' = eliminate_quantifiers (exists_s others f) in
	let s = solve_one_var_formula x f' in
	NumSet.fold
	  (fun n accu ->
	     let f' = inst1 x n f in
	     let sols = solve f' others in
	     List.fold_right
	       (fun l accu -> ((x,n)::l)::accu)
	       sols
	       accu)
	  s
	  []
;;




let get_all_solutions f = 
  let f = eliminate_quantifiers (remove_denominators f) in
  try
    solve f (free_vars f) 
  with
      No_solution -> []
 


