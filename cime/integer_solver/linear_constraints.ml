(*

\subsection{Abstract type for variables}

variables are abstract, may only be built with [make_var]. 

*)

type var_id = 
    {
      var_tag : int;
      var_name : string;
    }
;;

let make_var,make_var_uniq_name =
  let count = ref 0 in
  (function name ->
    incr count;
    { var_tag = !count ; var_name = name }),
  (function name ->
    incr count;
    { var_tag = !count ; var_name = name ^ "_" ^ (string_of_int !count) })
;;

let var_name v = 
  v.var_name (*i ^ "@" ^ (string_of_int v.var_tag) i*);;

(*

\subsection{Abstract type for expressions}

  [zero] is $0$, [one] is $1$, [(cte n)] is the constant $n$, [(var
  v)] is the variable [v], [(add e1 e2)] is $e_1+e_2$, [(sub e1 e2)]
  is $e_1-e_2$, [(minus e)] is $-e$, [(times n e)] is $ne$.

*)


module VarSet = Inttagset.Make (struct type t = var_id let tag x = x.var_tag end);;

module VarMap = Inttagmap.Make (struct type t = var_id let tag x = x.var_tag end);;


type expr = { const : Numbers.t ; vars : (unit,Numbers.t) VarMap.t };;


let hash_combine acc n = acc * 65599 + n;;

let hash_expr e =
  VarMap.fold
    (fun x k acc ->
       hash_combine (hash_combine acc x.var_tag) (Numbers.hash k))
    e.vars
    (Numbers.hash e.const)
;;


let zero = { const = Numbers.zero ; vars = VarMap.empty };;

let one = { const = Numbers.one ; vars = VarMap.empty };;

let minus_one = { const = Numbers.minus_one ; vars = VarMap.empty };;

let cte n = { const = n ; vars = VarMap.empty };;

let var v = 
  { const = Numbers.zero ; vars = VarMap.add v Numbers.one (VarMap.empty) };; 


let get_coef e x = VarMap.find x e.vars
let remove_coef e x = { e with vars = VarMap.remove x e.vars}

let add_cte e n = { e with const = Numbers.add e.const n }

let add e1 e2 = 
  { const = Numbers.add e1.const e2.const ;
    vars =
      VarMap.fold
	(fun v k2 accu ->
	   try 
	     let k = Numbers.add (VarMap.find v accu) k2 in
	     if Numbers.is_zero k
	     then VarMap.remove v accu 
	     else VarMap.add v k accu 
	   with
	       Not_found ->
		 VarMap.add v k2 accu)
	e2.vars 
	e1.vars ;
  }
;;


let sub e1 e2 = 
  { const = Numbers.sub e1.const e2.const ;
    vars =
      VarMap.fold
	(fun v k2 accu ->
	   try 
	     let k = Numbers.sub (VarMap.find v accu) k2 in
	     if Numbers.is_zero k
	     then VarMap.remove v accu 
	     else VarMap.add v k accu 
	   with
	       Not_found ->
		 VarMap.add v (Numbers.minus k2) accu)
	e2.vars
	e1.vars ;
  }
;;

let minus e = 
  { const = Numbers.minus e.const;
    vars = VarMap.map (fun k -> Numbers.minus k) e.vars 
  }
;;

let times n e = 
  if Numbers.is_zero n
  then zero
  else 
    { 
      const = Numbers.mult n e.const;
      vars = VarMap.map (fun k -> Numbers.mult n k) e.vars 
    }
;;

let div e n = 
  if Numbers.is_zero n
  then raise Division_by_zero
  else 
    if Numbers.eq n Numbers.one
    then e
    else
      { 
	const = Numbers.div e.const n;
	vars = VarMap.map (fun k -> Numbers.div k n) e.vars 
      }
;;

let is_cte e = VarMap.is_empty e.vars

let val_of_cte e = e.const

let common_denominator e =
  VarMap.fold
    (fun x k acc ->
       Numbers.ppcm (Numbers.denominator k) acc)
    e.vars (Numbers.denominator e.const)
;;
       

let expr_eq e1 e2 =
  let d = sub e1 e2 in
  if is_cte d then Numbers.is_zero (val_of_cte d) else false
  

(*

  substitutions

*)

type substitution = (unit,expr) VarMap.t;;

let subst1_expr v e' e =
  try
    let v_coef = VarMap.find v e.vars in
    let rest = { e with vars = VarMap.remove v e.vars } in
    add (times v_coef e') rest
  with
      Not_found -> e
  

let subst_expr sigma e =
  VarMap.fold
    (fun x k acc ->
       try
	 let e = VarMap.find x sigma in
	 add (times k e) acc
       with
	   Not_found -> add (times k (var x)) acc)
    e.vars
    (cte e.const)
;;


let subst_eq = VarMap.equal expr_eq 
  

(*

\subsection{Abstract type for formulas}

Invariants :

\begin{itemize}

\item [Positive(e)], [NonPositive(e)] : $e$ is a non-constant
expression.

\item [Divisible(e,n)], [NonDivisible(e,n)] : $e$ is a non-constant
expression, $n$ is greater than 1.

\item [And(s,l)] : formulas in [l] are neither [True], [False], nor
[And(..)] ; [s]+[l] has length at least 2.

\item [Or(l)] : formulas in [l] are neither [True], [False], nor
[Or(..)] ; [l] has length at least 2.

\end{itemize}

*)

open Hcons;;


type formula = formula_struct hash_consed

and formula_struct = 
  | True 
  | False
  | Null of expr            
  | PositiveOrNull of expr            
  | Divisible of expr * Numbers.t
  | And of substitution * formula_struct Ptset.t
  | Or of formula_struct Ptset.t
  | Not of  formula
  | Implies of formula * formula
  | Equiv of formula * formula
  | Exists of var_id list * formula
  | Forall of var_id list * formula
;;



let formula_eq (f1,f2) =
  match (f1,f2) with
    | True, True -> true
    | False, False -> true
    | Null(e1), Null(e2) -> expr_eq e1 e2
    | PositiveOrNull(e1), PositiveOrNull(e2) -> expr_eq e1 e2
    | Divisible(e1,n1), Divisible(e2,n2) -> Numbers.eq n1 n2 && expr_eq e1 e2
    | And(s1,e1), And(s2,e2) -> 
	subst_eq s1 s2 && Ptset.equalq e1 e2
    | Or(e1), Or(e2) -> Ptset.equalq e1 e2
    | Not(f1), Not(f2) -> f1==f2
    | Implies(f11,f12), Implies(f21,f22) -> f11==f21 && f12==f22
    | Equiv(f11,f12), Equiv(f21,f22) -> f11==f21 && f12==f22
    | Exists(l1,f1), Exists(l2,f2) -> l1=l2 && f1==f2
    | Forall(l1,f1), Forall(l2,f2) -> l1=l2 && f1==f2
    | _,_ -> false
;;

let hTrue = 1;;
let hFalse = 2;;
let hNull = 3;;
let hPositiveOrNull = 4;;
let hDivisible = 5;;
let hAnd = 6;;
let hOr = 7;;
let hNot = 8;;
let hImplies = 9;;
let hEquiv = 10;;
let hExists = 11;;
let hForall = 12;;

let hash_combine2 = hash_combine (* (lxor) *)

let hash_formula f =
  match f with
    | True -> hTrue
    | False -> hFalse
    | Null(e) ->  hash_combine2 hNull  (hash_expr e)        
    | PositiveOrNull(e) ->  hash_combine2 hPositiveOrNull (hash_expr e) 
    | Divisible(e,n) ->
	hash_combine2 (hash_combine2 hDivisible (hash_expr e)) (Numbers.hash n)
    | And(sigma,l) ->
	let h = 
	  VarMap.fold
	    (fun x e acc ->
	       hash_combine2 (hash_combine2 acc x.var_tag) (hash_expr e)
	    )
	    sigma
	    hAnd
	in
	Ptset.fold
	  (fun f acc -> hash_combine2 acc f.hkey)
	  l
	  h  
    | Or(l) -> 
	Ptset.fold
	  (fun f acc -> hash_combine2 acc f.hkey)
	  l
	  hOr  
    | Not(f) -> 
	hash_combine2 f.hkey hNot
    | Implies(f1,f2) ->
	hash_combine2 (hash_combine2 hImplies f1.hkey) f2.hkey
    | Equiv(f1,f2) ->
	hash_combine2 (hash_combine2 hEquiv f1.hkey) f2.hkey
    | Exists(l,f) ->
	hash_combine2
	  (List.fold_left
	     (fun acc x ->
		hash_combine2 acc x.var_tag)	     
	     hExists l)
	  f.hkey
    | Forall(l,f) ->
	hash_combine2
	  (List.fold_left
	     (fun acc x ->
		hash_combine2 acc x.var_tag)
	     hForall l)
	  f.hkey
	

(*


\subsection{Printing}


*)

open Format;;


let fprint_expr fmt e =
  let b = 
    VarMap.fold 
      (fun v k b ->
	 if b
	 then
	   if Numbers.eq k Numbers.one 
	   then fprintf fmt " + %s" (var_name v)
	   else 
	     if Numbers.eq k Numbers.minus_one 
	     then fprintf fmt " - %s" (var_name v)
	     else 
	       if Numbers.ge k Numbers.zero 
	       then fprintf fmt " + %s.%s" (Numbers.to_string k) (var_name v)
	       else 
		 fprintf fmt " - %s.%s" 
		   (Numbers.to_string (Numbers.minus k)) (var_name v)
	 else
	   if Numbers.eq k Numbers.one 
	   then fprintf fmt "%s" (var_name v)
	   else 
	     if Numbers.eq k Numbers.minus_one 
	     then fprintf fmt "-%s" (var_name v)
	     else 
	       fprintf fmt "%s.%s" (Numbers.to_string k) (var_name v);
	 true)
      e.vars false
  in
  if b 
  then
    if Numbers.gt e.const Numbers.zero 
    then fprintf fmt " + %s" (Numbers.to_string e.const)
    else
      if Numbers.lt e.const Numbers.zero 
      then 
	fprintf fmt " - %s" 
	  (Numbers.to_string (Numbers.minus e.const))
      else ()
  else
    fprintf fmt "%s" (Numbers.to_string e.const)
;;

let print_expr = fprint_expr std_formatter;;

let rec fprint fmt f = 
  match f.node with
  | True -> fprintf fmt "true"
  | False -> fprintf fmt "false"
  | Null(e) -> fprintf fmt "@[%a = 0@]" fprint_expr e
  | PositiveOrNull(e) -> fprintf fmt "@[%a >= 0@]" fprint_expr e
  | Divisible(e,n) ->
      fprintf fmt "@[ %s |@ %a @]" (Numbers.to_string n) fprint_expr e
  | And(s,l) ->
      fprintf fmt "@[(";
      let accu = 
	VarMap.fold 
	  (fun x e accu -> 
	     if accu then fprintf fmt " and@ ";
	     fprintf fmt "%s = %a" (var_name x) fprint_expr e;true) s false
      in
      let _ = 
	Ptset.fold 
	  (fun f accu -> 
	     if accu then fprintf fmt " and@ ";
	     fprintf fmt "%a" fprint f;true) l accu
      in
      fprintf fmt ")@]"
  | Or(l) ->
      fprintf fmt "@[(";
      let _ = 
	Ptset.fold 
	  (fun f accu -> fprintf fmt accu fprint f;" or@ %a") l "%a"
      in
      fprintf fmt ")@]"
  | Not(f) -> fprintf fmt "@[(not@ %a)@]" fprint f
  | Implies(f1,f2) -> 
      fprintf fmt "@[(%a implies@ %a)@]" fprint f1 fprint f2
  | Equiv(f1,f2) -> 
      fprintf fmt "@[(%a equiv@ %a)@]" fprint f1 fprint f2
  | Exists(x::l,f) ->
      fprintf fmt "@[(exists@ %s" (var_name x);
      List.iter (fun x -> fprintf fmt " %s" (var_name x)) l;
      fprintf fmt ",@ %a)@]" fprint f
  | Forall(x::l,f) ->
      fprintf fmt "@[(forall@ %s" (var_name x);
      List.iter (fun x -> fprintf fmt " %s" (var_name x)) l;
      fprintf fmt ",@ %a)@]" fprint f
  | Exists([],_) | Forall([],_) -> assert false

let print = fprint std_formatter


(*

 hash consing

*)

module Hash = Hcons.Make(struct type t = formula_struct
				   let equal = formula_eq
				   let hash f = 
				     let n = hash_formula f in
				     n land Pervasives.max_int
			    end)

let hash_consing_table = Hash.create 1997;;

let hash_cons f = 
  let g = Hash.hashcons hash_consing_table f in
(*
  Format.printf "%a@." fprint g;
*)
  g


(*

[(eq e1 e2)] is $e_1=e_2$, 
[(ne e1 e2)] is $e_1\neq e_2$, 
[(ge e1 e2)] is $e_1\geq e_2$, 
[(gt e1 e2)] is $e_1>e_2$, 
[(le e1 e2)] is $e_1\leq e_2$, 
[(lt e1 e2)] is $e_1<e_2$. 
[(divides n e)] is $n$ divides $e$.

*)

(*

  \subsection{constructors of atomic formulas}

*)

let true_formula = hash_cons True;;

let false_formula = hash_cons False;;

let null e =
  if e.vars = VarMap.empty then 
    if Numbers.is_zero e.const then true_formula else false_formula
  else hash_cons (Null(e))
;;

let positive_or_null e =
  if e.vars = VarMap.empty then 
    if Numbers.ge e.const Numbers.zero then true_formula else false_formula
  else hash_cons (PositiveOrNull(e))
;;

let divides n e = 
  if Numbers.is_zero n 
  then failwith "div by zero"
  else
    let n = Numbers.abs n in
    if Numbers.eq n Numbers.one 
    then true_formula 
    else 
      let vars_mod = VarMap.fold
		(fun v k accu ->
		   let k'= Numbers.modulo k n in
		   if Numbers.is_zero k'
		   then accu
		   else VarMap.add v k' accu)
		e.vars
		VarMap.empty
      in
      if vars_mod = VarMap.empty
      then 
	if Numbers.is_zero (Numbers.modulo e.const n)
	then true_formula 
	else false_formula
      else
	hash_cons(Divisible({const = e.const; vars = vars_mod},n))
;;


let is_atom f = 
  match f.node with
    | True | False | Null(_) | PositiveOrNull(_) | Divisible(_,_) -> true
    | And(_,_) | Or(_) | Implies(_,_) | Equiv(_,_) | Not(_) 
    | Exists(_,_) | Forall(_,_) -> false

(*

  \subsection{negation, and derived constructors for atomic formulas}

*)

let neg f = 
  match f.node with
    | True -> false_formula
    | False -> true_formula
    | Not(g) -> g
    | _ -> hash_cons(Not(f))

let negative e = neg(positive_or_null e);;

let negative_or_null e = positive_or_null (minus e);;

let positive e = neg(negative_or_null e);;

let ge e1 e2 = positive_or_null (sub e1 e2) ;;

let gt e1 e2 = positive (sub e1 e2);;

let le e1 e2 = positive_or_null (sub e2 e1);;

let lt e1 e2 = positive (sub e2 e1);;

let eq e1 e2 = null (sub e1 e2);;

let ne e1 e2 = neg(eq e1 e2)

(* 

   \subsection{Others connectives, except disjunction and conjunction}

*)


(*

  remaining connectives

*)


let implies f1 f2 = 
  if f1==f2 then true_formula else
    match f1.node with
      | True -> f2
      | False -> true_formula
      | _ ->
	  match f2.node with
	    | True -> true_formula
	    | False -> neg f1
	    | _ -> hash_cons(Implies(f1,f2));;

let equiv f1 f2 = 
  if f1==f2 then true_formula else
    match f1.node with
      | True -> f2
      | False -> neg f2
      | _ ->
	  match f2.node with
	    | True -> f1
	    | False -> neg f1
	    | _ -> hash_cons(Equiv(f1,f2));;

let exists v f =
  match f.node with
    | True | False -> f
    | Exists(l,f') -> hash_cons(Exists(v::l,f'))
    | _ -> hash_cons(Exists([v],f))
;;

let forall v f =
  match f.node with
    | True | False -> f
    | Forall(l,f') -> hash_cons(Forall(v::l,f'))
    | _ -> hash_cons(Forall([v],f))
;;

let exists_s l f =
  if l=[] then f else
  match f.node with
    | True | False -> f
    | Exists(l',f') -> hash_cons(Exists(List.append l l',f'))
    | _ -> hash_cons(Exists(l,f))
;;

let forall_s l f =
  if l=[] then f else
  match f.node with
    | True | False -> f
    | Forall(l',f') -> hash_cons(Forall(List.append l l',f'))
    | _ -> hash_cons(Forall(l,f))
;;


(*

  \subsection{Disjunction}

*)

let hash_disj l = 
  Ptset.case1
    (fun () -> false_formula)
    (fun f -> f)
    (fun () -> hash_cons(Or(l)))
    l
;;

let disj f1 f2 = 
  match (f1.node,f2.node) with
    | (True,_) -> true_formula
    | (_,True) -> true_formula
    | (False,_) -> f2
    | (_,False) -> f1
    | (Or(l1),Or(l2)) -> hash_disj(Ptset.union l1 l2)
    | (Or(l1),_) -> hash_disj(Ptset.add f2 l1)
    | (_,Or(l2)) -> hash_disj(Ptset.add f1 l2)
    | (_,_) -> hash_disj(Ptset.add f1 (Ptset.singleton f2))
	  


let rec disj_list l = 
  match l with
    | [] -> false_formula
    | [f] -> f
    | f::l -> disj f (disj_list l)
;;


let map_disj_set f s = 
  Ptset.fold (fun x accu -> disj (f x) accu) s false_formula

let map_disj2 f fold accu l =
  fold 
    (fun absform (env,linform) -> 
       let (env',linform') = f env absform in env',disj linform linform') 
    l 
    (accu,false_formula)
;;


(*

  \subsection{Conjunction and substitution}

  Are mutually recursive !

*)


let hash_conj s l = 
  (*
    if s empty and l empty : [true_formula] 
    if s empty and l singleton : [elt(l)]
    if s singleton and l empty : [elt(s)] 
    else : [And(s,l)]
  *)
  if VarMap.is_empty s
  then
    if Ptset.is_empty l 
    then true_formula
    else 
      try Ptset.elt l with Not_found -> hash_cons(And(s,l))
  else
    if Ptset.is_empty l 
    then 
      try 
	let (x,e) = VarMap.elt s in eq (var x) e
      with
	  Not_found -> hash_cons(And(s,l))
    else
      hash_cons(And(s,l))

exception Degenerate;;

let leading_var e = let x,_ = VarMap.max_tag e.vars in x;;

let expr_to_subst e =
  VarMap.case2
    (fun () -> raise Not_found)
    (fun x k -> 
       if Numbers.eq k Numbers.one then (x,cte(Numbers.minus e.const))
       else
	 if Numbers.eq k Numbers.minus_one then (x,cte e.const)
	 else
	   raise Not_found)
    (fun x kx y ky ->
       if x.var_tag > y.var_tag
       then
	 if Numbers.eq kx Numbers.one 
	 then (x,sub (var x) e)
	 else
	   if Numbers.eq kx Numbers.minus_one 
	   then (x,add (var x) e)
	   else raise Not_found
       else
	 if Numbers.eq ky Numbers.one 
	 then (y,sub (var y) e)
	 else
	   if Numbers.eq ky Numbers.minus_one 
	   then (y,add (var y) e)
	   else raise Not_found)
    (fun () -> raise Not_found)
    e.vars
;;

(*

  [subst_in_subst : substitution -> var_id -> expr -> substitution *
    formula Ptset.t]

  [subst_in_subst sigma x e] applies [{x->e}] to [sigma], returns
  [(sigma',S)], 
  [S] is the set of additional constraints, if [x] already
  occurs in [sigma].

  raises [Degenerate] if [sigma] already contains a [{x -> e'}] where [e-e' =
  cte <> 0].

  examples (if [x] is greater than [y])

  [subst_in_subst {x->1} y 2] returns [{x->1},{}]

  [subst_in_subst {x->y+1} y 2] returns [{x->3},{}]

  [subst_in_subst {x->1} x 1] returns [{},{}]

  [subst_in_subst {x->1} x 2] raises [Degenerate]

  [subst_in_subst {x->y+1} x 2] returns [{},{y+1=2}]

  [subst_in_subst {x->2} x y+1] returns [{},{y+1=2}]

*)

let subst1_in_subst x e sigma =
  try
    let f = VarMap.find x sigma in
    let d = sub e f in
    try
      let y = leading_var d in
      let ke = try VarMap.find y e.vars with Not_found -> Numbers.zero
      and kf = try VarMap.find y f.vars with Not_found -> Numbers.zero
      in
      let c = Numbers.compare (Numbers.abs ke) (Numbers.abs kf) in
      let c' = 
	(* if they have the same absolute value, then
	   the smallest is the positive one, so the smallest is 
	   the largest for the natural ordering, hence the inversion 
	   of the comparison *)
	if c = 0 then Numbers.compare kf ke else c 
      in
	if c' < 0 then 
	  (* e is smaller than f *)
	  VarMap.remove x sigma,Ptset.singleton(eq e f)
	else
	  if c' > 0 then 
	    (* f is smaller than e *)
	    VarMap.remove x sigma,Ptset.singleton(eq e f)
	  else
	    assert false
	      
    with
	Not_found ->
	  (* so d is a constant *)
	  if Numbers.is_zero d.const then (VarMap.remove x sigma,Ptset.empty)
	  else raise Degenerate
  with
      Not_found ->
	let e' = subst_expr sigma e in
	let sigma' = 
	  (VarMap.fold
	     (fun y f sigma -> 
		if x.var_tag < y.var_tag
		then
		  VarMap.add y (subst1_expr x e' f) sigma
		else
		  VarMap.add y f sigma)
	     sigma
	     VarMap.empty)
	in sigma', Ptset.empty
       
;;

(*

  [subst_in_subst sigma sigma'] applies [sigma] to [sigma']

  example:

  [subst_in_subst  {y->2,z->t} {x->y+1,z->3}]
   returns [{x->3} {t=3}]

*)

let subst_in_subst sigma sigma' =
  VarMap.fold
    (fun x e (s,acc) ->
       let (s',acc') = subst1_in_subst x e s in
       (s',Ptset.union acc' acc))
    sigma
    (sigma',Ptset.empty)
;;

(*

  [add_in_subst : 
    substitution -> var_id -> expr -> 
      substitution option * formula option]

  [add_in_subst sigma x e] adds [{x->e}] in [sigma],
  returns [(sigma',S)], [sigma'] is [None] if [sigma] does not change 
  [S] is an optional additional constraint, if [x] already occurs in [sigma]. 
  
  raises [Degenerate] if [sigma] already contains a [{x -> e'}] 
  where [e-e' = cte <> 0]. 

  examples (if [x] is greater than [y])

  [add_in_subst {x->1} y 2]   returns [Some({x->1, y->2}),None]

  [add_in_subst {x->y+1} y 2] returns [Some({x->3, y->2}),None]

  [add_in_subst {x->1} x 1]   returns [None,None]

  [add_in_subst {x->1} x 2]   raises [Degenerate]

  [add_in_subst {x->y+1} x 2] returns [Some({x->2}),Some(y+1=2)] 

  [add_in_subst {x->2} x y+1] returns [None,Some(y+1=2)] 

*)



let add_in_subst sigma x e =
  try
    let f = VarMap.find x sigma in
    let d = sub e f in
    try
      let y = leading_var d in
      let ke = try VarMap.find y e.vars with Not_found -> Numbers.zero
      and kf = try VarMap.find y f.vars with Not_found -> Numbers.zero
      in
      let c = Numbers.compare (Numbers.abs ke) (Numbers.abs kf) in
      let c' = 
	(* if they have the same absolute value, then
	   the smallest is the positive one, so the smallest is 
	   the largest for the natural ordering, hence the inversion 
	   of the comparison *)
	if c = 0 then Numbers.compare kf ke else c 
      in
      if c' < 0 then 
	(* e is smaller than f *)
	Some(VarMap.add x e sigma),Some(eq e f)
      else
	if c' > 0 then 
	  (* f is smaller than e *)
	  None,Some(eq e f)
	else
	  assert false
      
    with
	Not_found ->
	  (* so d is a constant *)
	  if Numbers.is_zero d.const then (None,None)
	  else raise Degenerate
  with
      Not_found ->
	let e' = subst_expr sigma e in
	let sigma' = 
	  (VarMap.fold
	     (fun y f sigma -> 
		if x.var_tag < y.var_tag
		then
		  VarMap.add y (subst1_expr x e' f) sigma
		else
		  VarMap.add y f sigma)
	  sigma
	     (VarMap.add x e' VarMap.empty))
	in Some(sigma'), None
       
;;

let rec subst1 v e' f = 
  match f.node with
    | True -> true_formula
    | False -> false_formula
    | Null(e) -> null (subst1_expr v e' e)            
    | PositiveOrNull(e) -> positive_or_null (subst1_expr v e' e)
    | Divisible(e,k) -> divides k (subst1_expr v e' e)
    | And(s,l) ->
	begin
	  try
	    let sigma1,h = subst1_in_subst v e' s in
	    let sigma2,l2 = 
	      add_in_conj_map sigma1 Ptset.empty (fun f -> subst1 v e' f) 
		(Ptset.union h l)
	    in hash_conj sigma2 l2
	  with
	      Degenerate -> false_formula
	end
    | Or(l) -> map_disj_set (fun f -> subst1 v e' f) l 
    | Not(f1) -> neg(subst1 v e' f1)
    | Implies(f1,f2) -> implies (subst1 v e' f1) (subst1 v e' f2)
    | Equiv(f1,f2) -> equiv (subst1 v e' f1) (subst1 v e' f2)
    | Forall(l,f1) -> if List.memq v l then f else forall_s l (subst1 v e' f)
    | Exists(l,f1) -> if List.memq v l then f else exists_s l (subst1 v e' f)


and subst sigma f = 
  match f.node with
    | True -> true_formula
    | False -> false_formula
    | Null(e) -> null (subst_expr sigma e)            
    | PositiveOrNull(e) -> positive_or_null (subst_expr sigma e)            
    | Divisible(e,k) -> divides k (subst_expr sigma e)
    | And(s,l) -> 
	begin
	  try
	    let sigma1,h = subst_in_subst sigma s in
	    let sigma2,l2 = 
	      add_in_conj_map sigma1 Ptset.empty (fun f -> subst sigma f) 
		(Ptset.union h l)
	    in hash_conj sigma2 l2
	  with
	      Degenerate -> false_formula
	end
    | Or(l) -> map_disj_set (subst sigma) l 
    | Not(f1) -> neg(subst sigma f1)
    | Implies(f1,f2) -> implies (subst sigma f1) (subst sigma f2)
    | Equiv(f1,f2) -> equiv (subst sigma f1) (subst sigma f2)
    | Forall(l,f1) -> 
	let sigma' = 
	  List.fold_left
	    (fun acc x -> VarMap.remove x acc)
	    sigma l
	in
	forall_s l (subst sigma' f1)
    | Exists(l,f1) -> 
	let sigma' = 
	  List.fold_left
	    (fun acc x -> VarMap.remove x acc)
	    sigma l
	in
	exists_s l (subst sigma' f1)

(*

  [add_in_conj : 
    substitution -> formula Ptset.t -> formula -> 
      substitution * formula Ptset.t]

*)


and add_in_conj sigma s f =
  let f = subst sigma f in
  match f.node with
    | True -> (sigma,s)
    | False -> raise Degenerate
    | Null(e) ->
  	begin
	  try
	    let x,n = expr_to_subst e in
	    match add_in_subst sigma x n with
	      | None,None -> (sigma,s)
	      | Some(sigma'),None -> 
		  Ptset.fold 
		    (fun h (sigma,s) -> add_in_conj sigma s h)
		    s
		    (sigma',Ptset.empty)
	      | None,Some(g) -> 
		  add_in_conj sigma s g
	      | Some(sigma'),Some(g) -> 
		  Ptset.fold 
		    (fun h (sigma,s) -> add_in_conj sigma s h)
		    (Ptset.add g s)
		    (sigma',Ptset.empty)
	  with
	      Not_found -> 
		(sigma,Ptset.add f s)
	end
    | _ -> 
	(sigma,Ptset.add f s)


and add_in_conj_map sigma s f t =
  Ptset.fold 
    (fun form (sigma,s) -> add_in_conj sigma s (f form)) t (sigma,s)

  

and conj f1 f2 = 
  try
    match (f1.node,f2.node) with
      | (True,_) -> f2
      | (_,True) -> f1
      | (False,_) -> false_formula
      | (_,False) -> false_formula
      | (And(s1,l1),And(s2,l2)) -> 
	  let (s,h) =
	    VarMap.fold
	      (fun x e (sigma,acc) ->
		 match add_in_subst sigma x e with
		   | None,None -> (sigma,acc)
		   | Some(sigma'),None -> (sigma',acc)
		   | None,Some(g) -> (sigma,Ptset.add g acc)
		   | Some(sigma'),Some(g) -> (sigma',Ptset.add g acc))
	      s2
	      (s1,Ptset.empty)
	  in
	  let (s,acc) =
	    Ptset.fold
	      (fun f (s,a) -> add_in_conj s a f)
	      h
	      (s,Ptset.empty)
	  in
	  let (s,acc) =
	    Ptset.fold
	      (fun f (s,a) -> add_in_conj s a f)
	      l1
	      (s,acc)
	  in
	  let (s,acc) =
	    Ptset.fold
	      (fun f (s,a) -> add_in_conj s a f)
	      l2
	      (s,acc)
	  in hash_conj s acc
      | (And(s1,l1),_) -> 
	  let (s,e) = add_in_conj s1 l1 f2 in
	  hash_conj s e
      | (_,And(s2,l2)) -> 
	  let (s,e) = add_in_conj s2 l2 f1 in
	  hash_conj s e
      | (_,_) -> 
	  let (s,e) = add_in_conj VarMap.empty Ptset.empty f1 in
	  let (s,e) = add_in_conj s e f2 in
	  hash_conj s e
  with
      Degenerate -> false_formula

;;

(*

  [map_conj f fold l] 
  return the conjunction of formulas f(x) for each x in l

  [map_disj f l] return the disjunction of formulas f(x) for each x in l

  [disji] f n] returns the disjunction of formulas f(i) for $0\leq i\leq n-1$. 
*)

let map_conj_no_subst f s l =
  try
    let (sigma,e) =
      Ptset.fold
	(fun form (s,a) ->
	   add_in_conj s a (f form))	
	l
	(s,Ptset.empty)
    in
    hash_conj sigma e
  with Degenerate -> false_formula
;;

let map_conj_subst f s l =
   try
     let (sigma,e) =
       VarMap.fold
	 (fun x e (s,a) ->
	    add_in_conj s a (f (eq (var x) e)))
	 s
	 (VarMap.empty,Ptset.empty)
     in 
     let (sigma,e) =
       Ptset.fold
	 (fun form (s,a) ->
	    add_in_conj s a (f form))	
	 l
	 (sigma,e)
    in
    hash_conj sigma e
  with Degenerate -> false_formula
;;
   

  
let rec conj_list l = 
  match l with
    | [] -> true_formula
    | [f] -> f
    | f::l -> conj f (conj_list l)
;;




let map_conj2 f fold accu l =
  fold 
    (fun absform (env,linform) -> 
       let (env',linform') = f env absform in env',conj linform linform') 
    l 
    (accu,true_formula)
;;


(*

  \subsection{Free variables}

*)

let free_vars_var global_env local_env x =
  if List.memq x local_env 
  then global_env
  else if List.memq x global_env
  then global_env
  else x::global_env
;;

let free_vars_expr global_env local_env e =
  VarMap.fold
    (fun x _ accu -> free_vars_var accu local_env x)
    e.vars
    global_env


let rec free_vars_formula global_env local_env f =
  match f.node with 
  | True | False -> global_env
  | Divisible(e,_) | PositiveOrNull(e) | Null(e) ->
      free_vars_expr global_env local_env e
  | And(s,l)  -> 
      let genv = 
	VarMap.fold
	  (fun x e genv ->
	     let genv = free_vars_var genv local_env x in
	     free_vars_expr genv local_env e)
	  s
	  global_env
      in
      Ptset.fold
	(fun f genv -> free_vars_formula genv local_env f)
	l 
	genv
  | Or(l) ->
      Ptset.fold
	(fun f genv -> free_vars_formula genv local_env f)
	l 
	global_env
  | Not(f) -> free_vars_formula global_env local_env f
  | Implies(f1,f2) | Equiv(f1,f2) ->
      let genv = free_vars_formula global_env local_env f1 in
      free_vars_formula genv local_env f2
  | Exists(l,f) | Forall(l,f) ->
      free_vars_formula global_env (l@local_env) f

let free_vars_env env f =  free_vars_formula env [] f;;     
let free_vars f = free_vars_formula [] [] f;;



exception Var_found;;

let search_var_expr x e =
  try
    let _ = VarMap.find x e.vars in raise Var_found
  with
      Not_found -> ()
;;

let rec search_var x f = 
  match f.node with 
    | True | False -> ()
    | Divisible(e,_) | PositiveOrNull(e) | Null(e) ->
	search_var_expr x e
    | And(s,l)  -> 
	VarMap.iter
	  (fun y e ->
	     if x==y then raise Var_found
	     else
	       search_var_expr x e) s;
	Ptset.iter (search_var x) l
    | Or(l) ->
	Ptset.iter (search_var x) l
    | Not(f) -> search_var x f
    | Implies(f1,f2) | Equiv(f1,f2) ->
	search_var x f1;search_var x f2
    | Exists(l,f) | Forall(l,f) ->
	if not (List.memq x l) then search_var x f

let var_occurs x f =
  try
    search_var x f; false
  with
      Var_found -> true
;;

(*

\subsection{Instantiation}

*)


type instantiation = (unit,Numbers.t) VarMap.t;;

let inst1_expr v n e =
  try
    let v_coef = VarMap.find v e.vars in
    let others = VarMap.remove v e.vars in
    { const = Numbers.add e.const (Numbers.mult n v_coef) ;
      vars = others }
  with
      Not_found -> e
  
let inst1_in_subst x n sigma =
  try
    let f = VarMap.find x sigma in
    if is_cte f then
      if Numbers.eq n f.const then (sigma,Ptset.empty)
      else raise Degenerate
    else
      let d = cte n in
      VarMap.remove x sigma,Ptset.singleton(eq d f)	  
  with
      Not_found ->
	let sigma' = 
	  (VarMap.fold
	     (fun y f sigma -> 
		if x.var_tag < y.var_tag
		then
		  VarMap.add y (inst1_expr x n f) sigma
		else
		  VarMap.add y f sigma)
	     sigma
	     VarMap.empty)
	in sigma', Ptset.empty
       
;;


let rec inst1 v n f = 
  match f.node with
    | True -> true_formula
    | False -> false_formula
    | Null(e) -> null (inst1_expr v n e)
    | PositiveOrNull(e) -> positive_or_null (inst1_expr v n e)            
    | Divisible(e,k) -> divides k (inst1_expr v n e)
    | And(s,l) -> 
	begin
	  try
	    let sigma1,h = inst1_in_subst v n s in
	    let sigma2,l2 = 
	      add_in_conj_map sigma1 Ptset.empty (fun f -> inst1 v n f) 
		(Ptset.union h l)
	    in hash_conj sigma2 l2
	  with
	      Degenerate -> false_formula
	end
    | Or(l) -> map_disj_set (inst1 v n) l 
    | Not(f1) -> neg(inst1 v n f1)
    | Implies(f1,f2) -> implies (inst1 v n f1) (inst1 v n f2)
    | Equiv(f1,f2) -> equiv (inst1 v n f1) (inst1 v n f2)
    | Forall(l,f1) -> if List.memq v l then f else forall_s l (inst1 v n f1)
    | Exists(l,f1) -> if List.memq v l then f else exists_s l (inst1 v n f1)
;;

let inst_expr sigma e =
  VarMap.fold
    (fun x k acc ->
       try
	 let n = VarMap.find x sigma in
	 add_cte acc (Numbers.mult k n)
       with
	   Not_found -> add (times k (var x)) acc)
    e.vars
    (cte e.const)
;;
  
let inst_in_subst sigma sigma' =
  VarMap.fold
    (fun x e (s,acc) ->
       let (s',acc') = inst1_in_subst x e s in
       (s',Ptset.union acc' acc))
    sigma
    (sigma',Ptset.empty)
;;

let rec inst sigma f = 
  match f.node with
    | True -> true_formula
    | False -> false_formula
    | Null(e) -> null (inst_expr sigma e)
    | PositiveOrNull(e) -> positive_or_null (inst_expr sigma e)            
    | Divisible(e,k) -> divides k (inst_expr sigma e)
    | And(s,l) -> 
	begin
	  try
	    let sigma1,h = inst_in_subst sigma s in
	    let sigma2,l2 = 
	      add_in_conj_map sigma1 Ptset.empty (fun f -> inst sigma f) 
		(Ptset.union h l)
	    in hash_conj sigma2 l2
	  with
	      Degenerate -> false_formula
	end
    | Or(l) -> map_disj_set (inst sigma) l 
    | Not(f1) -> neg(inst sigma f1)
    | Implies(f1,f2) -> implies (inst sigma f1) (inst sigma f2)
    | Equiv(f1,f2) -> equiv (inst sigma f1) (inst sigma f2)
    | Forall(l,f1) -> 
	let sigma' = 
	  List.fold_left
	    (fun acc x -> VarMap.remove x acc)
	    sigma l
	in
	forall_s l (inst sigma' f1)
    | Exists(l,f1) -> 
	let sigma' = 
	  List.fold_left
	    (fun acc x -> VarMap.remove x acc)
	    sigma l
	in
	exists_s l (inst sigma' f1)
;;


(*

  \subsection{conversion form abstract formulas}

*)

exception Not_linear;;

let linear_mult e1 e2 = 
  if e1.vars = VarMap.empty
  then times e1.const e2
  else
    if e2.vars = VarMap.empty
    then times e2.const e1
    else raise Not_linear
;;

let linear_div e1 e2 = 
  if e2.vars = VarMap.empty
  then div e1 e2.const
  else
    raise Not_linear
;;

let linear_divides e1 e2 = 
  if e1.vars = VarMap.empty
  then divides e1.const e2
  else
    raise Not_linear
;;

type var_env = (string * var_id) list;;

let rec from_abstract_expr env e =
  match e with
    | Abstract_constraint.Cte(n) -> env,(cte n)
    | Abstract_constraint.Var(x) -> 
	begin
	  try
	    let v = var (List.assoc x env) in env,v
	  with
	      Not_found -> 
		let v = make_var x in (x,v)::env,var v
	end
    | Abstract_constraint.Plus(e1,e2) -> 
	let env1,e1 = from_abstract_expr env e1 in
	let env2,e2 = from_abstract_expr env1 e2 in
	env2,add e1 e2
    | Abstract_constraint.Sub(e1,e2) -> 
	let env1,e1 = from_abstract_expr env e1 in
	let env2,e2 = from_abstract_expr env1 e2 in
	env2,sub e1 e2
    | Abstract_constraint.Minus(e) -> 
	let env1,e1 = from_abstract_expr env e in
	env1,minus e1
    | Abstract_constraint.Mult(e1,e2) -> 
	let env1,e1 = from_abstract_expr env e1 in
	let env2,e2 = from_abstract_expr env1 e2 in
	env2,linear_mult e1 e2
    | Abstract_constraint.Quotient(e1,e2) -> 
	let env1,e1 = from_abstract_expr env e1 in
	let env2,e2 = from_abstract_expr env1 e2 in
	env2,linear_div e1 e2


let rec from_abstract_formula env f =
  match f with
    | Abstract_constraint.True -> env,true_formula
    | Abstract_constraint.False -> env,false_formula
    | Abstract_constraint.Comp(e1,op,e2) ->
	let env1,e1 = from_abstract_expr env e1 in
	let env2,e2 = from_abstract_expr env1 e2 in
	begin
	  env2,
	  match op with
	    | "=" -> eq e1 e2
	    | ">" -> gt e1 e2
	    | ">=" -> ge e1 e2
	    | "<" -> lt e1 e2
	    | "<=" -> le e1 e2
	    | "<>" -> ne e1 e2
	    | "|" -> linear_divides e1 e2
	    | _ -> assert false
	end
    | Abstract_constraint.And(l) -> 
	map_conj2 from_abstract_formula List.fold_right env l
    | Abstract_constraint.Or(l) -> 
	map_disj2 from_abstract_formula List.fold_right env l
    | Abstract_constraint.Neg(f) -> 
	let env1,f1 = from_abstract_formula env f
	in env1,neg f1
    | Abstract_constraint.Implies(f1,f2) -> 
	let env1,f1 = from_abstract_formula env f1 in
	let env2,f2 = from_abstract_formula env1 f2 in
	env2, implies f1 f2
    | Abstract_constraint.Equiv(f1,f2) -> 
	let env1,f1 = from_abstract_formula env f1 in
	let env2,f2 = from_abstract_formula env1 f2 in
	env2, equiv f1 f2
    | Abstract_constraint.Exists(l,f) -> 
	let (vars,new_env) =
	  List.fold_right 
	    (fun x (accu,env) -> 
	       let v = make_var x in 
	       (v::accu,(x,v)::env))
	    l
	    ([],env)
	in
	let env1,f1 = from_abstract_formula new_env f in
	let env2 = 
	  List.filter
	    (fun (x,v) -> not (List.memq v vars)) env1 in
	env2,List.fold_right exists vars f1
    | Abstract_constraint.Forall(l,f) -> 
	let (vars,new_env) =
	  List.fold_right 
	    (fun x (accu,env) -> 
	       let v = make_var x in 
	       (v::accu,(x,v)::env))
	    l
	    ([],env)
	in
	let env1,f1 = from_abstract_formula new_env f in
	let env2 = 
	  List.filter
	    (fun (x,v) -> not (List.memq v vars)) env1 in
	env2,List.fold_right forall vars f1


 

(*


\subsection{Renaming}


*)


(* Type of the renaming tables *)

type var_renaming = (unit,var_id) VarMap.t

(* Rename all variables in an expression.*)

let rename_expr r e = 
  subst_expr 
    (VarMap.fold 
       (fun v1 v2 acc -> VarMap.add v1 (var v2) acc) r VarMap.empty)
    e
  
(* Rename all variables in a formula. *)
let rename_formula r f = 
  subst 
    (VarMap.fold 
       (fun v1 v2 acc -> VarMap.add v1 (var v2) acc) r VarMap.empty)
    f
 
(* [build_renaming l] builds a fresh renaming for the vars in 
   [l].  *) 
 
let build_renaming l =
  List.fold_left 
    (fun acc vid -> 
       VarMap.add vid (make_var_uniq_name vid.var_name) acc)
    VarMap.empty
    l




(*

  \subsection{Removing denominators}

*)

  

  
let rec remove_denominators f =
  match f.node with
    | True | False -> f
    | Not(g) -> neg(remove_denominators g)
    | Null(e) -> 
	let d = common_denominator e in
	if Numbers.eq d Numbers.one then f else 
	  null(times d e)
    | PositiveOrNull(e) -> 
	let d = common_denominator e in
	if Numbers.eq d Numbers.one then f else 
	  positive_or_null(times d e)
    | Divisible(e,n) -> 
	let d = common_denominator e in
	if Numbers.eq d Numbers.one then f else
	divides (Numbers.mult d n) (times d e)
    | Forall (l, g) -> forall_s l (remove_denominators g)
    | Exists (l, g) -> exists_s l (remove_denominators g)
    | Equiv (f1, f2) ->
	equiv (remove_denominators f1) (remove_denominators f2)
    | Implies (f1, f2) -> 
	implies (remove_denominators f1) (remove_denominators f2)
    | Or(s) -> map_disj_set remove_denominators s
    | And(s,l) -> 
	map_conj_subst remove_denominators s l 

;;

