
type expr =
  | Cte of Numbers.t
  | Var of string
  | Plus of expr * expr
  | Mult of expr * expr
  | Sub of expr * expr
  | Minus of expr
  | Quotient of expr * expr
;;

(*i
let cte_zero = Cte(Num_utils.zero);;
i*)

let cte_one = Cte(Numbers.one);;

let plus e1 e2 = Plus(e1,e2);;
let mult e1 e2 = Mult(e1,e2);;
let minus e = Minus(e);;

let rec power e n =
  if n<=0 
  then cte_one
  else
    if n=1 
    then e
    else
      let p = power e (n/2) in
      let p2 = Mult(p,p) in
      if n mod 2=0 then p2 else Mult(e,p2)
;;

type formula =
  | True
  | False
  | Comp of expr * string * expr    (*r <,>,=,>=,<=, <> or | *)
  | And of formula list             (*r length at least 2 *)
  | Or of formula list              (*r length at least 2 *)
  | Neg of formula
  | Implies of formula * formula 
  | Equiv of formula * formula 
  | Exists of string list * formula (*r length at least 1 *)
  | Forall of string list * formula (*r length at least 1 *)


let divisible e n = Comp(n,"|",e);;

let neg f = Neg(f);;

let exists v f = match v with
  | [] -> f
  | _ -> Exists(v,f)

let forall v f = match v with
  | [] -> f
  | _ -> Forall(v,f)


let conj f1 f2 =
  match (f1,f2) with
    | False,_ | _,False -> False
    | True,x  | x,True -> x
    | (And l1,And l2) -> And(List.rev_append l1 l2)
    | (And l1,_) -> And(f2::l1)
    | (_,And l2) -> And(f1::l2)
    | (_,_) -> And([f1;f2])
;;

let conj_all l =
  let rec aux l accu =
  match l with
    | [] -> accu
    | x::r -> aux r (conj x accu)
  in
  aux l True

let disj f1 f2 =
  match (f1,f2) with
    | False,x | x,False -> x
    | True,_ | _,True -> True
    | (Or l1,Or l2) -> Or(List.rev_append l1 l2)
    | (Or l1,_) -> Or(f2::l1)
    | (_,Or l2) -> Or(f1::l2)
    | (_,_) -> Or([f1;f2])
;;

let disj_all l =
  let rec aux l accu =
  match l with
    | [] -> accu
    | x::r -> aux r (disj x accu)
  in
  aux l False
;;


let rec free_vars_expr global_env local_env e =
  match e with 
  | Cte(n) -> global_env
  | Var(x) -> 
      if List.mem x local_env 
      then global_env 
      else if List.mem x global_env
      then global_env
      else x::global_env
  | Plus(e1,e2)
  | Sub(e1,e2)
  | Mult(e1,e2)
  | Quotient(e1,e2) ->
      let genv = free_vars_expr global_env local_env e1 in
      free_vars_expr genv local_env e2
  | Minus(e) -> free_vars_expr global_env local_env e
;;


let rec free_vars_formula global_env local_env f =
  match f with 
  | True 
  | False -> global_env
  | Comp(e1,_,e2) ->
      let genv = free_vars_expr global_env local_env e1 in
      free_vars_expr genv local_env e2
  | And(l) 
  | Or(l) ->
      List.fold_left
	(fun genv f -> free_vars_formula genv local_env f)
	global_env
	l
  | Neg(f) -> free_vars_formula global_env local_env f
  | Implies(f1,f2) 
  | Equiv(f1,f2) ->
      let genv = free_vars_formula global_env local_env f1 in
      free_vars_formula genv local_env f2
  | Exists(l,f) 
  | Forall(l,f) ->
      free_vars_formula global_env (l@local_env) f

      
let free_vars f = free_vars_formula [] [] f;;
  
open Format;;

let rec print_expr e =
  match e with
  | Cte(n) -> printf "%s" (Numbers.to_string n)
  | Var(x) -> printf "%s" x
  | Plus(e1,e2) ->
      printf "@[(";
      print_expr e1;
      printf " +@ ";
      print_expr e2;
      printf ")@]"
  | Sub(e1,e2) ->
      printf "@[(";
      print_expr e1;
      printf " -@ ";
      print_expr e2;
      printf ")@]"
  | Mult(e1,e2) ->
      printf "@[(";
      print_expr e1;
      printf " .@ ";
      print_expr e2;
      printf ")@]"
  | Quotient(e1,e2) ->
      printf "@[(";
      print_expr e1;
      printf " /@ ";
      print_expr e2;
      printf ")@]"
  | Minus(e) ->
      printf "@[(";
      printf "-@ ";
      print_expr e;
      printf ")@]"
;;

let rec print_formula f =
  match f with
  | True -> printf "true"
  | False -> printf "false"
  | Comp(e1,op,e2) ->
      printf "@[";
      print_expr e1;
      printf " %s@ " op;
      print_expr e2;
      printf "@]"
  | And(f::l) ->
      assert (List.length l > 0);
      printf "@[(";
      print_formula f;
      List.iter	(fun f -> printf " and@ ";print_formula f) l;
      printf ")@]"
  | Or(f::l) ->
      assert (List.length l > 0);
      printf "@[(";
      print_formula f;
      List.iter (fun f -> printf " or@ ";print_formula f) l;
      printf ")@]"
  | Implies(f1,f2) ->
      printf "@[(";
      print_formula f1;
      printf " ->@ ";
      print_formula f2;
      printf ")@]"
  | Neg(f) ->
      printf "@[(not ";
      print_formula f;
      printf ")@]"
  | Equiv(f1,f2) ->
      printf "@[(";
      print_formula f1;
      printf " <->@ ";
      print_formula f2;
      printf ")@]"
  | Exists(x::l,f) ->
      printf "@[";
      printf "exists %s" x;
      List.iter (fun x -> printf ",%s" x) l;
      printf "@ (";
      print_formula f;
      printf ")@]"
  | Forall(x::l,f) ->
      printf "@[";
      printf "forall %s" x;
      List.iter (fun x -> printf ",%s" x) l;
      printf "@ (";
      print_formula f;
      printf ")@]"
  | Exists([],_) 
  | Forall([],_) 
  | And([]) 
  | Or([]) -> assert false

let rec rename_expr r e = 
  match e with
    | Cte(n) -> e
    | Var(x) -> (try Var(List.assoc x r) with Not_found -> e)
    | Plus(e1,e2) -> Plus(rename_expr r e1, rename_expr r e2)
    | Sub(e1,e2) -> Sub(rename_expr r e1, rename_expr r e2)
    | Mult(e1,e2) -> Mult(rename_expr r e1, rename_expr r e2)
    | Quotient(e1,e2) -> Quotient(rename_expr r e1, rename_expr r e2)
    | Minus(e) -> Minus (rename_expr r e)
;;

let replace r s = 
  try
    List.assoc s r
  with Not_found -> s
  
let rec rename_formula r f = 
  match f with
  | True | False -> f
  | Comp(e1,op,e2) ->
      Comp(rename_expr r e1,op,rename_expr r e2)
  | And(l) ->
      And(List.rev_map (rename_formula r) l)
  | Or(l) ->
      Or(List.rev_map (rename_formula r) l)
  | Neg(f) ->
      Neg(rename_formula r f)
  | Implies(f1,f2) ->
      Implies(rename_formula r f1, rename_formula r f2)
  | Equiv(f1,f2) ->
      Equiv(rename_formula r f1, rename_formula r f2)
  | Exists(l,f) ->
      Exists(List.rev_map (replace r) l,rename_formula r f)
  | Forall(l,f) ->
     Forall(List.rev_map (replace r) l,rename_formula r f)
;;


let build_renaming,new_var =
  let counter = ref 0 in
    (function l -> 
      List.map 
      (function s -> 
	 incr counter;
	 (s,s^"_"^(string_of_int !counter))
      )
      l),
    (function s -> incr counter ; s^"_"^(string_of_int !counter))

(*
let divisible e1 e2 = 
  match build_renaming (free_vars_expr [] [] e2) with 
      [] ->  Exists(["Q"],Comp(e1,"=",mult e2 (Var "Q")))
    | (_,s)::_ -> Exists([s],Comp(e1,"=",mult e2 (Var s)))

let rec normalize e = match e with 
  | Cte(n) -> e, (Cte Num_utils.one)
  | Var(x) -> e, (Cte Num_utils.one)
  | Plus(l) ->
      let m = List.rev_map normalize l in
	List.fold_left (fun (n1,d1) (n2,d2) -> 
			  (plus (mult n1 d2) (mult n2 d1)),
			  (mult d1 d2))
	  (Cte Num_utils.zero, Cte Num_utils.one)
	  m
	  
  | Mult(l) ->
      let m = List.rev_map normalize l in
	List.fold_left (fun (n1,d1) (n2,d2) -> (mult n1 n2,mult d1 d2))
	  (Cte Num_utils.one, Cte Num_utils.one)
	  m
  | Minus(e) -> 
      let n1,d1 = normalize e in
	(minus n1),d1

let rec compact f = match f with 
  | True | False -> f
  | Comp(e1,"=",e2) when e1=e2 -> True 
  | Comp(e1,op,e2) -> f
  | And(l) ->
      make_and (compact_and l)
  | Or(l) ->
      make_or (compact_and l)
 
  | Neg(True) -> False
  | Neg(False) -> True
  | Neg(f) -> Neg (compact f)
  | Implies(f1,f2) ->
      Implies(compact f1, compact f2)
  | Equiv(f1,f2) ->
      Equiv(compact f1, compact f2)
  | Exists(l,f) ->
      Exists(l, compact f)
  | Forall(l,f) ->
     Forall(l,compact f)
and compact_and l = 
  let rec compact_and_local l = match l with 
    | [] -> []
    | x::l -> let l' = compact_and l in
	if List.exists (fun e -> e=x) l' then l' else x::l'
  in
    compact_and_local (List.rev_map compact l)

*)
