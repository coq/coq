(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(**************************************************************************)
(*                                                                        *)
(* Omega: a solver of quantifier-free problems in Presburger Arithmetic   *)
(*                                                                        *)
(* Pierre Crégut (CNET, Lannion, France)                                  *)
(*                                                                        *)
(**************************************************************************)

(* $Id$ *) 

open Util
open Hashtbl
open Names

let flat_map f =
 let rec flat_map_f = function
   | [] -> [] 
   | x :: l -> f x @ flat_map_f l
 in 
 flat_map_f

let pp i = print_int i; print_newline (); flush stdout

let debug = ref false

let filter = List.partition

let push v l = l := v :: !l

let rec pgcd x y = if y = 0 then x else pgcd y (x mod y)

let pgcd_l = function
  | [] -> failwith "pgcd_l"
  | x :: l -> List.fold_left pgcd x l

let floor_div a b =
  match a >=0 , b > 0 with
    | true,true -> a / b
    | false,false -> a / b
    | true, false -> (a-1) / b - 1
    | false,true  -> (a+1) / b - 1

let new_id =
  let cpt = ref 0 in fun () -> incr cpt; ! cpt

let new_var =
  let cpt = ref 0 in fun () -> incr cpt; Nameops.make_ident "WW" (Some !cpt)
    
let new_var_num =
  let cpt = ref 1000 in (fun () -> incr cpt; !cpt)
					  
type coeff = {c: int ; v: int}

type linear = coeff list

type eqn_kind = EQUA | INEQ | DISE

type afine = { 
  (* a number uniquely identifying the equation *)
  id: int ; 
  (* a boolean true for an eq, false for an ineq (Sigma a_i x_i >= 0) *)
  kind: eqn_kind; 
  (* the variables and their coefficient *)
  body: coeff list; 
  (* a constant *)
  constant: int }

type action =
  | DIVIDE_AND_APPROX of afine * afine * int * int
  | NOT_EXACT_DIVIDE of afine * int
  | FORGET_C of int
  | EXACT_DIVIDE of afine * int
  | SUM of int * (int * afine) * (int * afine)
  | STATE of afine * afine * afine * int * int
  | HYP of afine
  | FORGET   of int * int
  | FORGET_I of int * int
  | CONTRADICTION of afine * afine
  | NEGATE_CONTRADICT of afine * afine * bool
  | MERGE_EQ of int * afine * int 
  | CONSTANT_NOT_NUL of int * int
  | CONSTANT_NUL of int
  | CONSTANT_NEG of int * int
  | SPLIT_INEQ of afine * (int * action list) * (int * action list)
  | WEAKEN of int * int

exception UNSOLVABLE

exception NO_CONTRADICTION

let intern_id,unintern_id =
  let cpt = ref 0 in
  let table = create 7 and co_table = create 7 in
  (fun (name : identifier) -> 
     try find table name with Not_found -> 
       let idx = !cpt in
       add table name idx; add co_table idx name; incr cpt; idx),
  (fun idx -> 
     try find co_table idx with Not_found -> 
       let v = new_var () in add table v idx; add co_table idx v; v)

let display_eq (l,e) =
  let _ = 
    List.fold_left 
      (fun not_first f ->
	 print_string 
	   (if f.c < 0 then "- " else if not_first then "+ " else "");
	 let c = abs f.c in
	 if c = 1 then 
	   Printf.printf "%s " (string_of_id (unintern_id f.v))
	 else 
	   Printf.printf "%d %s " c (string_of_id (unintern_id f.v)); 
	 true)
      false l
  in
  if e > 0 then 
    Printf.printf "+ %d " e 
  else if e < 0 then 
    Printf.printf "- %d " (abs e)

let operator_of_eq = function 
  | EQUA -> "=" | DISE -> "!=" | INEQ -> ">="

let kind_of = function
  | EQUA -> "equation" | DISE -> "disequation" | INEQ -> "inequation"

let display_system l = 
  List.iter 
    (fun { kind=b; body=e; constant=c; id=id} -> 
       print_int id; print_string ": ";
       display_eq (e,c); print_string (operator_of_eq b);
       print_string "0\n") 
    l;
  print_string "------------------------\n\n"

let display_inequations l = 
  List.iter (fun e -> display_eq e;print_string ">= 0\n") l;
  print_string "------------------------\n\n"

let rec display_action = function
  | act :: l -> begin match act with
      | DIVIDE_AND_APPROX (e1,e2,k,d) ->
          Printf.printf 
            "Inequation E%d is divided by %d and the constant coefficient is \
            rounded by substracting %d.\n" e1.id k d
      | NOT_EXACT_DIVIDE (e,k) ->
          Printf.printf
            "Constant in equation E%d is not divisible by the pgcd \
            %d of its other coefficients.\n" e.id k
      | EXACT_DIVIDE (e,k) ->
          Printf.printf
            "Equation E%d is divided by the pgcd \
            %d of its coefficients.\n" e.id k
      | WEAKEN (e,k) ->
          Printf.printf 
            "To ensure a solution in the dark shadow \
            the equation E%d is weakened by %d.\n" e k
      | SUM (e,(c1,e1),(c2,e2)) -> 
          Printf.printf
            "We state %s E%d = %d %s E%d + %d %s E%d.\n" 
            (kind_of e1.kind) e c1 (kind_of e1.kind) e1.id c2 
            (kind_of e2.kind) e2.id
      | STATE (e,_,_,x,_) ->
          Printf.printf "We define a new equation %d :" e.id; 
          display_eq (e.body,e.constant); 
          print_string (operator_of_eq e.kind); print_string " 0\n"
      | HYP e ->   
          Printf.printf "We define %d :" e.id; 
          display_eq (e.body,e.constant); 
          print_string (operator_of_eq e.kind); print_string " 0\n"
      | FORGET_C e ->  Printf.printf "E%d is trivially satisfiable.\n" e
      | FORGET (e1,e2) -> Printf.printf "E%d subsumes E%d.\n" e1 e2
      | FORGET_I (e1,e2) -> Printf.printf "E%d subsumes E%d.\n" e1 e2
      | MERGE_EQ (e,e1,e2) ->
         Printf.printf "E%d and E%d can be merged into E%d.\n" e1.id e2 e
      | CONTRADICTION (e1,e2) -> 
          Printf.printf
            "equations E%d and E%d implie a contradiction on their \
            constant factors.\n" e1.id e2.id
      | NEGATE_CONTRADICT(e1,e2,b) ->
          Printf.printf
            "Eqations E%d and E%d state that their body is at the same time
            equal and different\n" e1.id e2.id
      | CONSTANT_NOT_NUL (e,k) -> 
          Printf.printf "equation E%d states %d=0.\n" e k
      | CONSTANT_NEG(e,k) -> 
          Printf.printf "equation E%d states %d >= 0.\n" e k
      | CONSTANT_NUL e ->
          Printf.printf "inequation E%d states 0 != 0.\n" e
      | SPLIT_INEQ (e,(e1,l1),(e2,l2)) -> 
          Printf.printf "equation E%d is split in E%d and E%d\n\n" e.id e1 e2;
          display_action l1;
          print_newline ();
          display_action l2;
          print_newline ()
    end; display_action l
  | [] -> 
      flush stdout

(*""*)

let add_event, history, clear_history =
  let accu = ref [] in
  (fun (v : action) -> if !debug then display_action [v]; push v accu), 
  (fun () -> !accu),
  (fun () -> accu := [])

let nf_linear = Sort.list (fun x y -> x.v > y.v)

let nf ((b : bool),(e,(x : int))) = (b,(nf_linear e,x))

let map_eq_linear f = 
  let rec loop = function
    | x :: l -> let c = f x.c in if c=0 then loop l else {v=x.v; c=c} :: loop l
    | [] -> [] 
  in
  loop

let map_eq_afine f e = 
  { id = e.id; kind = e.kind; body = map_eq_linear f e.body; 
    constant = f e.constant }

let negate_eq = map_eq_afine (fun x -> -x)

let rec sum p0 p1 = match (p0,p1) with 
  | ([], l) -> l | (l, []) -> l
  | (((x1::l1) as l1'), ((x2::l2) as l2')) -> 
      if x1.v = x2.v then
	let c = x1.c + x2.c in
	if c = 0 then sum l1 l2 else {v=x1.v;c=c} :: sum l1 l2
      else if x1.v > x2.v then 
	x1 :: sum l1 l2'
      else 
	x2 :: sum l1' l2

let sum_afine eq1 eq2 = 
  { kind = eq1.kind; id = new_id ();
    body = sum eq1.body eq2.body; constant = eq1.constant + eq2.constant }

exception FACTOR1

let rec chop_factor_1 = function
  | x :: l -> 
      if abs x.c = 1 then x,l else let (c',l') = chop_factor_1 l in (c',x::l')
  | [] -> raise FACTOR1

exception CHOPVAR

let rec chop_var v = function
  | f :: l -> if f.v = v then f,l else let (f',l') = chop_var v l in (f',f::l')
  | [] -> raise CHOPVAR

let normalize ({id=id; kind=eq_flag; body=e; constant =x} as eq) =
  if e = [] then begin 
    match eq_flag with
      | EQUA ->
          if x =0 then [] else begin
            add_event (CONSTANT_NOT_NUL(id,x)); raise UNSOLVABLE
         end
      | DISE ->
          if x <> 0 then [] else begin
            add_event (CONSTANT_NUL id); raise UNSOLVABLE
          end
      | INEQ ->
          if x >= 0 then [] else begin
            add_event (CONSTANT_NEG(id,x)); raise UNSOLVABLE
          end
  end else
    let gcd = pgcd_l (List.map (fun f -> abs f.c) e) in
    if eq_flag=EQUA & x mod gcd <> 0 then begin
      add_event (NOT_EXACT_DIVIDE (eq,gcd)); raise UNSOLVABLE
    end else if eq_flag=DISE & x mod gcd <> 0 then begin
      add_event (FORGET_C eq.id); []
    end else if gcd <> 1 then begin
      let c = floor_div x gcd in
      let d = x - c * gcd in
      let new_eq = {id=id; kind=eq_flag; constant=c; 
                    body=map_eq_linear (fun c -> c / gcd) e} in
      add_event (if eq_flag=EQUA or eq_flag = DISE then EXACT_DIVIDE(eq,gcd)
                 else DIVIDE_AND_APPROX(eq,new_eq,gcd,d));
      [new_eq]
    end else [eq]

let eliminate_with_in {v=v;c=c_unite} eq2
                        ({body=e1; constant=c1} as eq1) =
  try
    let (f,_) = chop_var v e1 in 
    let coeff = if c_unite=1 then -f.c else if c_unite= -1 then f.c 
                else failwith "eliminate_with_in" in
    let res = sum_afine eq1 (map_eq_afine (fun c -> c * coeff) eq2) in
    add_event (SUM (res.id,(1,eq1),(coeff,eq2))); res
  with CHOPVAR -> eq1

let omega_mod a b = a - b * floor_div (2 * a + b) (2 * b)
let banerjee_step original l1 l2 = 
  let e = original.body in
  let sigma = new_var_num () in
  let smallest,var =
    try
      List.fold_left (fun (v,p) c ->  if v > (abs c.c) then abs c.c,c.v else (v,p))
              (abs (List.hd e).c, (List.hd e).v) (List.tl e)
    with Failure "tl" -> display_system [original] ; failwith "TL" in
  let m = smallest + 1 in
  let new_eq =
    { constant = omega_mod original.constant m;
      body = {c= -m;v=sigma} :: 
             map_eq_linear (fun a -> omega_mod a m) original.body;
      id = new_id (); kind = EQUA } in
  let definition =
    { constant = - floor_div (2 * original.constant + m) (2 * m);
      body = map_eq_linear (fun a -> - floor_div (2 * a + m) (2 * m))
                             original.body;
      id = new_id (); kind = EQUA } in
  add_event (STATE (new_eq,definition,original,m,sigma));
  let new_eq = List.hd (normalize new_eq) in
  let eliminated_var, def = chop_var var new_eq.body in
  let other_equations = 
    flat_map (fun e -> normalize (eliminate_with_in eliminated_var new_eq e))
             l1 in
  let inequations = 
    flat_map (fun e -> normalize (eliminate_with_in eliminated_var new_eq e))
             l2 in
  let original' = eliminate_with_in eliminated_var new_eq original in
  let mod_original = map_eq_afine (fun c -> c / m) original' in
  add_event (EXACT_DIVIDE (original',m));
  List.hd (normalize mod_original),other_equations,inequations

let rec eliminate_one_equation (e,other,ineqs) = 
  if !debug then display_system (e::other);
  try
    let v,def = chop_factor_1 e.body in
    (flat_map (fun e' -> normalize (eliminate_with_in v e e')) other,
     flat_map (fun e' -> normalize (eliminate_with_in v e e')) ineqs)
  with FACTOR1 -> eliminate_one_equation (banerjee_step e other ineqs)

let rec banerjee (sys_eq,sys_ineq) =
  let rec fst_eq_1 = function
     (eq::l) -> 
        if List.exists (fun x -> abs x.c = 1) eq.body then eq,l
        else let (eq',l') = fst_eq_1 l in (eq',eq::l')
   | [] -> raise Not_found in
  match sys_eq with
     [] -> if !debug then display_system sys_ineq; sys_ineq
   | (e1::rest) -> 
       let eq,other = try fst_eq_1 sys_eq with Not_found -> (e1,rest) in
       if eq.body = [] then 
         if eq.constant = 0 then begin
           add_event (FORGET_C eq.id); banerjee (other,sys_ineq)
         end else begin
           add_event (CONSTANT_NOT_NUL(eq.id,eq.constant)); raise UNSOLVABLE
         end
       else banerjee (eliminate_one_equation (eq,other,sys_ineq))
type kind = INVERTED | NORMAL
let redundancy_elimination system =
  let normal = function
     ({body=f::_} as e) when f.c < 0 ->  negate_eq e, INVERTED
   | e -> e,NORMAL in
  let table = create 7 in
  List.iter
    (fun e -> 
       let ({body=ne} as nx) ,kind = normal e in
       if ne = [] then
         if nx.constant < 0 then begin
           add_event (CONSTANT_NEG(nx.id,nx.constant)); raise UNSOLVABLE
         end else add_event (FORGET_C nx.id)
       else
       try 
         let (optnormal,optinvert) = find table ne in
         let final =
           if kind = NORMAL then begin
             match optnormal with 
                Some v -> 
                  let kept =
                    if v.constant < nx.constant 
                    then begin add_event (FORGET (v.id,nx.id));v end
                    else begin add_event (FORGET (nx.id,v.id));nx end in
                  (Some(kept),optinvert)
              | None -> Some nx,optinvert
           end else begin
             match optinvert with 
                Some v ->
                  let kept =
                    if v.constant > nx.constant 
                    then begin add_event (FORGET_I (v.id,nx.id));v end
                    else begin add_event (FORGET_I (nx.id,v.id));nx end in
                  (optnormal,Some(if v.constant > nx.constant then v else nx))
              | None -> optnormal,Some nx
           end in
         begin match final with
            (Some high, Some low) -> 
              if high.constant < low.constant then begin
                add_event(CONTRADICTION (high,negate_eq low));
                raise UNSOLVABLE
              end
          | _ -> () end;
         remove table ne;
         add table ne final
       with Not_found ->
         add table ne 
           (if kind = NORMAL then (Some nx,None) else (None,Some nx)))
    system;
  let accu_eq = ref [] in
  let accu_ineq = ref [] in
  iter
    (fun p0 p1 -> match (p0,p1) with 
       | (e, (Some x, Some y)) when x.constant = y.constant ->
           let id=new_id () in
           add_event (MERGE_EQ(id,x,y.id));
           push {id=id; kind=EQUA; body=x.body; constant=x.constant} accu_eq
       | (e, (optnorm,optinvert)) ->
           begin match optnorm with 
               Some x -> push x accu_ineq | _ -> () end;
           begin match optinvert with 
               Some x -> push (negate_eq x) accu_ineq | _ -> () end)
    table;
  !accu_eq,!accu_ineq

exception SOLVED_SYSTEM

let select_variable system =
  let table = create 7 in
  let push v c= 
    try let r = find table v in r := max !r (abs c)
    with Not_found -> add table v (ref (abs c)) in
  List.iter (fun {body=l} -> List.iter (fun f -> push f.v f.c) l) system;
  let vmin,cmin = ref (-1), ref 0 in
  let var_cpt = ref 0 in
  iter
    (fun v ({contents =  c}) ->
       incr var_cpt;
       if c < !cmin or !vmin = (-1) then begin vmin := v; cmin := c end)
    table;
  if !var_cpt < 1 then raise SOLVED_SYSTEM;
  !vmin

let classify v system =
  List.fold_left 
    (fun (not_occ,below,over) eq ->
       try let f,eq' = chop_var v eq.body in
       if f.c >= 0 then (not_occ,((f.c,eq) :: below),over)
       else (not_occ,below,((-f.c,eq) :: over))
       with CHOPVAR -> (eq::not_occ,below,over))
    ([],[],[]) system

let product dark_shadow low high =
  List.fold_left
    (fun accu (a,eq1) ->
       List.fold_left
         (fun accu (b,eq2) ->
            let eq = 
              sum_afine (map_eq_afine (fun c -> c * b) eq1)
                (map_eq_afine (fun c -> c * a) eq2) in
            add_event(SUM(eq.id,(b,eq1),(a,eq2)));
            match normalize eq with
	      | [eq] ->
                  let final_eq =
                    if dark_shadow then 
                      let delta = (a - 1) * (b - 1) in
                      add_event(WEAKEN(eq.id,delta));
                      {id = eq.id; kind=INEQ; body = eq.body; 
                       constant = eq.constant - delta} 
                    else eq
                  in final_eq :: accu
              | (e::_) -> failwith "Product dardk"
              | [] -> accu)
         accu high)
    [] low

let fourier_motzkin dark_shadow system =
  let v = select_variable system in
  let (ineq_out, ineq_low,ineq_high) = classify v system in
  let expanded = ineq_out @ product dark_shadow ineq_low ineq_high in
  if !debug then display_system expanded; expanded

let simplify dark_shadow system =
  if List.exists (fun e -> e.kind = DISE) system then 
    failwith "disequation in simplify";
  clear_history ();
  List.iter (fun e -> add_event (HYP e)) system;
  let system = flat_map normalize system in
  let eqs,ineqs = filter (fun e -> e.kind=EQUA) system in
  let simp_eq,simp_ineq = redundancy_elimination ineqs in
  let system = (eqs @ simp_eq,simp_ineq) in
  let rec loop1a system =
    let sys_ineq = banerjee system in 
    loop1b sys_ineq 
  and loop1b sys_ineq =
    let simp_eq,simp_ineq = redundancy_elimination sys_ineq in
    if simp_eq = [] then simp_ineq else loop1a (simp_eq,simp_ineq) 
  in
  let rec loop2 system =
    try
      let expanded = fourier_motzkin dark_shadow system in
      loop2 (loop1b expanded)
    with SOLVED_SYSTEM -> if !debug then display_system system; system 
  in
  loop2 (loop1a system)

let rec depend relie_on accu = function
  | act :: l -> 
      begin match act with
	| DIVIDE_AND_APPROX (e,_,_,_) ->
            if List.mem e.id relie_on then depend relie_on (act::accu) l
            else depend relie_on accu l
	| EXACT_DIVIDE (e,_) ->
            if List.mem e.id relie_on then depend relie_on (act::accu) l
            else depend relie_on accu l
	| WEAKEN (e,_) ->
            if List.mem e relie_on then depend relie_on (act::accu) l
            else depend relie_on accu l
	| SUM (e,(_,e1),(_,e2)) -> 
            if List.mem e relie_on then 
	      depend (e1.id::e2.id::relie_on) (act::accu) l
            else 
	      depend relie_on accu l
	| STATE (e,_,o,_,_) ->
            if List.mem e.id relie_on then
	      depend (o.id::relie_on) (act::accu) l
            else
	      depend relie_on accu l
	| HYP e ->   
            if List.mem e.id relie_on then depend relie_on (act::accu) l
            else depend relie_on accu l
	| FORGET_C _ -> depend relie_on accu l
	| FORGET _ -> depend relie_on accu l
	| FORGET_I _ -> depend relie_on accu l
	| MERGE_EQ (e,e1,e2) ->
            if List.mem e relie_on then 
	      depend (e1.id::e2::relie_on) (act::accu) l
            else 
	      depend relie_on accu l
	| NOT_EXACT_DIVIDE (e,_) -> depend (e.id::relie_on) (act::accu) l
	| CONTRADICTION (e1,e2) -> 
	    depend (e1.id::e2.id::relie_on) (act::accu) l
	| CONSTANT_NOT_NUL (e,_) -> depend (e::relie_on) (act::accu) l
	| CONSTANT_NEG (e,_) -> depend (e::relie_on) (act::accu) l
	| CONSTANT_NUL e -> depend (e::relie_on) (act::accu) l
	| NEGATE_CONTRADICT (e1,e2,_) -> 
            depend (e1.id::e2.id::relie_on) (act::accu) l
	| SPLIT_INEQ _ -> failwith "depend"
      end
  | [] -> relie_on, accu

let solve system =
  try let _ = simplify false system in failwith "no contradiction"
  with UNSOLVABLE -> display_action (snd (depend [] [] (history ())))
      
let negation (eqs,ineqs) =
  let diseq,_ = filter (fun e -> e.kind = DISE) ineqs in
  let normal = function
    | ({body=f::_} as e) when f.c < 0 ->  negate_eq e, INVERTED
    | e -> e,NORMAL in
  let table = create 7 in
  List.iter (fun e -> 
               let {body=ne;constant=c} ,kind = normal e in
               add table (ne,c) (kind,e)) diseq;
  List.iter (fun e ->
               if e.kind <> EQUA then pp 9999;
               let {body=ne;constant=c},kind = normal e in
               try 
		 let (kind',e') = find table (ne,c) in
		 add_event (NEGATE_CONTRADICT (e,e',kind=kind'));
		 raise UNSOLVABLE
               with Not_found -> ()) eqs

exception FULL_SOLUTION of action list * int list

let simplify_strong system =
  clear_history ();
  List.iter (fun e -> add_event (HYP e)) system;
  (* Initial simplification phase *)
  let rec loop1a system =
    negation system;
    let sys_ineq = banerjee system in 
    loop1b sys_ineq 
  and loop1b sys_ineq =
    let dise,ine = filter (fun e -> e.kind = DISE) sys_ineq in
    let simp_eq,simp_ineq = redundancy_elimination ine in
    if simp_eq = [] then dise @ simp_ineq
    else loop1a (simp_eq,dise @ simp_ineq) 
  in
  let rec loop2 system =
    try
      let expanded = fourier_motzkin false system in
      loop2 (loop1b expanded)
    with SOLVED_SYSTEM -> if !debug then display_system system; system 
  in
  let rec explode_diseq = function 
    | (de::diseq,ineqs,expl_map) ->
	let id1 = new_id () 
	and id2 = new_id () in
	let e1 = 
	  {id = id1; kind=INEQ; body = de.body; constant = de.constant - 1} in
	let e2 = 
	  {id = id2; kind=INEQ; body = map_eq_linear (fun x -> -x) de.body; 
           constant = - de.constant - 1} in
	let new_sys =
          List.map (fun (what,sys) -> ((de.id,id1,true)::what, e1::sys)) 
	    ineqs @ 
          List.map (fun (what,sys) -> ((de.id,id2,false)::what,e2::sys)) 
	    ineqs 
	in
	explode_diseq (diseq,new_sys,(de.id,(de,id1,id2))::expl_map)
    | ([],ineqs,expl_map) -> ineqs,expl_map 
  in
  try 
    let system = flat_map normalize system in
    let eqs,ineqs = filter (fun e -> e.kind=EQUA) system in
    let dise,ine = filter (fun e -> e.kind = DISE) ineqs in
    let simp_eq,simp_ineq = redundancy_elimination ine in
    let system = (eqs @ simp_eq,simp_ineq @ dise) in
    let system' = loop1a system in
    let diseq,ineq = filter (fun e -> e.kind = DISE) system' in
    let first_segment = history () in
    let sys_exploded,explode_map = explode_diseq (diseq,[[],ineq],[]) in
    let all_solutions =
      List.map
        (fun (decomp,sys) -> 
           clear_history ();
           try let _ = loop2 sys in raise NO_CONTRADICTION
           with UNSOLVABLE -> 
             let relie_on,path = depend [] [] (history ()) in
             let dc,_ = filter (fun (_,id,_) -> List.mem id relie_on) decomp in
             let red = List.map (fun (x,_,_) -> x) dc in
             (red,relie_on,decomp,path))
        sys_exploded 
    in
    let max_count sys = 
      let tbl = create 7 in
      let augment x = 
        try incr (find tbl x) with Not_found -> add tbl x (ref 1) in
      let eq = ref (-1) and c = ref 0 in
      List.iter (function 
		   | ([],r_on,_,path) -> raise (FULL_SOLUTION (path,r_on))
                   | (l,_,_,_) -> List.iter augment l) sys;
      iter (fun x v -> if !v > !c then begin eq := x; c := !v end) tbl;
      !eq 
    in
    let rec solve systems = 
      try 
	let id = max_count systems in 
        let rec sign = function 
	  | ((id',_,b)::l) -> if id=id' then b else sign l 
          | [] -> failwith "solve" in
        let s1,s2 = filter (fun (_,_,decomp,_) -> sign decomp) systems in
        let s1' = 
	  List.map (fun (dep,ro,dc,pa) -> (list_except id dep,ro,dc,pa)) s1 in
        let s2' = 
	  List.map (fun (dep,ro,dc,pa) -> (list_except id dep,ro,dc,pa)) s2 in
        let (r1,relie1) = solve s1' 
	and (r2,relie2) = solve s2' in
	let (eq,id1,id2) = List.assoc id explode_map in
	[SPLIT_INEQ(eq,(id1,r1),(id2, r2))], eq.id :: list_union relie1 relie2
      with FULL_SOLUTION (x0,x1) -> (x0,x1) 
    in
    let act,relie_on = solve all_solutions in
    snd(depend relie_on act first_segment)
  with UNSOLVABLE -> snd (depend [] [] (history ()))
