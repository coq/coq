(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

(* Yet another implementation of Fourier *)
open Num

module Cmp =
 (* How to compare pairs, lists ... *)
struct
 let rec compare_lexical l = 
  match l with
   | [] -> 0 (* Equal *)
   | f::l -> 
      let cmp = f () in
       if cmp = 0 	then  compare_lexical l else cmp
	
 let rec compare_list cmp l1 l2 = 
  match l1 , l2 with
   | []  , [] -> 0
   | []  , _  -> -1
   | _   , [] -> 1
   | e1::l1 , e2::l2 -> 
      let c = cmp e1 e2 in
       if c = 0 then compare_list cmp l1 l2 else c
	
 let hash_list hash l = 
  let rec xhash res l = 
   match l with
    | []  -> res 
    | e::l -> xhash ((hash e)  lxor res) l in
   xhash  (Hashtbl.hash []) l

end
 
module Interval = 
struct
 (** The type of intervals.  **)
 type intrvl = Empty | Point of num | Itv  of  num option * num option
  
 (**
    Different intervals can denote the same set of variables e.g., 
    Point n && Itv (Some n, Some n)
    Itv (Some x) (Some y) && Empty if x > y
    see the 'belongs_to' function.
 **)

 (* The set of numerics that belong to an interval *)
 let belongs_to n = function
  | Empty -> false
  | Point x -> n =/ x
  | Itv(Some x, Some y) -> x <=/ n && n <=/ y
  | Itv(None,Some y) -> n <=/ y
  | Itv(Some x,None) -> x <=/ n
  | Itv(None,None) -> true

 let string_of_bound = function
  | None -> "oo"
  | Some n -> Printf.sprintf "Bd(%s)"  (string_of_num n)

 let string_of_intrvl = function
  | Empty -> "[]"
  | Point n -> Printf.sprintf "[%s]" (string_of_num n)
  | Itv(bd1,bd2) -> 
     Printf.sprintf "[%s,%s]" (string_of_bound bd1) (string_of_bound bd2)

 let pick_closed_to_zero = function
  | Empty -> None
  | Point n -> Some n
  | Itv(None,None) -> Some (Int 0)
  | Itv(None,Some i) -> 
     Some (if  (Int 0) <=/ (floor_num  i) then Int 0 else floor_num i)
  | Itv(Some i,None) -> 
     Some (if i <=/ (Int 0) then Int 0 else ceiling_num i)
  | Itv(Some i,Some j) -> 
     Some (
      if i <=/ Int 0 && Int 0 <=/ j 
      then Int 0
      else if ceiling_num i <=/ floor_num j 
      then ceiling_num i (* why not *) else i)

 type status = 
   | O | Qonly | Z | Q 
       
 let interval_kind = function
  | Empty -> O
  | Point n -> if ceiling_num n =/ n then Z else Qonly
  | Itv(None,None) -> Z
  | Itv(None,Some i) -> if ceiling_num i <>/ i then Q else Z
  | Itv(Some i,None) -> if ceiling_num i <>/ i then Q else Z
  | Itv(Some i,Some j) -> 
     if ceiling_num i <>/ i or floor_num j <>/ j then Q else Z

 let empty_z = function
  | Empty -> true
  | Point n ->  ceiling_num n <>/ n 
  | Itv(None,None) | Itv(None,Some _) | Itv(Some _,None) -> false
  | Itv(Some i,Some j) -> ceiling_num i >/ floor_num j


 let normalise b1 b2 =
  match b1 , b2 with
   | Some i , Some j -> 
      (match compare_num i j with
       | 1 -> Empty
       | 0 -> Point i
       | _ -> Itv(b1,b2)
      )
   |  _ -> Itv(b1,b2)

       

 let min x y = 
  match x , y with
   | None , x | x , None -> x
   | Some i , Some j -> Some (min_num i j)
      
 let max x y = 
  match x , y with
   | None , x | x , None -> x
   | Some i , Some j -> Some (max_num i j)

 let inter i1 i2 = 
  match i1,i2 with
   | Empty , _ -> Empty
   |  _   , Empty -> Empty
   |  Point n , Point m -> if n =/ m then i1 else Empty
   | Point n , Itv (mn,mx) | Itv (mn,mx) , Point n-> 
      if (match mn with 
       | None -> true
       | Some mn ->  mn <=/ n) && 
       (match mx with 
	| None -> true
	| Some mx ->  n <=/ mx) then Point n else Empty
   | Itv (min1,max1) , Itv (min2,max2) -> 
      let bmin = max min1 min2
      and bmax = min max1 max2 in
       normalise bmin bmax

 (* a.x >= b*)
 let bound_of_constraint (a,b) =
  match compare_num a (Int 0) with
   | 0 -> 
      if compare_num b (Int 0) = 1
      then Empty  
       (*actually this is a contradiction  failwith "bound_of_constraint" *)
      else Itv (None,None)
   | 1 -> Itv (Some (div_num  b a),None)
   | -1 -> Itv (None, Some (div_num  b a))
   | x -> failwith "bound_of_constraint(2)"


 let bounded x = 
  match x with
   | Itv(None,_) | Itv(_,None) -> false
   |   _   -> true


 let range = function
  | Empty -> Some (Int 0)
  | Point n -> Some (Int (if ceiling_num n =/ n then 1 else 0))
  | Itv(None,_) | Itv(_,None)-> None
  | Itv(Some i,Some j) -> Some (floor_num j -/ceiling_num i +/ (Int 1))

 (* Returns the interval of smallest range *)
 let smaller_itv i1 i2 = 
  match range i1 , range i2  with
   | None , _ -> false
   |  _   , None -> true
   | Some i , Some j -> i <=/ j

end
open Interval

(* A set of constraints *)
module Sys(V:Vector.S) (* : Vector.SystemS with module Vect = V*) = 
struct
 
 module Vect = V
  
 module Cstr = Vector.Cstr(V)
 open Cstr
 
 
 module CMap = Map.Make(
  struct
   type t = Vect.t
   let compare = Vect.compare
  end)
  
 module CstrBag = 
 struct 

  type mut_itv = { mutable itv : intrvl} 

  type t = mut_itv CMap.t
    
  exception Contradiction

  let cstr_to_itv cstr = 
   let (n,l) = V.normalise cstr.coeffs in 
    if n =/ (Int 0)
    then (Vect.null, bound_of_constraint (Int 0,cstr.cst)) (* Might be empty *)
    else
     match cstr.op with
      | Eq -> let n = cstr.cst // n in (l, Point n)
      | Ge -> 
	 match  compare_num n (Int 0) with
	  | 0 -> failwith "intrvl_of_constraint"
	  | 1 -> (l,Itv (Some (cstr.cst // n), None))
	  | -1 -> (l, Itv(None,Some (cstr.cst // n)))
	  |  _ -> failwith "cstr_to_itv"

	      
  let empty = CMap.empty




  let is_empty = CMap.is_empty

  let find_vect v bag = 
   try
    (bag,CMap.find v bag) 
   with Not_found -> let x = { itv = Itv(None,None)} in (CMap.add v x bag ,x)


  let add (v,b) bag = 
   match b with
    | Empty -> raise Contradiction
    | Itv(None,None) -> bag
    | _    -> 
       let (bag,intrl) = find_vect v bag in
	match inter b intrl.itv with
	 | Empty -> raise Contradiction
	 |  itv  -> intrl.itv <- itv ; bag

  exception Found of cstr

  let find_equation bag = 
   try 
    CMap.fold (fun v i () -> 
     match i.itv with
      | Point n -> let e = {coeffs = v ; op = Eq ; cst = n} 
	in 	raise	(Found e)
      |    _    -> () ) bag () ; None
   with Found c -> Some c

    
  let fold f bag acc = 
   CMap.fold (fun v itv acc -> 
    match itv.itv with
     | Empty | Itv(None,None)  -> failwith "fold Empty"
     | Itv(None ,Some i) -> 
	f {coeffs = V.mul (Int (-1)) v ; op = Ge ; cst = minus_num i} acc
     | Point n           ->   f {coeffs =  v ; op = Eq ; cst = n} acc
     | Itv(x,y) -> 	
	(match x with 
	 | None -> (fun x -> x)
	 | Some i -> f {coeffs = v ; op = Ge ; cst = i})
	 (match y with
	  | None -> acc
	  | Some i -> 
	     f {coeffs = V.mul (Int (-1)) v ; op = Ge ; cst = minus_num i} acc
	 ) ) bag acc


  let remove l _ = failwith "remove:Not implemented"
   
  module Map = 
   Map.Make(
    struct 
     type t = int 
     let compare : int -> int -> int = Pervasives.compare 
    end)

  let split f (t:t) =
   let res = 
    fold (fun e m -> let i = f e in
                      Map.add i (add (cstr_to_itv e) 
				  (try Map.find i m with 
				    Not_found -> empty)) m) t Map.empty in
    (fun i -> try Map.find i res with Not_found -> empty)
     
  type map = (int list * int list) Map.t
    
    
  let status (b:t) = 
   let _ , map = fold (fun c ( (idx:int),(res: map)) ->
    ( idx + 1,
    List.fold_left (fun (res:map) (pos,s) -> 
     let (lp,ln) = try  Map.find pos res with Not_found -> ([],[]) in
      match s with
       | Vect.Pos -> Map.add pos (idx::lp,ln) res
       | Vect.Neg -> 
	  Map.add pos (lp, idx::ln) res) res 
     (Vect.status c.coeffs))) b (0,Map.empty) in
    Map.fold (fun k e res -> (k,e)::res)  map []
     

  type it = num CMap.t
    
  let iterator x = x
   
  let element it = failwith "element:Not implemented"

 end
end

module Fourier(Vect : Vector.S)  =
struct
 module Vect = Vect
 module Sys = Sys( Vect)
 module Cstr = Sys.Cstr
 module Bag = Sys.CstrBag

 open Cstr
 open Sys

 let debug = false

 let print_bag msg b =
  print_endline msg;
  CstrBag.fold (fun e () -> print_endline (Cstr.string_of_cstr e)) b () 

 let print_bag_file file msg b =
  let f = open_out file in
   output_string f msg;
   CstrBag.fold (fun e () -> 
    Printf.fprintf f "%s\n" (Cstr.string_of_cstr e)) b () 

    
 (* A system with only inequations --
 *)
 let partition i m =
  let splitter cstr =  compare_num (Vect.get i cstr.coeffs ) (Int 0) in
  let split = CstrBag.split splitter m in
   (split (-1) , split 0, split 1)

    
 (* op of the result is arbitrary Ge *) 
 let lin_comb n1 c1 n2 c2 =
  { coeffs = Vect.lin_comb n1 c1.coeffs n2 c2.coeffs ; 
    op = Ge ; 
    cst = (n1 */ c1.cst) +/ (n2 */ c2.cst)}

 (* BUG? : operator of the result ? *)

 let combine_project i c1 c2 =
  let p = Vect.get  i c1.coeffs  
  and n = Vect.get i c2.coeffs  in 
   assert (n </ Int 0 && p >/ Int 0) ;
   let nopp = minus_num n in 
   let c =lin_comb nopp c1 p c2  in
   let op = if c1.op = Ge ||  c2.op = Ge then Ge else Eq in
    CstrBag.cstr_to_itv {coeffs =  c.coeffs ; op = op ; cst= c.cst }


 let project i m =
  let (neg,zero,pos) = partition i m in
  let project1 cpos acc = 
   CstrBag.fold (fun cneg res ->
    CstrBag.add (combine_project i cpos cneg) res) neg acc in
   (CstrBag.fold project1 pos zero)

 (* Given a vector [x1 -> v1; ... ; xn -> vn]
    and a constraint {x1 ; .... xn >= c }
 *)
 let evaluate_constraint i map cstr =
  let {coeffs = _coeffs ; op = _op ; cst = _cst} = cstr in
  let vi = Vect.get  i _coeffs  in
  let v = Vect.set i (Int 0) _coeffs in
   (vi, _cst -/ Vect.dotp map v)


 let rec bounds m itv =
  match m with
   | [] -> itv
   | e::m -> bounds m (inter itv (bound_of_constraint e))



 let compare_status (i,(lp,ln)) (i',(lp',ln')) = 
  let cmp = Pervasives.compare 
   ((List.length lp) * (List.length ln))  
   ((List.length lp') * (List.length ln')) in
   if cmp = 0
   then Pervasives.compare i i'
   else cmp

 let cardinal m = CstrBag.fold (fun _ x -> x + 1) m 0

 let lightest_projection  l c m  =
  let bound = c in 
   if debug then (Printf.printf "l%i" bound; flush stdout) ; 
   let rec xlight best l =
    match l with
     | [] -> best
     | i::l -> 
	let proj = (project i m) in
	let cproj = cardinal proj in
	 (*Printf.printf " p %i " cproj; flush stdout;*)
	 match best with
	  | None -> 
	     if cproj < bound 
	     then Some(cproj,proj,i) 
	     else xlight (Some(cproj,proj,i)) l
	  | Some (cbest,_,_) -> 		
	     if cproj < cbest 
	     then 
	      if cproj < bound then Some(cproj,proj,i)
	      else xlight (Some(cproj,proj,i)) l 
	     else xlight best l in
    match xlight None l with
     | None -> None
     | Some(_,p,i) -> Some (p,i)
	


 exception Equality of cstr

 let find_equality m = Bag.find_equation m

  

 let pivot (n,v) eq ge =
  assert (eq.op = Eq) ;
  let res = 
   match 
    compare_num v (Int 0), 
    compare_num (Vect.get n ge.coeffs) (Int 0) 
   with
    | 0 , _ -> failwith "Buggy"
    | _ ,0  -> (CstrBag.cstr_to_itv ge)
    | 1 , -1 -> combine_project n eq ge
    | -1 , 1 -> combine_project n ge eq
    | 1  , 1 -> 
       combine_project n ge 
	{coeffs = Vect.mul (Int (-1)) eq.coeffs; 
	 op = eq.op ; 
	 cst = minus_num eq.cst}
    | -1 , -1 -> 
       combine_project n 
	{coeffs = Vect.mul (Int (-1)) eq.coeffs; 
	 op = eq.op ; cst = minus_num eq.cst} ge
    | _ -> failwith "pivot" in
   res

 let check_cstr v c = 
  let {coeffs = _coeffs ; op = _op ; cst = _cst} = c in
  let vl = Vect.dotp v _coeffs in
   match _op with
    | Eq -> vl =/ _cst
    | Ge -> vl >= _cst


 let forall p  sys = 
  try 
   CstrBag.fold (fun c () -> if p c then () else raise Not_found) sys (); true
  with Not_found -> false


 let check_sys v sys = forall (check_cstr v) sys

 let check_null_cstr c = 
  let {coeffs = _coeffs ; op = _op ; cst = _cst} = c in
   match _op with
    | Eq -> (Int 0) =/ _cst
    | Ge -> (Int 0) >= _cst
       
 let check_null sys = forall check_null_cstr sys


 let optimise_ge 
   quick_check choose choose_idx return_empty return_ge return_eq  m =
  let c = cardinal m in
  let bound =  2 * c  in
   if debug then (Printf.printf "optimise_ge: %i\n" c; flush stdout);

   let rec xoptimise  m =
    if debug then (Printf.printf "x%i" (cardinal m) ; flush stdout);
    if debug then (print_bag "xoptimise" m ; flush stdout);
    if quick_check m
    then return_empty m
    else 
     match find_equality m with
      | None -> xoptimise_ge m
      | Some eq -> xoptimise_eq eq m
	 
   and xoptimise_ge m =
    begin
     let c = cardinal m in
     let l = List.map fst (List.sort compare_status (CstrBag.status m)) in
     let  idx = choose bound l c m in
      match idx with
       | None -> return_empty m
       | Some (proj,i) -> 
	  match xoptimise proj with
	   | None -> None
	   | Some mapping -> return_ge m i mapping
    end
   and xoptimise_eq eq m = 
    let l = List.map fst (Vect.status eq.coeffs) in
     match choose_idx l with
      | None -> (*if l = [] then None else*) return_empty m
      | Some i -> 
	 let p  = (i,Vect.get i eq.coeffs) in
	 let m' = CstrBag.fold 
	  (fun ge res -> CstrBag.add (pivot p eq ge) res) m CstrBag.empty in
	  match xoptimise ( m') with
	   | None -> None
	   | Some mapp -> return_eq m eq i mapp in
    try 
     let res = xoptimise   m  in res
    with CstrBag.Contradiction -> (*print_string "contradiction" ;*) None



 let minimise m = 
  let opt_zero_choose bound l c m = 
   if c > bound 
   then lightest_projection l c m
   else match l with
    | [] -> None
    | i::_ -> Some (project i m, i) in
   
  let choose_idx = function [] -> None | x::l -> Some x in

  let opt_zero_return_empty m = Some Vect.null in

   
  let opt_zero_return_ge m i mapping = 
   let (it:intrvl) = CstrBag.fold (fun cstr itv -> Interval.inter 
    (bound_of_constraint (evaluate_constraint i mapping cstr)) itv) m 
    (Itv (None, None)) in
    match pick_closed_to_zero it with
     | None -> print_endline "Cannot pick" ; None
     | Some v -> 
	let res =  (Vect.set i v mapping) in
	 if debug 
	 then Printf.printf "xoptimise res %i [%s]" i (Vect.string res) ;
	 Some res in

  let opt_zero_return_eq m eq i mapp = 
   let (a,b) = evaluate_constraint i mapp eq in
    Some (Vect.set i (div_num b a) mapp) in
   
   optimise_ge check_null opt_zero_choose 
    choose_idx opt_zero_return_empty opt_zero_return_ge opt_zero_return_eq   m

 let normalise cstr = [CstrBag.cstr_to_itv cstr]

 let find_point l = 
  (*  List.iter (fun e -> print_endline (Cstr.string_of_cstr e)) l;*)
  try 
   let m = List.fold_left (fun sys e -> CstrBag.add (CstrBag.cstr_to_itv e) sys) 
    CstrBag.empty l in
    match minimise m with
     | None -> None
     | Some res -> 
	if debug then Printf.printf "[%s]"  (Vect.string res); 
	Some res
  with CstrBag.Contradiction -> None


 let find_q_interval_for x m = 
  if debug then Printf.printf "find_q_interval_for %i\n" x ;

  let choose bound l c m =
   let rec xchoose l = 
    match l with
     | [] -> None
     | i::l -> if i = x then xchoose l else Some (project i m,i) in
    xchoose l in

  let rec choose_idx = function 
    [] -> None 
   | e::l -> if e = x then choose_idx l else Some e in

  let return_empty m = (* Beurk *)
   (* returns the interval of x *)
   Some (CstrBag.fold (fun cstr itv -> 
    let i = if cstr.op = Eq 
    then Point (cstr.cst // Vect.get x cstr.coeffs)  
     else if Vect.is_null (Vect.set x (Int 0) cstr.coeffs) 
     then  bound_of_constraint (Vect.get x cstr.coeffs  , cstr.cst) 
     else itv
   in
		       Interval.inter i itv) m (Itv (None, None)))  in
   
  let return_ge m i res = Some res in

  let return_eq m eq i res = Some res in

   try 
    optimise_ge 
     (fun x -> false) choose choose_idx return_empty return_ge return_eq m
   with CstrBag.Contradiction -> None


 let find_q_intervals sys =
  let variables =  
   List.map fst (List.sort compare_status (CstrBag.status sys)) in
   List.map (fun x -> (x,find_q_interval_for x sys)) variables

 let pp_option f o = function 
   None -> Printf.fprintf o "None" 
  | Some x -> Printf.fprintf o "Some %a" f x

 let optimise vect sys = 
  (* we have to modify the system with a dummy variable *)
  let fresh = 
   List.fold_left (fun fr c -> Pervasives.max fr (Vect.fresh c.coeffs)) 0 sys in
   assert (List.for_all (fun x -> Vect.get fresh x.coeffs =/ Int 0) sys);
   let cstr = {
    coeffs = Vect.set fresh (Int (-1)) vect ; 
    op = Eq ; 
    cst = (Int 0)} in
    try 
     find_q_interval_for fresh 
      (List.fold_left 
	(fun bg c -> CstrBag.add (CstrBag.cstr_to_itv c) bg)  
	CstrBag.empty (cstr::sys))
    with CstrBag.Contradiction -> None


 let optimise vect sys = 
  let res = optimise vect sys in 
   if debug 
   then Printf.printf "optimise %s -> %a\n" 
    (Vect.string vect) (pp_option (fun o x -> Printf.printf "%s" (string_of_intrvl x))) res  
   ; res

 let find_Q_interval sys = 
  try 
   let sys = 
    (List.fold_left 
      (fun bg c -> CstrBag.add (CstrBag.cstr_to_itv c) bg)  CstrBag.empty sys) in
   let candidates = 
    List.fold_left 
     (fun l (x,i) -> match i with 
       None -> (x,Empty)::l 
      | Some i ->  (x,i)::l) [] (find_q_intervals sys) in
    match List.fold_left 
     (fun (x1,i1) (x2,i2) -> 
      if smaller_itv i1 i2 
      then (x1,i1) else (x2,i2)) (-1,Itv(None,None)) candidates 
    with
     | (i,Empty) -> None
     | (x,Itv(Some i, Some j))  -> Some(i,x,j)
     | (x,Point n) -> Some(n,x,n)
     |   _        -> None
  with CstrBag.Contradiction -> None


end

