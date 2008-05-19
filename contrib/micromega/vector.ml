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

open Num

module type S =
sig
 type t 

 val fresh : t -> int

 val null : t

 val is_null : t -> bool

 val get : int -> t -> num

 val update : int -> (num -> num) -> t -> t
  (* behaviour is undef if index < 0 -- might loop*)

 val set : int -> num -> t -> t

 (* 
    For efficiency...

    val get_update : int -> (num -> num) -> t -> num * t  
 *)

 val mul : num -> t -> t

 val uminus : t -> t

 val add : t -> t -> t

 val dotp : t -> t -> num

 val lin_comb : num -> t -> num -> t -> t
  (* lin_comb n1 t1 n2 t2 = (n1 * t1) + (n2 * t2) *)

 val gcd : t -> Big_int.big_int

 val normalise : t -> num * t 

 val hash : t -> int

 val compare : t -> t -> int 

 type it 

 val iterator : t -> it
 val element : it -> (num*it) option

 val string : t -> string

 type status = Pos | Neg

 (* the result list is ordered by fst *)
 val status : t -> (int * status) list 

 val from_list : num list -> t
 val to_list : t -> num list

end


module type SystemS = 
sig
 
 module Vect : S

 module  Cstr :
 sig
  type kind = Eq | Ge
  val string_of_kind : kind -> string
  type cstr = {coeffs : Vect.t ; op : kind ; cst : num} 
  val  string_of_cstr : cstr -> string
  val compare : cstr -> cstr -> int
 end
 open Cstr


 module CstrBag : 
 sig 
  type t
  exception Contradiction

  val empty : t

  val is_empty : t -> bool

  val add : cstr -> t -> t
   (* c can be deduced from add c t *)

  val find : (cstr -> bool) -> t  ->  cstr option

  val fold : (cstr -> 'a -> 'a) -> t -> 'a -> 'a

  val status : t ->  (int * (int list * int list)) list
   (* aggregate of vector statuses *)

  val remove : cstr -> t -> t

  (* remove_list the ith element -- it is the ith element visited by 'fold' *)

  val split : (cstr -> int) -> t -> (int ->  t)

  type it 
  val iterator : t -> it
  val element : it -> (cstr*it) option

 end

end

let zero_num = Int 0
let unit_num = Int 1




module Cstr(V:S) = 
struct 
 type kind = Eq | Ge
 let string_of_kind = function Eq -> "Eq" | Ge -> "Ge"

 type cstr = {coeffs : V.t ; op : kind ; cst : num} 

 let string_of_cstr  {coeffs =a  ; op = b ; cst =c} =
  Printf.sprintf "{coeffs = %s;op=%s;cst=%s}" (V.string a) (string_of_kind b) (string_of_num c)

 type t = cstr
 let compare 
   {coeffs = v1 ; op = op1 ; cst = c1}
   {coeffs = v2 ; op = op2 ; cst = c2} =
  Mutils.Cmp.compare_lexical [
   (fun () -> V.compare v1 v2);
   (fun () -> Pervasives.compare op1 op2);
   (fun () -> compare_num c1 c2)
  ]


end



module VList : S with type t = num list =
struct
 type t =  num list

 let fresh l = failwith "not implemented"

 let null = []

 let is_null  = List.for_all ((=/) zero_num) 

 let normalise l = failwith "Not implemented"
  (*match l with (* Buggy : What if the first num is zero! *)
    | [] -> (Int 0,[])
    | [n] -> (n,[Int 1])
    | n::l -> (n, (Int 1) :: List.map (fun x -> x // n) l)
  *)


 let get i l = try List.nth l i with _ -> zero_num

 (* This is not tail-recursive *)
 let rec update i f t =
  match t with
   | []   -> if i = 0 then [f zero_num] else (zero_num)::(update (i-1) f [])
   | e::t -> if i = 0 then (f e)::t else e::(update (i-1) f t)

 let rec set i n t =
  match t with
   | []   -> if i = 0 then [n] else (zero_num)::(set (i-1) n [])
   | e::t -> if i = 0 then (n)::t else e::(set (i-1) n t)




 let rec mul z t = 
  match z with
   | Int 0 -> null
   | Int 1 -> t
   |  _    -> List.map (mult_num z) t

 let uminus t = mul (Int (-1)) t

 let rec add t1 t2 =
  match t1,t2 with
   | [], _  -> t2
   | _ , [] -> t1
   | e1::t1,e2::t2 -> (e1 +/ e2 )::(add t1 t2)

 let dotp t1 t2 =
  let rec _dotp t1 t2 acc = 
   match t1, t2 with
    | [] , _  -> acc
    | _  , [] -> acc
    | e1::t1,e2::t2 -> _dotp t1 t2 (acc +/ (e1 */ e2)) in
   _dotp t1 t2 zero_num

 let add_mul n t1 t2 =
  match n with
   | Int 0 -> t2
   | Int 1  -> add t1 t2
   |  _     -> 
       let rec _add_mul t1 t2 = 
	match t1,t2 with
	 | [], _  -> t2
	 | _ , [] -> mul n t1
	 | e1::t1,e2::t2 -> ( (n */e1) +/ e2 )::(_add_mul t1 t2) in
	_add_mul t1 t2

 let lin_comb n1 t1 n2 t2 = 
  match n1,n2 with
   | Int 0 , _  -> mul n2 t2
   | Int 1 , _ -> add_mul n2 t2 t1
   |   _   , Int 0 ->  mul n1 t1
   |   _   , Int 1 -> add_mul n1 t1 t2  
   |       _       -> 
	    let rec _lin_comb t1 t2 = 
	     match t1,t2 with
	      | [], _  -> mul n2 t2
	      | _ , [] -> mul n1 t1
	      | e1::t1,e2::t2 -> ( (n1 */e1) +/ (n2 */ e2 ))::(_lin_comb t1 t2) in
	     _lin_comb t1 t2
	      
 (* could be computed on the fly *)
 let gcd  t =Mutils.gcd_list t




 let hash = Mutils.Cmp.hash_list int_of_num 

 let compare = Mutils.Cmp.compare_list compare_num

 type it = t
 let iterator (x:t) : it = x
 let element it = 
  match it with
   | [] -> None
   | e::l -> Some (e,l)

 (* TODO: Buffer! *)
 let string l = List.fold_right (fun n s -> (string_of_num n)^";"^s) l ""

 type status = Pos | Neg

 let status l =
  let rec xstatus i l = 
   match l with 
    | [] -> []
    | e::l -> 
       begin
	match compare_num e (Int 0) with
	 | 1 -> (i,Pos):: (xstatus (i+1) l)
	 | 0 -> xstatus (i+1) l
	 | -1 -> (i,Neg) :: (xstatus (i+1) l)
	 | _  -> assert false
       end in
   xstatus 0 l

 let from_list l = l
 let to_list l = l
  
end

module VMap : S =
struct
 module Map = Map.Make(struct type t = int let compare (x:int) (y:int) = Pervasives.compare x y end)

 type t =  num Map.t

 let null = Map.empty

 let fresh m = failwith "not implemented"

 let is_null  = Map.is_empty

 let normalise m = failwith "Not implemented"



 let get i l = try Map.find i l with _ -> zero_num

 let  update i f t =
  try
   let res = f (Map.find i t) in
    if res =/ zero_num
    then Map.remove i t
    else Map.add i res t
  with
    Not_found -> 
     let res = f zero_num in
      if res =/ zero_num then t else Map.add i res t

 let set i n t =
  if n =/ zero_num then Map.remove i t
  else Map.add i n t


 let rec mul z t = 
  match z with
   | Int 0 -> null
   | Int 1 -> t
   |  _    -> Map.map (mult_num z) t

 let uminus t = mul (Int (-1)) t
  

 let map2 f m1 m2 = 
  let res,m2' = 
   Map.fold (fun k e (res,m2) -> 
    let v = f e (get k m2) in
     if v =/ zero_num
     then (res,Map.remove k m2)
     else (Map.add k v res,Map.remove k m2)) m1 (Map.empty,m2) in
   Map.fold (fun k e res -> 
    let v = f zero_num e in
     if v =/ zero_num
     then res else Map.add k v res) m2' res
    
 let  add t1 t2 = map2 (+/) t1 t2
  

 let dotp t1 t2 =
  Map.fold (fun k e res -> 
   res +/ (e */ get k t2)) t1 zero_num



 let add_mul n t1 t2 =
  match n with
   | Int 0 -> t2
   | Int 1  -> add t1 t2
   |  _     -> map2 (fun x y -> (n */ x) +/ y) t1 t2

 let lin_comb n1 t1 n2 t2 = 
  match n1,n2 with
   | Int 0 , _  -> mul n2 t2
   | Int 1 , _ -> add_mul n2 t2 t1
   |   _   , Int 0 ->  mul n1 t1
   |   _   , Int 1 -> add_mul n1 t1 t2  
   |       _       -> map2 (fun x y -> (n1 */ x) +/ (n2 */ y)) t1 t2


 let hash map = Map.fold (fun k e res -> k lxor (int_of_num e) lxor res) map 0

 let compare = Map.compare compare_num

 type it = t * int

 let iterator (x:t) : it = (x,0)
  
 let element (mp,id) = 
  try 
   Some (Map.find id mp, (mp, id+1))
  with
    Not_found -> None

 (* TODO: Buffer! *)
 type status = Pos | Neg

 let status l = Map.fold (fun k e l -> 
  match compare_num e (Int 0) with
   | 1 -> (k,Pos)::l
   | 0 ->  l
   | -1 -> (k,Neg) :: l
   | _  -> assert false) l []
 let from_list l = 
  let rec from_list i l map = 
   match l with
    | [] -> map
    | e::l -> from_list (i+1) l (if e <>/ Int 0 then Map.add i e map else map) in
   from_list 0 l Map.empty

 let gcd m = 
  let res = Map.fold (fun _ e x -> Big_int.gcd_big_int  x (Mutils.numerator e)) m Big_int.zero_big_int in
   if Big_int.compare_big_int res Big_int.zero_big_int = 0 
   then Big_int.unit_big_int else res


 let to_list m = 
  let l = List.rev (Map.fold (fun k e l -> (k,e)::l) m []) in
  let rec xto_list i l =
   match l with
    | [] -> []
    |	(x,v)::l' -> if i = x then v::(xto_list (i+1) l') else zero_num ::(xto_list (i+1) l) in
   xto_list 0 l

 let string l = VList.string (to_list l)

  
end


module VSparse : S =
struct

 type t = (int*num) list

 let null = []
  
 let fresh l = List.fold_left (fun acc (i,_) -> max (i+1) acc)  0 l

 let is_null l = l = []
  
 let rec is_sorted l =
  match l with
   |	[] -> true
   | [e] -> true
   | (i,_)::(j,x)::l -> i < j && is_sorted ((j,x)::l)
      
      
 let check l = (List.for_all (fun (_,n) -> compare_num n (Int 0) <> 0) l) && (is_sorted l)
  
 (*	let get i t = 
	assert (check t);
	try List.assoc i t with Not_found -> zero_num *)

 let rec get (i:int) t = 
  match t with
   | [] -> zero_num
   | (j,n)::t -> 
      match compare i j with
       | 0 -> n
       | 1 -> get i t
       |  _ -> zero_num

 let cons i v rst = if v =/ Int 0 then rst else (i,v)::rst
   
 let rec update i f t = 
  match t with
   | [] -> cons i (f zero_num) []
   | (k,v)::l -> 
      match Pervasives.compare i k with
       | 0 -> cons k (f v) l
       | -1 -> cons i (f zero_num) t
       |  1 -> (k,v) ::(update i f l)
       |  _  -> failwith "compare_num"
	   
 let update i f t =
  assert (check t); 
  let res = update i f t in
   assert (check t) ; res
    
    
 let rec set i n t =
  match t with
   | [] -> cons i n []
   | (k,v)::l -> 
      match Pervasives.compare i k with
       | 0 -> cons k n l
       | -1 -> cons i n t
       |  1 -> (k,v) :: (set i n l)
       |  _  -> failwith "compare_num"
	   

 let rec map f l = 
  match l with
   | [] -> []
   | (i,e)::l -> cons i (f e) (map f l)
      
 let rec mul z t = 
  match z with
   | Int 0 -> null
   | Int 1 -> t
   |  _    -> List.map (fun (i,n) -> (i, mult_num z n)) t
       
 let mul z t = 
  assert (check t) ;
  let res = mul z t in
   assert (check res) ; 
   res

 let uminus t = mul (Int (-1)) t


 let normalise l = 
  match l with
   | []   -> (Int 0,[])
   | (i,n)::_ -> (n, mul ((Int 1) // n) l)
      

 let rec map2 f m1 m2 = 
  match m1, m2 with
   | [] , [] -> []
   | l  , [] -> map (fun x -> f x zero_num) l
   | [] ,l   -> map (f zero_num) l
   | (i,e)::l1,(i',e')::l2 -> 
      match Pervasives.compare i i' with
       | 0 -> cons i (f e e') (map2 f l1 l2)
       | -1 -> cons i (f e zero_num) (map2 f l1 m2)
       |  1 -> cons i' (f zero_num e') (map2 f m1 l2)
       | _  -> assert false
	  
 (* let  add t1 t2 = map2 (+/) t1 t2*)

 let rec add (m1:t) (m2:t) = 
  match m1, m2 with
   | [] , [] -> []
   | l  , [] -> l
   | [] ,l   -> l
   | (i,e)::l1,(i',e')::l2 -> 
      match Pervasives.compare i i' with
       | 0 -> cons i ( e +/ e') (add  l1 l2)
       | -1 -> (i,e) :: (add l1 m2)
       |  1 -> (i', e') :: (add m1 l2)
       | _  -> assert false




 let add t1 t2 = 
  assert (check t1 && check t2);
  let res = add t1 t2 in
   assert (check res);
   res


 let rec dotp (t1:t) (t2:t) =
  match t1, t2 with
   | [] , _ -> zero_num
   | _  , [] -> zero_num
   | (i,e)::l1 , (i',e')::l2 -> 
      match Pervasives.compare i i' with
       | 0 -> (e */ e') +/ (dotp l1 l2)
       | -1 -> dotp l1 t2
       |  1 -> dotp t1 l2
       |  _ -> assert false
	   
 let dotp t1 t2 = 
  assert (check t1 && check t2) ; dotp t1 t2

 let add_mul n t1 t2 =
  match n with
   | Int 0 -> t2
   | Int 1  -> add t1 t2
   |  _     -> map2 (fun x y -> (n */ x) +/ y) t1 t2

 let add_mul n (t1:t) (t2:t) =
  match n with
   | Int 0 -> t2
   | Int 1  -> add t1 t2
   |   _    -> 
	let rec xadd_mul m1 m2 = 
	 match m1, m2 with
	  | [] , [] -> []
	  | _  , [] -> mul n m1
	  | [] , _   -> m2
	  | (i,e)::l1,(i',e')::l2 -> 
	     match Pervasives.compare i i' with
	      | 0 -> cons i ( n */ e +/ e') (xadd_mul  l1 l2)
	      | -1 -> (i,n */ e) :: (xadd_mul l1 m2)
	      |  1 -> (i', e') :: (xadd_mul m1 l2)
	      | _  -> assert false in
	 xadd_mul t1 t2
	  



 let lin_comb n1 t1 n2 t2 = 
  match n1,n2 with
   | Int 0 , _  -> mul n2 t2
   | Int 1 , _ -> add_mul n2 t2 t1
   |   _   , Int 0 ->  mul n1 t1
   |   _   , Int 1 -> add_mul n1 t1 t2  
   |       _       -> (*map2 (fun x y -> (n1 */ x) +/ (n2 */ y)) t1 t2*)
	    let rec xlin_comb m1 m2 = 
	     match m1, m2 with
	      | [] , [] -> []
	      | _  , [] -> mul n1 m1
	      | [] , _   -> mul n2 m2
	      | (i,e)::l1,(i',e')::l2 -> 
		 match Pervasives.compare i i' with
		  | 0 -> cons i ( n1 */ e +/ n2 */ e') (xlin_comb  l1 l2)
		  | -1 -> (i,n1 */ e) :: (xlin_comb l1 m2)
		  |  1 -> (i', n2 */ e') :: (xlin_comb m1 l2)
		  | _  -> assert false in
	     xlin_comb t1 t2





 let lin_comb n1 t1 n2 t2 = 
  assert (check t1 && check t2);
  let res = lin_comb n1 t1 n2 t2 in
   assert (check res); res

 let hash = Mutils.Cmp.hash_list (fun (x,y) -> (Hashtbl.hash x) lxor (int_of_num y))


 let compare = Mutils.Cmp.compare_list (fun x y -> Mutils.Cmp.compare_lexical 
  [
   (fun () -> Pervasives.compare (fst x) (fst y));
   (fun () -> compare_num (snd x) (snd y))]) 

 (* 
    let compare (x:t) (y:t) = 
    let rec xcompare acc1 acc2 x y = 
    match x , y with
    | [] , [] -> xcomp acc1 acc2
    | [] , _  -> -1
    |  _ , [] -> 1
    | (i,n1)::l1 , (j,n2)::l2 -> 
    match Pervasives.compare i j with
    | 0 -> xcompare (n1::acc1) (n2::acc2) l1 l2
    | c -> c
    and xcomp acc1 acc2 = Mutils.Cmp.compare_list compare_num acc1 acc2 in
    xcompare [] [] x y
 *)

 type it = t

 let iterator (x:t) : it =  x
  
 let element l = failwith "Not_implemented"

 (* TODO: Buffer! *)
 type status = Pos | Neg

 let status l = List.map (fun (i,e) -> 
  match compare_num e (Int 0) with
   | 1 -> i,Pos
   | -1 -> i,Neg
   | _  -> assert false) l

 let from_list (l: num list) = 
  let rec xfrom_list i l = 
   match l with
    | [] -> []
    | e::l ->  
       if e <>/ Int 0 
       then (i,e)::(xfrom_list (i+1) l)
       else xfrom_list (i+1) l in
   
  let res = xfrom_list 0 l in
   assert (check res) ; res


 let gcd m = 
  let res = List.fold_left (fun x (i,e) -> Big_int.gcd_big_int  x (Mutils.numerator e))  Big_int.zero_big_int m in
   if Big_int.compare_big_int res Big_int.zero_big_int = 0 
   then Big_int.unit_big_int else res

 let to_list m = 
  let rec xto_list i l =
   match l with
    | [] -> []
    |	(x,v)::l' -> 
	 if i = x then v::(xto_list (i+1) l') else zero_num ::(xto_list (i+1) l) in
   xto_list 0 m

 let to_list l =
  assert (check l); 
  to_list l


 let string l = VList.string (to_list l)
  
end
