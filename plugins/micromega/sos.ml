(* ========================================================================= *)
(* - This code originates from John Harrison's HOL LIGHT 2.20                *)
(*   (see file LICENSE.sos for license, copyright and disclaimer)            *)
(* - Laurent Théry (thery@sophia.inria.fr) has isolated the HOL              *)
(*   independent bits                                                        *)
(* - Frédéric Besson (fbesson@irisa.fr) is using it to feed  micromega       *)
(* - Addition of a csdp cache by the Coq development team                    *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Nonlinear universal reals procedure using SOS decomposition.              *)
(* ========================================================================= *)

open Num;;
open List;;

let debugging = ref false;;

exception Sanity;;

exception Unsolvable;;

(* ------------------------------------------------------------------------- *)
(* Comparisons that are reflexive on NaN and also short-circuiting.          *)
(* ------------------------------------------------------------------------- *)

let (=?) = fun x y -> Pervasives.compare x y = 0;;
let (<?) = fun x y -> Pervasives.compare x y < 0;;
let (<=?) = fun x y -> Pervasives.compare x y <= 0;;
let (>?) = fun x y -> Pervasives.compare x y > 0;;
let (>=?) = fun x y -> Pervasives.compare x y >= 0;;

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

let (o) = fun f g x -> f(g x);;

(* ------------------------------------------------------------------------- *)
(* Some useful functions on "num" type.                                      *)
(* ------------------------------------------------------------------------- *)


let num_0 = Int 0
and num_1 = Int 1
and num_2 = Int 2
and num_10 = Int 10;;

let pow2 n = power_num num_2 (Int n);;
let pow10 n = power_num num_10 (Int n);;

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r');;

let numerator = (o) fst numdom
and denominator = (o) snd numdom;;

let gcd_num n1 n2 =
  num_of_big_int(Big_int.gcd_big_int (big_int_of_num n1) (big_int_of_num n2));;

let lcm_num x y =
  if x =/ num_0 & y =/ num_0 then num_0
  else abs_num((x */ y) // gcd_num x y);;


(* ------------------------------------------------------------------------- *)
(* List basics.                                                              *)
(* ------------------------------------------------------------------------- *)

let rec el n l =
  if n = 0 then hd l else el (n - 1) (tl l);;


(* ------------------------------------------------------------------------- *)
(* Various versions of list iteration.                                       *)
(* ------------------------------------------------------------------------- *)

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec end_itlist f l =
  match l with
        []     -> failwith "end_itlist"
      | [x]    -> x
      | (h::t) -> f h (end_itlist f t);;

let rec itlist2 f l1 l2 b =
  match (l1,l2) with
    ([],[]) -> b
  | (h1::t1,h2::t2) -> f h1 h2 (itlist2 f t1 t2 b)
  | _ -> failwith "itlist2";;

(* ------------------------------------------------------------------------- *)
(* All pairs arising from applying a function over two lists.                *)
(* ------------------------------------------------------------------------- *)

let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;

(* ------------------------------------------------------------------------- *)
(* String operations (surely there is a better way...)                       *)
(* ------------------------------------------------------------------------- *)

let implode l = itlist (^) l "";;

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.sub s n 1)::l) in
  exap (String.length s - 1) [];;


(* ------------------------------------------------------------------------- *)
(* Attempting function or predicate applications.                            *)
(* ------------------------------------------------------------------------- *)

let can f x = try (f x; true) with Failure _ -> false;;


(* ------------------------------------------------------------------------- *)
(* Repetition of a function.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;


(* ------------------------------------------------------------------------- *)
(*  term??                                                                   *)
(* ------------------------------------------------------------------------- *)

type vname = string;;

type term =
| Zero
| Const of Num.num
| Var of vname
| Inv of term
| Opp of term
| Add of (term * term)
| Sub of (term * term)
| Mul of (term * term)
| Div of (term * term)
| Pow of (term * int);;


(* ------------------------------------------------------------------------- *)
(* Data structure for Positivstellensatz refutations.                        *)
(* ------------------------------------------------------------------------- *)

type positivstellensatz =
   Axiom_eq of int
 | Axiom_le of int
 | Axiom_lt of int
 | Rational_eq of num
 | Rational_le of num
 | Rational_lt of num
 | Square of term
 | Monoid of int list
 | Eqmul of term * positivstellensatz
 | Sum of positivstellensatz * positivstellensatz
 | Product of positivstellensatz * positivstellensatz;;



(* ------------------------------------------------------------------------- *)
(* Replication and sequences.                                                *)
(* ------------------------------------------------------------------------- *)

let rec replicate x n =
    if n < 1 then []
    else x::(replicate x (n - 1));;

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);;

(* ------------------------------------------------------------------------- *)
(* Various useful list operations.                                           *)
(* ------------------------------------------------------------------------- *)

let rec forall p l =
  match l with
    [] -> true
  | h::t -> p(h) & forall p t;;

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;

let index x =
  let rec ind n l =
    match l with
      [] -> failwith "index"
    | (h::t) -> if x =? h then n else ind (n + 1) t in
  ind 0;;

(* ------------------------------------------------------------------------- *)
(* "Set" operations on lists.                                                *)
(* ------------------------------------------------------------------------- *)

let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> x =? h or mem x t;;

let insert x l =
  if mem x l then l else x::l;;

let union l1 l2 = itlist insert l1 l2;;

let subtract l1 l2 = filter (fun x -> not (mem x l2)) l1;;

(* ------------------------------------------------------------------------- *)
(* Merging and bottom-up mergesort.                                          *)
(* ------------------------------------------------------------------------- *)

let rec merge ord l1 l2 =
  match l1 with
    [] -> l2
  | h1::t1 -> match l2 with
                [] -> l1
              | h2::t2 -> if ord h1 h2 then h1::(merge ord t1 l2)
                          else h2::(merge ord l1 t2);;


(* ------------------------------------------------------------------------- *)
(* Common measure predicates to use with "sort".                             *)
(* ------------------------------------------------------------------------- *)

let increasing f x y = f x <? f y;;

let decreasing f x y = f x >? f y;;

(* ------------------------------------------------------------------------- *)
(* Zipping, unzipping etc.                                                   *)
(* ------------------------------------------------------------------------- *)

let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let rec unzip =
  function [] -> [],[]
         | ((a,b)::rest) -> let alist,blist = unzip rest in
                            (a::alist,b::blist);;

(* ------------------------------------------------------------------------- *)
(* Iterating functions over lists.                                           *)
(* ------------------------------------------------------------------------- *)

let rec do_list f l =
  match l with
    [] -> ()
  | (h::t) -> (f h; do_list f t);;

(* ------------------------------------------------------------------------- *)
(* Sorting.                                                                  *)
(* ------------------------------------------------------------------------- *)

let rec sort cmp lis =
  match lis with
    [] -> []
  | piv::rest ->
      let r,l = partition (cmp piv) rest in
      (sort cmp l) @ (piv::(sort cmp r));;

(* ------------------------------------------------------------------------- *)
(* Removing adjacent (NB!) equal elements from list.                         *)
(* ------------------------------------------------------------------------- *)

let rec uniq l =
  match l with
    x::(y::_ as t) -> let t' = uniq t in
                      if x =? y then t' else
                      if t'==t then l else x::t'
 | _ -> l;;

(* ------------------------------------------------------------------------- *)
(* Convert list into set by eliminating duplicates.                          *)
(* ------------------------------------------------------------------------- *)

let setify s = uniq (sort (<=?) s);;

(* ------------------------------------------------------------------------- *)
(* Polymorphic finite partial functions via Patricia trees.                  *)
(*                                                                           *)
(* The point of this strange representation is that it is canonical (equal   *)
(* functions have the same encoding) yet reasonably efficient on average.    *)
(*                                                                           *)
(* Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        *)
(* ------------------------------------------------------------------------- *)

type ('a,'b)func =
   Empty
 | Leaf of int * ('a*'b)list
 | Branch of int * int * ('a,'b)func * ('a,'b)func;;

(* ------------------------------------------------------------------------- *)
(* Undefined function.                                                       *)
(* ------------------------------------------------------------------------- *)

let undefined = Empty;;

(* ------------------------------------------------------------------------- *)
(* In case of equality comparison worries, better use this.                  *)
(* ------------------------------------------------------------------------- *)

let is_undefined f =
  match f with
    Empty -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Operation analagous to "map" for lists.                                   *)
(* ------------------------------------------------------------------------- *)

let mapf =
  let rec map_list f l =
    match l with
      [] -> []
    | (x,y)::t -> (x,f(y))::(map_list f t) in
  let rec mapf f t =
    match t with
      Empty -> Empty
    | Leaf(h,l) -> Leaf(h,map_list f l)
    | Branch(p,b,l,r) -> Branch(p,b,mapf f l,mapf f r) in
  mapf;;

(* ------------------------------------------------------------------------- *)
(* Operations analogous to "fold" for lists.                                 *)
(* ------------------------------------------------------------------------- *)

let foldl =
  let rec foldl_list f a l =
    match l with
      [] -> a
    | (x,y)::t -> foldl_list f (f a x y) t in
  let rec foldl f a t =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldl_list f a l
    | Branch(p,b,l,r) -> foldl f (foldl f a l) r in
  foldl;;

let foldr =
  let rec foldr_list f l a =
    match l with
      [] -> a
    | (x,y)::t -> f x y (foldr_list f t a) in
  let rec foldr f t a =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldr_list f l a
    | Branch(p,b,l,r) -> foldr f l (foldr f r a) in
  foldr;;

(* ------------------------------------------------------------------------- *)
(* Redefinition and combination.                                             *)
(* ------------------------------------------------------------------------- *)

let (|->),combine =
  let ldb x y = let z = x lxor y in z land (-z) in
  let newbranch p1 t1 p2 t2 =
    let b = ldb p1 p2 in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch(p,b,t1,t2)
    else Branch(p,b,t2,t1) in
  let rec define_list (x,y as xy) l =
    match l with
      (a,b as ab)::t ->
          if x =? a then xy::t
          else if x <? a then xy::l
          else ab::(define_list xy t)
    | [] -> [xy]
  and combine_list op z l1 l2 =
    match (l1,l2) with
      [],_ -> l2
    | _,[] -> l1
    | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
          if x1 <? x2 then xy1::(combine_list op z t1 l2)
          else if x2 <? x1 then xy2::(combine_list op z l1 t2) else
          let y = op y1 y2 and l = combine_list op z t1 t2 in
          if z(y) then l else (x1,y)::l in
  let (|->) x y =
    let k = Hashtbl.hash x in
    let rec upd t =
      match t with
        Empty -> Leaf (k,[x,y])
      | Leaf(h,l) ->
           if h = k then Leaf(h,define_list (x,y) l)
           else newbranch h t k (Leaf(k,[x,y]))
      | Branch(p,b,l,r) ->
          if k land (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
          else if k land b = 0 then Branch(p,b,upd l,r)
          else Branch(p,b,l,upd r) in
    upd in
  let rec combine op z t1 t2 =
    match (t1,t2) with
      Empty,_ -> t2
    | _,Empty -> t1
    | Leaf(h1,l1),Leaf(h2,l2) ->
          if h1 = h2 then
            let l = combine_list op z l1 l2 in
            if l = [] then Empty else Leaf(h1,l)
          else newbranch h1 t1 h2 t2
    | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) |
      (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              let l' = combine op z lf l in
              if is_undefined l' then r else Branch(p,b,l',r)
            else
              let r' = combine op z lf r in
              if is_undefined r' then l else Branch(p,b,l,r')
          else
            newbranch k lf p br
    | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
          if b1 < b2 then
            if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
            else if p2 land b1 = 0 then
              let l = combine op z l1 t2 in
              if is_undefined l then r1 else Branch(p1,b1,l,r1)
            else
              let r = combine op z r1 t2 in
              if is_undefined r then l1 else Branch(p1,b1,l1,r)
          else if b2 < b1 then
            if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
            else if p1 land b2 = 0 then
              let l = combine op z t1 l2 in
              if is_undefined l then r2 else Branch(p2,b2,l,r2)
            else
              let r = combine op z t1 r2 in
              if is_undefined r then l2 else Branch(p2,b2,l2,r)
          else if p1 = p2 then
            let l = combine op z l1 l2 and r = combine op z r1 r2 in
            if is_undefined l then r
            else if is_undefined r then l else Branch(p1,b1,l,r)
          else
            newbranch p1 t1 p2 t2 in
  (|->),combine;;

(* ------------------------------------------------------------------------- *)
(* Special case of point function.                                           *)
(* ------------------------------------------------------------------------- *)

let (|=>) = fun x y -> (x |-> y) undefined;;


(* ------------------------------------------------------------------------- *)
(* Grab an arbitrary element.                                                *)
(* ------------------------------------------------------------------------- *)

let rec choose t =
  match t with
    Empty -> failwith "choose: completely undefined function"
  | Leaf(h,l) -> hd l
  | Branch(b,p,t1,t2) -> choose t1;;

(* ------------------------------------------------------------------------- *)
(* Application.                                                              *)
(* ------------------------------------------------------------------------- *)

let applyd =
  let rec apply_listd l d x =
    match l with
      (a,b)::t -> if x =? a then b
                  else if x >? a then apply_listd t d x else d x
    | [] -> d x in
  fun f d x ->
    let k = Hashtbl.hash x in
    let rec look t =
      match t with
        Leaf(h,l) when h = k -> apply_listd l d x
      | Branch(p,b,l,r) -> look (if k land b = 0 then l else r)
      | _ -> d x in
    look f;;

let apply f = applyd f (fun x -> failwith "apply");;

let tryapplyd f a d = applyd f (fun x -> d) a;;

let defined f x = try apply f x; true with Failure _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Undefinition.                                                             *)
(* ------------------------------------------------------------------------- *)

let undefine =
  let rec undefine_list x l =
    match l with
      (a,b as ab)::t ->
          if x =? a then t
          else if x <? a then l else
          let t' = undefine_list x t in
          if t' == t then l else ab::t'
    | [] -> [] in
  fun x ->
    let k = Hashtbl.hash x in
    let rec und t =
      match t with
        Leaf(h,l) when h = k ->
          let l' = undefine_list x l in
          if l' == l then t
          else if l' = [] then Empty
          else Leaf(h,l')
      | Branch(p,b,l,r) when k land (b - 1) = p ->
          if k land b = 0 then
            let l' = und l in
            if l' == l then t
            else if is_undefined l' then r
            else Branch(p,b,l',r)
          else
            let r' = und r in
            if r' == r then t
            else if is_undefined r' then l
            else Branch(p,b,l,r')
      | _ -> t in
    und;;


(* ------------------------------------------------------------------------- *)
(* Mapping to sorted-list representation of the graph, domain and range.     *)
(* ------------------------------------------------------------------------- *)

let graph f = setify (foldl (fun a x y -> (x,y)::a) [] f);;

let dom f = setify(foldl (fun a x y -> x::a) [] f);;

let ran f = setify(foldl (fun a x y -> y::a) [] f);;

(* ------------------------------------------------------------------------- *)
(* Turn a rational into a decimal string with d sig digits.                  *)
(* ------------------------------------------------------------------------- *)

let decimalize =
  let rec normalize y =
    if abs_num y </ Int 1 // Int 10 then normalize (Int 10 */ y) - 1
    else if abs_num y >=/ Int 1 then normalize (y // Int 10) + 1
    else 0 in
  fun d x ->
    if x =/ Int 0 then "0.0" else
    let y = abs_num x in
    let e = normalize y in
    let z = pow10(-e) */ y +/ Int 1 in
    let k = round_num(pow10 d */ z) in
    (if x </ Int 0 then "-0." else "0.") ^
    implode(tl(explode(string_of_num k))) ^
    (if e = 0 then "" else "e"^string_of_int e);;


(* ------------------------------------------------------------------------- *)
(* Iterations over numbers, and lists indexed by numbers.                    *)
(* ------------------------------------------------------------------------- *)

let rec itern k l f a =
  match l with
    [] -> a
  | h::t -> itern (k + 1) t f (f h k a);;

let rec iter (m,n) f a =
  if n < m then a
  else iter (m+1,n) f (f m a);;

(* ------------------------------------------------------------------------- *)
(* The main types.                                                           *)
(* ------------------------------------------------------------------------- *)

type vector = int*(int,num)func;;

type matrix = (int*int)*(int*int,num)func;;

type monomial = (vname,int)func;;

type poly = (monomial,num)func;;

(* ------------------------------------------------------------------------- *)
(* Assignment avoiding zeros.                                                *)
(* ------------------------------------------------------------------------- *)

let (|-->) x y a = if y =/ Int 0 then a else (x |-> y) a;;

(* ------------------------------------------------------------------------- *)
(* This can be generic.                                                      *)
(* ------------------------------------------------------------------------- *)

let element (d,v) i = tryapplyd v i (Int 0);;

let mapa f (d,v) =
  d,foldl (fun a i c -> (i |--> f(c)) a) undefined v;;

let is_zero (d,v) =
  match v with
    Empty -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Vectors. Conventionally indexed 1..n.                                     *)
(* ------------------------------------------------------------------------- *)

let vector_0 n = (n,undefined:vector);;

let dim (v:vector) = fst v;;

let vector_const c n =
  if c =/ Int 0 then vector_0 n
  else (n,itlist (fun k -> k |-> c) (1--n) undefined :vector);;

let vector_1 = vector_const (Int 1);;

let vector_cmul c (v:vector) =
  let n = dim v in
  if c =/ Int 0 then vector_0 n
  else n,mapf (fun x -> c */ x) (snd v);;

let vector_neg (v:vector) = (fst v,mapf minus_num (snd v) :vector);;

let vector_add (v1:vector) (v2:vector) =
  let m = dim v1 and n = dim v2 in
  if m <> n then failwith "vector_add: incompatible dimensions" else
  (n,combine (+/) (fun x -> x =/ Int 0) (snd v1) (snd v2) :vector);;

let vector_sub v1 v2 = vector_add v1 (vector_neg v2);;

let vector_of_list l =
  let n = length l in
  (n,itlist2 (|->) (1--n) l undefined :vector);;

(* ------------------------------------------------------------------------- *)
(* Matrices; again rows and columns indexed from 1.                          *)
(* ------------------------------------------------------------------------- *)

let matrix_0 (m,n) = ((m,n),undefined:matrix);;

let dimensions (m:matrix) = fst m;;

let matrix_const c (m,n as mn) =
  if m <> n then failwith "matrix_const: needs to be square"
  else if c =/ Int 0 then matrix_0 mn
  else (mn,itlist (fun k -> (k,k) |-> c) (1--n) undefined :matrix);;

let matrix_1 = matrix_const (Int 1);;

let matrix_cmul c (m:matrix) =
  let (i,j) = dimensions m in
  if c =/ Int 0 then matrix_0 (i,j)
  else (i,j),mapf (fun x -> c */ x) (snd m);;

let matrix_neg (m:matrix) = (dimensions m,mapf minus_num (snd m) :matrix);;

let matrix_add (m1:matrix) (m2:matrix) =
  let d1 = dimensions m1 and d2 = dimensions m2 in
  if d1 <> d2 then failwith "matrix_add: incompatible dimensions"
  else (d1,combine (+/) (fun x -> x =/ Int 0) (snd m1) (snd m2) :matrix);;

let matrix_sub m1 m2 = matrix_add m1 (matrix_neg m2);;

let row k (m:matrix) =
  let i,j = dimensions m in
  (j,
   foldl (fun a (i,j) c -> if i = k then (j |-> c) a else a) undefined (snd m)
   : vector);;

let column k (m:matrix) =
  let i,j = dimensions m in
  (i,
   foldl (fun a (i,j) c -> if j = k then (i |-> c) a else a) undefined (snd m)
   : vector);;

let transp (m:matrix) =
  let i,j = dimensions m in
  ((j,i),foldl (fun a (i,j) c -> ((j,i) |-> c) a) undefined (snd m) :matrix);;

let diagonal (v:vector) =
  let n = dim v in
  ((n,n),foldl (fun a i c -> ((i,i) |-> c) a) undefined (snd v) : matrix);;

let matrix_of_list l =
  let m = length l in
  if m = 0 then matrix_0 (0,0) else
  let n = length (hd l) in
  (m,n),itern 1 l (fun v i -> itern 1 v (fun c j -> (i,j) |-> c)) undefined;;

(* ------------------------------------------------------------------------- *)
(* Monomials.                                                                *)
(* ------------------------------------------------------------------------- *)

let monomial_eval assig (m:monomial) =
  foldl (fun a x k -> a */ power_num (apply assig x) (Int k))
        (Int 1) m;;

let monomial_1 = (undefined:monomial);;

let monomial_var x = (x |=> 1 :monomial);;

let (monomial_mul:monomial->monomial->monomial) =
  combine (+) (fun x -> false);;

let monomial_pow (m:monomial) k =
  if k = 0 then monomial_1
  else mapf (fun x -> k * x) m;;

let monomial_divides (m1:monomial) (m2:monomial) =
  foldl (fun a x k -> tryapplyd m2 x 0 >= k & a) true m1;;

let monomial_div (m1:monomial) (m2:monomial) =
  let m = combine (+) (fun x -> x = 0) m1 (mapf (fun x -> -x) m2) in
  if foldl (fun a x k -> k >= 0 & a) true m then m
  else failwith "monomial_div: non-divisible";;

let monomial_degree x (m:monomial) = tryapplyd m x 0;;

let monomial_lcm (m1:monomial) (m2:monomial) =
  (itlist (fun x -> x |-> max (monomial_degree x m1) (monomial_degree x m2))
          (union (dom m1) (dom m2)) undefined :monomial);;

let monomial_multidegree (m:monomial) = foldl (fun a x k -> k + a) 0 m;;

let monomial_variables m = dom m;;

(* ------------------------------------------------------------------------- *)
(* Polynomials.                                                              *)
(* ------------------------------------------------------------------------- *)

let eval assig (p:poly) =
  foldl (fun a m c -> a +/ c */ monomial_eval assig m) (Int 0) p;;

let poly_0 = (undefined:poly);;

let poly_isconst (p:poly) = foldl (fun a m c -> m = monomial_1 & a) true p;;

let poly_var x = ((monomial_var x) |=> Int 1 :poly);;

let poly_const c =
  if c =/ Int 0 then poly_0 else (monomial_1 |=> c);;

let poly_cmul c (p:poly) =
  if c =/ Int 0 then poly_0
  else mapf (fun x -> c */ x) p;;

let poly_neg (p:poly) = (mapf minus_num p :poly);;

let poly_add (p1:poly) (p2:poly) =
  (combine (+/) (fun x -> x =/ Int 0) p1 p2 :poly);;

let poly_sub p1 p2 = poly_add p1 (poly_neg p2);;

let poly_cmmul (c,m) (p:poly) =
  if c =/ Int 0 then poly_0
  else if m = monomial_1 then mapf (fun d -> c */ d) p
  else foldl (fun a m' d -> (monomial_mul m m' |-> c */ d) a) poly_0 p;;

let poly_mul (p1:poly) (p2:poly) =
  foldl (fun a m c -> poly_add (poly_cmmul (c,m) p2) a) poly_0 p1;;

let poly_div (p1:poly) (p2:poly) =
  if not(poly_isconst p2) then failwith "poly_div: non-constant" else
  let c = eval undefined p2 in
  if c =/ Int 0 then failwith "poly_div: division by zero"
  else poly_cmul (Int 1 // c) p1;;

let poly_square p = poly_mul p p;;

let rec poly_pow p k =
  if k = 0 then poly_const (Int 1)
  else if k = 1 then p
  else let q = poly_square(poly_pow p (k / 2)) in
       if k mod 2 = 1 then poly_mul p q else q;;

let poly_exp p1 p2 =
  if not(poly_isconst p2) then failwith "poly_exp: not a constant" else
  poly_pow p1 (Num.int_of_num (eval undefined p2));;

let degree x (p:poly) = foldl (fun a m c -> max (monomial_degree x m) a) 0 p;;

let multidegree (p:poly) =
  foldl (fun a m c -> max (monomial_multidegree m) a) 0 p;;

let poly_variables (p:poly) =
  foldr (fun m c -> union (monomial_variables m)) p [];;

(* ------------------------------------------------------------------------- *)
(* Order monomials for human presentation.                                   *)
(* ------------------------------------------------------------------------- *)

let humanorder_varpow (x1,k1) (x2,k2) = x1 < x2 or (x1 = x2 & k1 > k2);;

let humanorder_monomial =
  let rec ord l1 l2 = match (l1,l2) with
    _,[] -> true
  | [],_ -> false
  | h1::t1,h2::t2 -> humanorder_varpow h1 h2 or (h1 = h2 & ord t1 t2) in
  fun m1 m2 -> m1 = m2 or
               ord (sort humanorder_varpow (graph m1))
                   (sort humanorder_varpow (graph m2));;

(* ------------------------------------------------------------------------- *)
(* Conversions to strings.                                                   *)
(* ------------------------------------------------------------------------- *)

let string_of_vector min_size max_size (v:vector) =
  let n_raw = dim v in
  if n_raw = 0 then "[]" else
  let n = max min_size (min n_raw max_size) in
  let xs = map ((o) string_of_num (element v)) (1--n) in
  "[" ^ end_itlist (fun s t -> s ^ ", " ^ t) xs ^
  (if n_raw > max_size then ", ...]" else "]");;

let string_of_matrix max_size (m:matrix) =
  let i_raw,j_raw = dimensions m in
  let i = min max_size i_raw and j = min max_size j_raw in
  let rstr = map (fun k -> string_of_vector j j (row k m)) (1--i) in
  "["^end_itlist(fun s t -> s^";\n "^t) rstr ^
  (if j > max_size then "\n ...]" else "]");;

let string_of_vname (v:vname): string = (v: string);;

let rec string_of_term t =
  match t with
  Opp t1 -> "(- " ^ string_of_term t1 ^ ")"
| Add (t1, t2) -> 
   "(" ^ (string_of_term t1) ^ " + " ^ (string_of_term t2) ^ ")"
| Sub (t1, t2) -> 
   "(" ^ (string_of_term t1) ^ " - " ^ (string_of_term t2) ^ ")"
| Mul (t1, t2) -> 
   "(" ^ (string_of_term t1) ^ " * " ^ (string_of_term t2) ^ ")"
| Inv t1 -> "(/ " ^ string_of_term t1 ^ ")"
| Div (t1, t2) -> 
   "(" ^ (string_of_term t1) ^ " / " ^ (string_of_term t2) ^ ")"
| Pow (t1, n1) -> 
   "(" ^ (string_of_term t1) ^ " ^ " ^ (string_of_int n1) ^ ")"
| Zero -> "0"
| Var v -> "x" ^ (string_of_vname v)
| Const x -> string_of_num x;;


let string_of_varpow x k =
  if k = 1 then string_of_vname x else string_of_vname x^"^"^string_of_int k;;

let string_of_monomial m =
  if m = monomial_1 then "1" else
  let vps = List.fold_right (fun (x,k) a -> string_of_varpow x k :: a)
                            (sort humanorder_varpow (graph m)) [] in
  end_itlist (fun s t -> s^"*"^t) vps;;

let string_of_cmonomial (c,m) =
  if m = monomial_1 then string_of_num c
  else if c =/ Int 1 then string_of_monomial m
  else string_of_num c ^ "*" ^ string_of_monomial m;;

let string_of_poly (p:poly) =
  if p = poly_0 then "<<0>>" else
  let cms = sort (fun (m1,_) (m2,_) -> humanorder_monomial m1 m2) (graph p) in
  let s =
    List.fold_left (fun a (m,c) ->
             if c </ Int 0 then a ^ " - " ^ string_of_cmonomial(minus_num c,m)
             else a ^ " + " ^ string_of_cmonomial(c,m))
          "" cms in
  let s1 = String.sub s 0 3
  and s2 = String.sub s 3 (String.length s - 3) in
  "<<" ^(if s1 = " + " then s2 else "-"^s2)^">>";;

(* ------------------------------------------------------------------------- *)
(* Printers.                                                                 *)
(* ------------------------------------------------------------------------- *)

let print_vector v = Format.print_string(string_of_vector 0 20 v);;

let print_matrix m = Format.print_string(string_of_matrix 20 m);;

let print_monomial m = Format.print_string(string_of_monomial m);;

let print_poly m = Format.print_string(string_of_poly m);;

(*
#install_printer print_vector;;
#install_printer print_matrix;;
#install_printer print_monomial;;
#install_printer print_poly;;
*)

(* ------------------------------------------------------------------------- *)
(* Conversion from term.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec poly_of_term t = match t with
  Zero -> poly_0 
| Const n -> poly_const n
| Var x -> poly_var x
| Opp t1 -> poly_neg (poly_of_term t1)
| Inv t1 -> 
      let p = poly_of_term t1 in
      if poly_isconst p then poly_const(Int 1 // eval undefined p)
      else failwith "poly_of_term: inverse of non-constant polyomial"
| Add (l, r) -> poly_add (poly_of_term l) (poly_of_term r)
| Sub (l, r) -> poly_sub (poly_of_term l) (poly_of_term r)
| Mul (l, r) -> poly_mul (poly_of_term l) (poly_of_term r)
| Div (l, r) ->
      let p = poly_of_term l and q = poly_of_term r in
      if poly_isconst q then poly_cmul (Int 1 // eval undefined q) p
      else failwith "poly_of_term: division by non-constant polynomial"
| Pow (t, n) ->
      poly_pow (poly_of_term t) n;;

(* ------------------------------------------------------------------------- *)
(* String of vector (just a list of space-separated numbers).                *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_vector (v:vector) =
  let n = dim v in
  let strs = map (o (decimalize 20) (element v)) (1--n) in
  end_itlist (fun x y -> x ^ " " ^ y) strs ^ "\n";;

(* ------------------------------------------------------------------------- *)
(* String for block diagonal matrix numbered k.                              *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_blockdiagonal k m =
  let pfx = string_of_int k ^" " in
  let ents =
    foldl (fun a (b,i,j) c -> if i > j then a else ((b,i,j),c)::a) [] m in
  let entss = sort (increasing fst) ents in
  itlist (fun ((b,i,j),c) a ->
     pfx ^ string_of_int b ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^
     " " ^ decimalize 20 c ^ "\n" ^ a) entss "";;

(* ------------------------------------------------------------------------- *)
(* String for a matrix numbered k, in SDPA sparse format.                    *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_matrix k (m:matrix) =
  let pfx = string_of_int k ^ " 1 " in
  let ms = foldr (fun (i,j) c a -> if i > j then a else ((i,j),c)::a)
                 (snd m) [] in
  let mss = sort (increasing fst) ms in
  itlist (fun ((i,j),c) a ->
     pfx ^ string_of_int i ^ " " ^ string_of_int j ^
     " " ^ decimalize 20 c ^ "\n" ^ a) mss "";;

(* ------------------------------------------------------------------------- *)
(* String in SDPA sparse format for standard SDP problem:                    *)
(*                                                                           *)
(*    X = v_1 * [M_1] + ... + v_m * [M_m] - [M_0] must be PSD                *)
(*    Minimize obj_1 * v_1 + ... obj_m * v_m                                 *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_problem comment obj mats =
  let m = length mats - 1
  and n,_ = dimensions (hd mats) in
  "\"" ^ comment ^ "\"\n" ^
  string_of_int m ^ "\n" ^
  "1\n" ^
  string_of_int n ^ "\n" ^
  sdpa_of_vector obj ^
  itlist2 (fun k m a -> sdpa_of_matrix (k - 1) m ^ a)
          (1--length mats) mats "";;

(* ------------------------------------------------------------------------- *)
(* More parser basics.                                                       *)
(* ------------------------------------------------------------------------- *)

exception Noparse;;


let isspace,issep,isbra,issymb,isalpha,isnum,isalnum =
  let charcode s = Char.code(String.get s 0) in
  let spaces = " \t\n\r"
  and separators = ",;"
  and brackets = "()[]{}"
  and symbs = "\\!@#$%^&*-+|\\<=>/?~.:"
  and alphas = "'abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  and nums = "0123456789" in
  let allchars = spaces^separators^brackets^symbs^alphas^nums in
  let csetsize = itlist ((o) max charcode) (explode allchars) 256 in
  let ctable = Array.make csetsize 0 in
  do_list (fun c -> Array.set ctable (charcode c) 1) (explode spaces);
  do_list (fun c -> Array.set ctable (charcode c) 2) (explode separators);
  do_list (fun c -> Array.set ctable (charcode c) 4) (explode brackets);
  do_list (fun c -> Array.set ctable (charcode c) 8) (explode symbs);
  do_list (fun c -> Array.set ctable (charcode c) 16) (explode alphas);
  do_list (fun c -> Array.set ctable (charcode c) 32) (explode nums);
  let isspace c = Array.get ctable (charcode c) = 1
  and issep c  = Array.get ctable (charcode c) = 2
  and isbra c  = Array.get ctable (charcode c) = 4
  and issymb c = Array.get ctable (charcode c) = 8
  and isalpha c = Array.get ctable (charcode c) = 16
  and isnum c = Array.get ctable (charcode c) = 32
  and isalnum c = Array.get ctable (charcode c) >= 16 in
  isspace,issep,isbra,issymb,isalpha,isnum,isalnum;;

let (||) parser1 parser2 input =
  try parser1 input
  with Noparse -> parser2 input;;

let (++) parser1 parser2 input =
  let result1,rest1 = parser1 input in
  let result2,rest2 = parser2 rest1 in
  (result1,result2),rest2;;

let rec many prs input =
  try let result,next = prs input in
      let results,rest = many prs next in
      (result::results),rest
  with Noparse -> [],input;;

let (>>) prs treatment input =
  let result,rest = prs input in
  treatment(result),rest;;

let fix err prs input =
  try prs input
  with Noparse -> failwith (err ^ " expected");;

let rec listof prs sep err =
  prs ++ many (sep ++ fix err prs >> snd) >> (fun (h,t) -> h::t);;

let possibly prs input =
  try let x,rest = prs input in [x],rest
  with Noparse -> [],input;;

let some p =
  function
      [] -> raise Noparse
    | (h::t) -> if p h then (h,t) else raise Noparse;;

let a tok = some (fun item -> item = tok);;

let rec atleast n prs i =
  (if n <= 0 then many prs
   else prs ++ atleast (n - 1) prs >> (fun (h,t) -> h::t)) i;;

let finished input =
  if input = [] then 0,input else failwith "Unparsed input";;

let word s =
   end_itlist (fun p1 p2 -> (p1 ++ p2) >> (fun (s,t) -> s^t))
              (map a (explode s));;

let token s =
  many (some isspace) ++ word s ++ many (some isspace)
  >> (fun ((_,t),_) -> t);;

let decimal =
  let numeral = some isnum in
  let decimalint = atleast 1 numeral >> ((o) Num.num_of_string implode) in
  let decimalfrac = atleast 1 numeral
    >> (fun s -> Num.num_of_string(implode s) // pow10 (length s)) in
  let decimalsig =
    decimalint ++ possibly (a "." ++ decimalfrac >> snd)
    >> (function (h,[]) -> h | (h,[x]) -> h +/ x | _ -> failwith "decimalsig") in
  let signed prs =
       a "-" ++ prs >> ((o) minus_num snd)
    || a "+" ++ prs >> snd
    || prs in
  let exponent = (a "e" || a "E") ++ signed decimalint >> snd in
    signed decimalsig ++ possibly exponent
    >> (function (h,[]) -> h | (h,[x]) -> h */ power_num (Int 10) x | _ -> 
     failwith "exponent");;

let mkparser p s =
  let x,rst = p(explode s) in
  if rst = [] then x else failwith "mkparser: unparsed input";;

let parse_decimal = mkparser decimal;;

(* ------------------------------------------------------------------------- *)
(* Parse back a vector.                                                      *)
(* ------------------------------------------------------------------------- *)

let parse_csdpoutput =
  let rec skipupto dscr prs inp =
      (dscr ++ prs >> snd
    || some (fun c -> true) ++ skipupto dscr prs >> snd) inp in
  let ignore inp = (),[] in
  let csdpoutput =
    (decimal ++ many(a " " ++ decimal >> snd) >> (fun (h,t) -> h::t)) ++
    (a " " ++ a "\n" ++ ignore) >> ((o) vector_of_list fst) in
  mkparser csdpoutput;;

(* ------------------------------------------------------------------------- *)
(* CSDP parameters; so far I'm sticking with the defaults.                   *)
(* ------------------------------------------------------------------------- *)

let csdp_default_parameters =
"axtol=1.0e-8
atytol=1.0e-8
objtol=1.0e-8
pinftol=1.0e8
dinftol=1.0e8
maxiter=100
minstepfrac=0.9
maxstepfrac=0.97
minstepp=1.0e-8
minstepd=1.0e-8
usexzgap=1
tweakgap=0
affine=0
printlevel=1
";;

let csdp_params = csdp_default_parameters;;

(* ------------------------------------------------------------------------- *)
(* The same thing with CSDP.                                                 *)
(* Modified by the Coq development team to use a cache                       *)
(* ------------------------------------------------------------------------- *)

let buffer_add_line buff line =
  Buffer.add_string buff line; Buffer.add_char buff '\n'

let string_of_file filename =
  let fd = open_in filename in
  let buff = Buffer.create 16 in
  try while true do buffer_add_line buff (input_line fd) done; failwith ""
  with End_of_file -> (close_in fd; Buffer.contents buff)

let file_of_string filename s =
  let fd = Pervasives.open_out filename in
  output_string fd s; close_out fd

(*
let request_mark = "*** REQUEST ***"
let answer_mark  = "*** ANSWER ***"
let end_mark     = "*** END ***"
let infeasible_mark = "Infeasible\n"
let failure_mark    = "Failure\n"

let cache_name = "csdp.cache"

let look_in_cache string_problem =
  let n = String.length string_problem in
  try
    let inch = open_in cache_name in
    let rec search () =
      while input_line inch <> request_mark do () done;
      let i = ref 0 in
      while !i < n & string_problem.[!i] = input_char inch do incr i done;
      if !i < n or input_line inch <> answer_mark then
	search ()
      else begin
	let buff = Buffer.create 16 in
	let line = ref (input_line inch) in
	while (!line <> end_mark) do
	  buffer_add_line buff !line; line := input_line inch
	done;
	close_in inch;
	Buffer.contents buff
      end in
    try search () with End_of_file -> close_in inch; raise Not_found
  with Sys_error _ -> raise Not_found

let flush_to_cache string_problem string_result =
  try
    let flags = [Open_append;Open_text;Open_creat] in
    let outch = open_out_gen flags 0o666 cache_name in
    begin 
    try
      Printf.fprintf outch "%s\n" request_mark;
      Printf.fprintf outch "%s" string_problem;
      Printf.fprintf outch "%s\n" answer_mark;
      Printf.fprintf outch "%s" string_result;
      Printf.fprintf outch "%s\n" end_mark;
    with Sys_error _ as e -> close_out outch; raise e
    end;
    close_out outch
  with Sys_error _ -> 
    print_endline "Warning: Could not open or write to csdp cache"
*)
exception CsdpInfeasible

let run_csdp dbg string_problem =
(*  try
   let res = look_in_cache string_problem in
   if res = infeasible_mark then raise CsdpInfeasible;
   if res = failure_mark then failwith "csdp error";
   res
  with Not_found -> *)
  let input_file = Filename.temp_file "sos" ".dat-s" in
  let output_file = Filename.temp_file "sos" ".dat-s" in
  let temp_path = Filename.dirname input_file in
  let params_file = Filename.concat temp_path "param.csdp" in
  file_of_string input_file string_problem;
  file_of_string params_file csdp_params;
  let rv = Sys.command("cd "^temp_path^"; csdp "^input_file^" "^output_file^
                       (if dbg then "" else "> /dev/null")) in
    if rv = 1 or rv = 2 then 
      ((*flush_to_cache string_problem infeasible_mark;*) raise CsdpInfeasible); 
  if rv = 127 then
     (print_string "csdp not found, exiting..."; exit 1);
  if rv <> 0 & rv <> 3 (* reduced accuracy *) then
    ((*flush_to_cache string_problem failure_mark;*)
     failwith("csdp: error "^string_of_int rv));
  let string_result = string_of_file output_file in
(*  flush_to_cache string_problem string_result;*)
  if not dbg then
    (Sys.remove input_file; Sys.remove output_file; Sys.remove params_file);
  string_result

let csdp obj mats =
  try parse_csdpoutput (run_csdp !debugging (sdpa_of_problem "" obj mats))
  with CsdpInfeasible -> failwith "csdp: Problem is infeasible"

(* ------------------------------------------------------------------------- *)
(* Try some apparently sensible scaling first. Note that this is purely to   *)
(* get a cleaner translation to floating-point, and doesn't affect any of    *)
(* the results, in principle. In practice it seems a lot better when there   *)
(* are extreme numbers in the original problem.                              *)
(* ------------------------------------------------------------------------- *)

let scale_then =
  let common_denominator amat acc =
    foldl (fun a m c -> lcm_num (denominator c) a) acc amat
  and maximal_element amat acc =
    foldl (fun maxa m c -> max_num maxa (abs_num c)) acc amat in
  fun solver obj mats ->
    let cd1 = itlist common_denominator mats (Int 1)
    and cd2 = common_denominator (snd obj)  (Int 1) in
    let mats' = map (mapf (fun x -> cd1 */ x)) mats
    and obj' = vector_cmul cd2 obj in
    let max1 = itlist maximal_element mats' (Int 0)
    and max2 = maximal_element (snd obj') (Int 0) in
    let scal1 = pow2 (20-int_of_float(log(float_of_num max1) /. log 2.0))
    and scal2 = pow2 (20-int_of_float(log(float_of_num max2) /. log 2.0)) in
    let mats'' = map (mapf (fun x -> x */ scal1)) mats'
    and obj'' = vector_cmul scal2 obj' in
    solver obj'' mats'';;

(* ------------------------------------------------------------------------- *)
(* Round a vector to "nice" rationals.                                       *)
(* ------------------------------------------------------------------------- *)

let nice_rational n x = round_num (n */ x) // n;;

let nice_vector n = mapa (nice_rational n);;

(* ------------------------------------------------------------------------- *)
(* Reduce linear program to SDP (diagonal matrices) and test with CSDP. This *)
(* one tests A [-1;x1;..;xn] >= 0 (i.e. left column is negated constants).   *)
(* ------------------------------------------------------------------------- *)

let linear_program_basic a =
  let m,n = dimensions a in
  let mats =  map (fun j -> diagonal (column j a)) (1--n)
  and obj = vector_const (Int 1) m in
  try ignore (run_csdp false (sdpa_of_problem "" obj mats)); true
  with CsdpInfeasible -> false

(* ------------------------------------------------------------------------- *)
(* Test whether a point is in the convex hull of others. Rather than use     *)
(* computational geometry, express as linear inequalities and call CSDP.     *)
(* This is a bit lazy of me, but it's easy and not such a bottleneck so far. *)
(* ------------------------------------------------------------------------- *)

let in_convex_hull pts pt =
  let pts1 = (1::pt) :: map (fun x -> 1::x) pts in
  let pts2 = map (fun p -> map (fun x -> -x) p @ p) pts1 in
  let n = length pts + 1
  and v = 2 * (length pt + 1) in
  let m = v + n - 1 in
  let mat =
    (m,n),
    itern 1 pts2 (fun pts j -> itern 1 pts (fun x i -> (i,j) |-> Int x))
                 (iter (1,n) (fun i -> (v + i,i+1) |-> Int 1) undefined) in
  linear_program_basic mat;;

(* ------------------------------------------------------------------------- *)
(* Filter down a set of points to a minimal set with the same convex hull.   *)
(* ------------------------------------------------------------------------- *)

let minimal_convex_hull =
  let augment1 = function (m::ms) -> if in_convex_hull ms m then ms else ms@[m] 
          | _ -> failwith "augment1"
  in
  let augment m ms = funpow 3 augment1 (m::ms) in
  fun mons ->
    let mons' = itlist augment (tl mons) [hd mons] in
    funpow (length mons') augment1 mons';;

(* ------------------------------------------------------------------------- *)
(* Stuff for "equations" (generic A->num functions).                         *)
(* ------------------------------------------------------------------------- *)

let equation_cmul c eq =
  if c =/ Int 0 then Empty else mapf (fun d -> c */ d) eq;;

let equation_add eq1 eq2 = combine (+/) (fun x -> x =/ Int 0) eq1 eq2;;

let equation_eval assig eq =
  let value v = apply assig v in
  foldl (fun a v c -> a +/ value(v) */ c) (Int 0) eq;;

(* ------------------------------------------------------------------------- *)
(* Eliminate among linear equations: return unconstrained variables and      *)
(* assignments for the others in terms of them. We give one pseudo-variable  *)
(* "one" that's used for a constant term.                                    *)
(* ------------------------------------------------------------------------- *)


let eliminate_equations =
  let rec extract_first p l =
    match l with
      [] -> failwith "extract_first"
    | h::t -> if p(h) then h,t else
              let k,s = extract_first p t in
              k,h::s in
  let rec eliminate vars dun eqs =
    match vars with
      [] -> if forall is_undefined eqs then dun
            else (raise Unsolvable)
    | v::vs ->
            try let eq,oeqs = extract_first (fun e -> defined e v) eqs in
                let a = apply eq v in
                let eq' = equation_cmul (Int(-1) // a) (undefine v eq) in
                let elim e =
                  let b = tryapplyd e v (Int 0) in
                  if b =/ Int 0 then e else
                  equation_add e (equation_cmul (minus_num b // a) eq) in
                eliminate vs ((v |-> eq') (mapf elim dun)) (map elim oeqs)
            with Failure _ -> eliminate vs dun eqs in
  fun one vars eqs ->
    let assig = eliminate vars undefined eqs in
    let vs = foldl (fun a x f -> subtract (dom f) [one] @ a) [] assig in
    setify vs,assig;;

(* ------------------------------------------------------------------------- *)
(* Eliminate all variables, in an essentially arbitrary order.               *)
(* ------------------------------------------------------------------------- *)

let eliminate_all_equations one =
  let choose_variable eq =
    let (v,_) = choose eq in
    if v = one then
      let eq' = undefine v eq in
      if is_undefined eq' then failwith "choose_variable" else
      let (w,_) = choose eq' in w
    else v in
  let rec eliminate dun eqs =
    match eqs with
      [] -> dun
    | eq::oeqs ->
        if is_undefined eq then eliminate dun oeqs else
        let v = choose_variable eq in
        let a = apply eq v in
        let eq' = equation_cmul (Int(-1) // a) (undefine v eq) in
        let elim e =
          let b = tryapplyd e v (Int 0) in
          if b =/ Int 0 then e else
          equation_add e (equation_cmul (minus_num b // a) eq) in
        eliminate ((v |-> eq') (mapf elim dun)) (map elim oeqs) in
  fun eqs ->
    let assig = eliminate undefined eqs in
    let vs = foldl (fun a x f -> subtract (dom f) [one] @ a) [] assig in
    setify vs,assig;;

(* ------------------------------------------------------------------------- *)
(* Solve equations by assigning arbitrary numbers.                           *)
(* ------------------------------------------------------------------------- *)

let solve_equations one eqs =
  let vars,assigs = eliminate_all_equations one eqs in
  let vfn = itlist (fun v -> (v |-> Int 0)) vars (one |=> Int(-1)) in
  let ass =
    combine (+/) (fun c -> false) (mapf (equation_eval vfn) assigs) vfn in
  if forall (fun e -> equation_eval ass e =/ Int 0) eqs
  then undefine one ass else raise Sanity;;

(* ------------------------------------------------------------------------- *)
(* Hence produce the "relevant" monomials: those whose squares lie in the    *)
(* Newton polytope of the monomials in the input. (This is enough according  *)
(* to Reznik: "Extremal PSD forms with few terms", Duke Math. Journal,       *)
(* vol 45, pp. 363--374, 1978.                                               *)
(*                                                                           *)
(* These are ordered in sort of decreasing degree. In particular the         *)
(* constant monomial is last; this gives an order in diagonalization of the  *)
(* quadratic form that will tend to display constants.                       *)
(* ------------------------------------------------------------------------- *)

let newton_polytope pol =
  let vars = poly_variables pol in
  let mons = map (fun m -> map (fun x -> monomial_degree x m) vars) (dom pol)
  and ds = map (fun x -> (degree x pol + 1) / 2) vars in
  let all = itlist (fun n -> allpairs (fun h t -> h::t) (0--n)) ds [[]]
  and mons' = minimal_convex_hull mons in
  let all' =
    filter (fun m -> in_convex_hull mons' (map (fun x -> 2 * x) m)) all in
  map (fun m -> itlist2 (fun v i a -> if i = 0 then a else (v |-> i) a)
                        vars m monomial_1) (rev all');;

(* ------------------------------------------------------------------------- *)
(* Diagonalize (Cholesky/LDU) the matrix corresponding to a quadratic form.  *)
(* ------------------------------------------------------------------------- *)

let diag m =
  let nn = dimensions m in
  let n = fst nn in
  if snd nn <> n then failwith "diagonalize: non-square matrix" else
  let rec diagonalize i m =
    if is_zero m then [] else
    let a11 = element m (i,i) in
    if a11 </ Int 0 then failwith "diagonalize: not PSD"
    else if a11 =/ Int 0 then
      if is_zero(row i m) then diagonalize (i + 1) m
      else failwith "diagonalize: not PSD"
    else
      let v = row i m in
      let v' = mapa (fun a1k -> a1k // a11) v in
      let m' =
      (n,n),
      iter (i+1,n) (fun j ->
          iter (i+1,n) (fun k ->
              ((j,k) |--> (element m (j,k) -/ element v j */ element v' k))))
          undefined in
      (a11,v')::diagonalize (i + 1) m' in
  diagonalize 1 m;;

(* ------------------------------------------------------------------------- *)
(* Adjust a diagonalization to collect rationals at the start.               *)
(* ------------------------------------------------------------------------- *)

let deration d =
  if d = [] then Int 0,d else
  let adj(c,l) =
    let a = foldl (fun a i c -> lcm_num a (denominator c)) (Int 1) (snd l) //
            foldl (fun a i c -> gcd_num a (numerator c)) (Int 0) (snd l) in
    (c // (a */ a)),mapa (fun x -> a */ x) l in
  let d' = map adj d in
  let a = itlist ((o) lcm_num ((o) denominator fst)) d' (Int 1) //
          itlist ((o) gcd_num ((o) numerator fst)) d' (Int 0)  in
  (Int 1 // a),map (fun (c,l) -> (a */ c,l)) d';;

(* ------------------------------------------------------------------------- *)
(* Enumeration of monomials with given multidegree bound.                    *)
(* ------------------------------------------------------------------------- *)

let rec enumerate_monomials d vars =
  if d < 0 then []
  else if d = 0 then [undefined]
  else if vars = [] then [monomial_1] else
  let alts =
    map (fun k -> let oths = enumerate_monomials (d - k) (tl vars) in
                  map (fun ks -> if k = 0 then ks else (hd vars |-> k) ks) oths)
        (0--d) in
  end_itlist (@) alts;;

(* ------------------------------------------------------------------------- *)
(* Enumerate products of distinct input polys with degree <= d.              *)
(* We ignore any constant input polynomials.                                 *)
(* Give the output polynomial and a record of how it was derived.            *)
(* ------------------------------------------------------------------------- *)

let rec enumerate_products d pols =
  if d = 0 then [poly_const num_1,Rational_lt num_1] else if d < 0 then [] else
  match pols with
    [] -> [poly_const num_1,Rational_lt num_1]
  | (p,b)::ps -> let e = multidegree p in
                 if e = 0 then enumerate_products d ps else
                 enumerate_products d ps @
                 map (fun (q,c) -> poly_mul p q,Product(b,c))
                     (enumerate_products (d - e) ps);;

(* ------------------------------------------------------------------------- *)
(* Multiply equation-parametrized poly by regular poly and add accumulator.  *)
(* ------------------------------------------------------------------------- *)

let epoly_pmul p q acc =
  foldl (fun a m1 c ->
           foldl (fun b m2 e ->
                        let m =  monomial_mul m1 m2 in
                        let es = tryapplyd b m undefined in
                        (m |-> equation_add (equation_cmul c e) es) b)
                 a q) acc p;;

(* ------------------------------------------------------------------------- *)
(* Usual operations on equation-parametrized poly.                           *)
(* ------------------------------------------------------------------------- *)

let epoly_cmul c l =
  if c =/ Int 0 then undefined else mapf (equation_cmul c) l;;

let epoly_neg x = epoly_cmul (Int(-1)) x;;

let epoly_add x = combine equation_add is_undefined x;;

let epoly_sub p q = epoly_add p (epoly_neg q);;

(* ------------------------------------------------------------------------- *)
(* Convert regular polynomial. Note that we treat (0,0,0) as -1.             *)
(* ------------------------------------------------------------------------- *)

let epoly_of_poly p =
  foldl (fun a m c -> (m |-> ((0,0,0) |=> minus_num c)) a) undefined p;;

(* ------------------------------------------------------------------------- *)
(* String for block diagonal matrix numbered k.                              *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_blockdiagonal k m =
  let pfx = string_of_int k ^" " in
  let ents =
    foldl (fun a (b,i,j) c -> if i > j then a else ((b,i,j),c)::a) [] m in
  let entss = sort (increasing fst) ents in
  itlist (fun ((b,i,j),c) a ->
     pfx ^ string_of_int b ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^
     " " ^ decimalize 20 c ^ "\n" ^ a) entss "";;

(* ------------------------------------------------------------------------- *)
(* SDPA for problem using block diagonal (i.e. multiple SDPs)                *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_blockproblem comment nblocks blocksizes obj mats =
  let m = length mats - 1 in
  "\"" ^ comment ^ "\"\n" ^
  string_of_int m ^ "\n" ^
  string_of_int nblocks ^ "\n" ^
  (end_itlist (fun s t -> s^" "^t) (map string_of_int blocksizes)) ^
  "\n" ^
  sdpa_of_vector obj ^
  itlist2 (fun k m a -> sdpa_of_blockdiagonal (k - 1) m ^ a)
          (1--length mats) mats "";;

(* ------------------------------------------------------------------------- *)
(* Hence run CSDP on a problem in block diagonal form.                       *)
(* ------------------------------------------------------------------------- *)

let csdp_blocks nblocks blocksizes obj mats =
  let string_problem = sdpa_of_blockproblem "" nblocks blocksizes obj mats in
  try parse_csdpoutput (run_csdp !debugging string_problem)
  with CsdpInfeasible -> failwith "csdp: Problem is infeasible"

(* ------------------------------------------------------------------------- *)
(* 3D versions of matrix operations to consider blocks separately.           *)
(* ------------------------------------------------------------------------- *)

let bmatrix_add = combine (+/) (fun x -> x =/ Int 0);;

let bmatrix_cmul c bm =
  if c =/ Int 0 then undefined
  else mapf (fun x -> c */ x) bm;;

let bmatrix_neg = bmatrix_cmul (Int(-1));;

let bmatrix_sub m1 m2 = bmatrix_add m1 (bmatrix_neg m2);;

(* ------------------------------------------------------------------------- *)
(* Smash a block matrix into components.                                     *)
(* ------------------------------------------------------------------------- *)

let blocks blocksizes bm =
  map (fun (bs,b0) ->
        let m = foldl
          (fun a (b,i,j) c -> if b = b0 then ((i,j) |-> c) a else a)
          undefined bm in
        (*let d = foldl (fun a (i,j) c -> max a (max i j)) 0 m in*)
        (((bs,bs),m):matrix))
      (zip blocksizes (1--length blocksizes));;

(* ------------------------------------------------------------------------- *)
(* Positiv- and Nullstellensatz. Flag "linf" forces a linear representation. *)
(* ------------------------------------------------------------------------- *)

let real_positivnullstellensatz_general linf d eqs leqs pol 
  :   poly list *  (positivstellensatz * (num * poly) list) list  =
  
  let vars = itlist ((o) union poly_variables) (pol::eqs @ map fst leqs) [] in
  let monoid =
    if linf then
      (poly_const num_1,Rational_lt num_1)::
      (filter (fun (p,c) -> multidegree p <= d) leqs)
    else enumerate_products d leqs in
  let nblocks = length monoid in
  let mk_idmultiplier k p =
    let e = d - multidegree p in
    let mons = enumerate_monomials e vars in
    let nons = zip mons (1--length mons) in
    mons,
    itlist (fun (m,n) -> (m |-> ((-k,-n,n) |=> Int 1))) nons undefined in
  let mk_sqmultiplier k (p,c) =
    let e = (d - multidegree p) / 2 in
    let mons = enumerate_monomials e vars in
    let nons = zip mons (1--length mons) in
    mons,
    itlist (fun (m1,n1) ->
      itlist (fun (m2,n2) a ->
          let m = monomial_mul m1 m2 in
          if n1 > n2 then a else
          let c = if n1 = n2 then Int 1 else Int 2 in
          let e = tryapplyd a m undefined in
          (m |-> equation_add ((k,n1,n2) |=> c) e) a)
         nons)
       nons undefined in
  let sqmonlist,sqs = unzip(map2 mk_sqmultiplier (1--length monoid) monoid)
  and idmonlist,ids =  unzip(map2 mk_idmultiplier (1--length eqs) eqs) in
  let blocksizes = map length sqmonlist in
  let bigsum =
    itlist2 (fun p q a -> epoly_pmul p q a) eqs ids
            (itlist2 (fun (p,c) s a -> epoly_pmul p s a) monoid sqs
                     (epoly_of_poly(poly_neg pol))) in
  let eqns = foldl (fun a m e -> e::a) [] bigsum in
  let pvs,assig = eliminate_all_equations (0,0,0) eqns in
  let qvars = (0,0,0)::pvs in
  let allassig = itlist (fun v -> (v |-> (v |=> Int 1))) pvs assig in
  let mk_matrix v =
    foldl (fun m (b,i,j) ass -> if b < 0 then m else
                                let c = tryapplyd ass v (Int 0) in
                                if c =/ Int 0 then m else
                                ((b,j,i) |-> c) (((b,i,j) |-> c) m))
          undefined allassig in
  let diagents = foldl
    (fun a (b,i,j) e -> if b > 0 & i = j then equation_add e a else a)
    undefined allassig in
  let mats = map mk_matrix qvars
  and obj = length pvs,
            itern 1 pvs (fun v i -> (i |--> tryapplyd diagents v (Int 0)))
                        undefined in
  let raw_vec = if pvs = [] then vector_0 0
                else scale_then (csdp_blocks nblocks blocksizes) obj mats in
  let find_rounding d =
   (if !debugging then
     (Format.print_string("Trying rounding with limit "^string_of_num d);
      Format.print_newline())
    else ());
    let vec = nice_vector d raw_vec in
    let blockmat = iter (1,dim vec)
     (fun i a -> bmatrix_add (bmatrix_cmul (element vec i) (el i mats)) a)
     (bmatrix_neg (el 0 mats)) in
    let allmats = blocks blocksizes blockmat in
    vec,map diag allmats in
  let vec,ratdias =
    if pvs = [] then find_rounding num_1
    else tryfind find_rounding (map Num.num_of_int (1--31) @
                                map pow2 (5--66)) in
  let newassigs =
    itlist (fun k -> el (k - 1) pvs |-> element vec k)
           (1--dim vec) ((0,0,0) |=> Int(-1)) in
  let finalassigs =
    foldl (fun a v e -> (v |-> equation_eval newassigs e) a) newassigs
          allassig in
  let poly_of_epoly p =
    foldl (fun a v e -> (v |--> equation_eval finalassigs e) a)
          undefined p in
  let mk_sos mons =
    let mk_sq (c,m) =
        c,itlist (fun k a -> (el (k - 1) mons |--> element m k) a)
                 (1--length mons) undefined in
    map mk_sq in
  let sqs = map2 mk_sos sqmonlist ratdias
  and cfs = map poly_of_epoly ids in
  let msq = filter (fun (a,b) -> b <> []) (map2 (fun a b -> a,b) monoid sqs) in
  let eval_sq sqs = itlist
   (fun (c,q) -> poly_add (poly_cmul c (poly_mul q q))) sqs poly_0 in
  let sanity =
    itlist (fun ((p,c),s) -> poly_add (poly_mul p (eval_sq s))) msq
           (itlist2 (fun p q -> poly_add (poly_mul p q)) cfs eqs
                    (poly_neg pol)) in
  if not(is_undefined sanity) then raise Sanity else
     cfs,map (fun (a,b) -> snd a,b) msq;;


let term_of_monoid l1 m = itlist  (fun i m -> Mul (nth l1 i,m)) m (Const num_1)

let rec term_of_pos l1 x = match x with
   Axiom_eq i -> failwith "term_of_pos"
 | Axiom_le i -> nth l1 i
 | Axiom_lt i -> nth l1 i
 | Monoid m   -> term_of_monoid l1 m
 | Rational_eq n -> Const n
 | Rational_le n -> Const n
 | Rational_lt n -> Const n
 | Square t -> Pow (t, 2)
 | Eqmul (t, y) -> Mul (t, term_of_pos l1 y)
 | Sum (y, z) -> Add  (term_of_pos l1 y, term_of_pos l1 z)
 | Product (y, z) -> Mul (term_of_pos l1 y, term_of_pos l1 z);;


let dest_monomial mon = sort (increasing fst) (graph mon);;

let monomial_order =
  let rec lexorder l1 l2 =
    match (l1,l2) with
      [],[] -> true
    | vps,[] -> false
    | [],vps -> true
    | ((x1,n1)::vs1),((x2,n2)::vs2) ->
          if x1 < x2 then true
          else if x2 < x1 then false
          else if n1 < n2 then false
          else if n2 < n1 then true
          else lexorder vs1 vs2 in
  fun m1 m2 ->
    if m2 = monomial_1 then true else if m1 = monomial_1 then false else
    let mon1 = dest_monomial m1 and mon2 = dest_monomial m2 in
    let deg1 = itlist ((o) (+) snd) mon1 0
    and deg2 = itlist ((o) (+) snd) mon2 0 in
    if deg1 < deg2 then false else if deg1 > deg2 then true
    else lexorder mon1 mon2;;

let dest_poly p =
  map (fun (m,c) -> c,dest_monomial m)
      (sort (fun (m1,_) (m2,_) -> monomial_order m1 m2) (graph p));;

(* ------------------------------------------------------------------------- *)
(* Map back polynomials and their composites to term.                        *)
(* ------------------------------------------------------------------------- *)

let term_of_varpow =
  fun x k ->
    if k = 1 then Var x else Pow (Var x, k);;

let term_of_monomial =
  fun m -> if m = monomial_1 then Const num_1 else
           let m' = dest_monomial m in
           let vps = itlist (fun (x,k) a -> term_of_varpow x k :: a) m' [] in
           end_itlist (fun s t -> Mul (s,t)) vps;;

let term_of_cmonomial =
  fun (m,c) ->
    if m = monomial_1 then Const c
    else if c =/ num_1 then term_of_monomial m
    else Mul (Const c,term_of_monomial m);;

let term_of_poly =
  fun p ->
    if p = poly_0 then Zero else
    let cms = map term_of_cmonomial
     (sort (fun (m1,_) (m2,_) -> monomial_order m1 m2) (graph p)) in
    end_itlist (fun t1 t2 -> Add (t1,t2)) cms;;

let term_of_sqterm (c,p) =
  Product(Rational_lt c,Square(term_of_poly p));;

let term_of_sos (pr,sqs) =
  if sqs = [] then pr
  else Product(pr,end_itlist (fun a b -> Sum(a,b)) (map term_of_sqterm sqs));;

let rec deepen f n =
  try (*print_string "Searching with depth limit ";
      print_int n; print_newline();*) f n
  with Failure _ -> deepen f (n + 1);;





exception TooDeep

let deepen_until limit f n = 
  match compare limit 0 with
    | 0 -> raise TooDeep
    | -1 -> deepen f n
    | _  -> 
	let rec d_until  f n =
	  try if !debugging 
	  then (print_string "Searching with depth limit "; 
		print_int n; print_newline()) ; f n
	  with Failure x -> 
	    if !debugging then (Printf.printf "solver error : %s\n" x) ; 
	    if n = limit then raise TooDeep else  d_until f (n + 1) in
	  d_until f n


(* patch to remove  zero polynomials from equalities.
   In this case, hol light loops *)

let real_nonlinear_prover  depthmax eqs les lts =
  let eq = map poly_of_term eqs
  and le = map poly_of_term les
  and lt = map poly_of_term lts in
  let pol = itlist poly_mul lt (poly_const num_1)
  and lep = map (fun (t,i) -> t,Axiom_le i) (zip le (0--(length le - 1)))
  and ltp =  map (fun (t,i) -> t,Axiom_lt i) (zip lt (0--(length lt - 1))) 
  and eqp =  itlist2 (fun t i res -> 
   if t = undefined then res else (t,Axiom_eq i)::res) eq (0--(length eq - 1)) []
  in
    
  let proof =
      let leq = lep @ ltp in
      let eq = List.map fst eqp in
      let tryall d =
	let e = multidegree pol (*and pol' = poly_neg pol*) in
	let k = if e = 0 then 1 else d / e in
	  tryfind (fun i -> d,i, 
	   real_positivnullstellensatz_general false d  eq leq
            (poly_neg(poly_pow pol i)))
           (0--k) in
      let d,i,(cert_ideal,cert_cone) = deepen_until depthmax tryall 0 in
      let proofs_ideal =
       map2 (fun q i -> Eqmul(term_of_poly q,i))
        cert_ideal (List.map snd eqp)
      and proofs_cone = map term_of_sos cert_cone
      and proof_ne =
       if lt = [] then Rational_lt num_1 else
	let p = end_itlist (fun s t -> Product(s,t)) (map snd ltp) in
	 funpow i (fun q -> Product(p,q)) (Rational_lt num_1) in
       end_itlist (fun s t -> Sum(s,t)) (proof_ne :: proofs_ideal @ proofs_cone) in
   if !debugging then (print_string("Translating proof certificate to Coq"); print_newline());
   proof;;


(* ------------------------------------------------------------------------- *)
(* Now pure SOS stuff.                                                       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Some combinatorial helper functions.                                      *)
(* ------------------------------------------------------------------------- *)

let rec allpermutations l =
  if l = [] then [[]] else
  itlist (fun h acc -> map (fun t -> h::t)
                (allpermutations (subtract l [h])) @ acc) l [];;

let allvarorders l =
  map (fun vlis x -> index x vlis) (allpermutations l);;

let changevariables_monomial zoln (m:monomial) =
  foldl (fun a x k -> (assoc x zoln |-> k) a) monomial_1 m;;

let changevariables zoln pol =
  foldl (fun a m c -> (changevariables_monomial zoln m |-> c) a)
        poly_0 pol;;

(* ------------------------------------------------------------------------- *)
(* Sum-of-squares function with some lowbrow symmetry reductions.            *)
(* ------------------------------------------------------------------------- *)

let sumofsquares_general_symmetry tool pol =
  let vars = poly_variables pol
  and lpps = newton_polytope pol in
  let n = length lpps in
  let sym_eqs =
    let invariants = filter
     (fun vars' ->
        is_undefined(poly_sub pol (changevariables (zip vars vars') pol)))
     (allpermutations vars) in
(*    let lpps2 = allpairs monomial_mul lpps lpps in*)
(*    let lpp2_classes =
       setify(map (fun m ->
         setify(map (fun vars' -> changevariables_monomial (zip vars vars') m)
                   invariants)) lpps2) in *)
    let lpns = zip lpps (1--length lpps) in
    let lppcs =
      filter (fun (m,(n1,n2)) -> n1 <= n2)
             (allpairs
               (fun (m1,n1) (m2,n2) -> (m1,m2),(n1,n2)) lpns lpns) in
    let clppcs = end_itlist (@)
       (map (fun ((m1,m2),(n1,n2)) ->
                map (fun vars' ->
                        (changevariables_monomial (zip vars vars') m1,
                         changevariables_monomial (zip vars vars') m2),(n1,n2))
                    invariants)
            lppcs) in
    let clppcs_dom = setify(map fst clppcs) in
    let clppcs_cls = map (fun d -> filter (fun (e,_) -> e = d) clppcs)
                         clppcs_dom in
    let eqvcls = map (o setify (map snd)) clppcs_cls in
    let mk_eq cls acc =
      match cls with
        [] -> raise Sanity
      | [h] -> acc
      | h::t -> map (fun k -> (k |-> Int(-1)) (h |=> Int 1)) t @ acc in
    itlist mk_eq eqvcls [] in
  let eqs = foldl (fun a x y -> y::a) []
   (itern 1 lpps (fun m1 n1 ->
        itern 1 lpps (fun m2 n2 f ->
                let m = monomial_mul m1 m2 in
                if n1 > n2 then f else
                let c = if n1 = n2 then Int 1 else Int 2 in
                (m |-> ((n1,n2) |-> c) (tryapplyd f m undefined)) f))
       (foldl (fun a m c -> (m |-> ((0,0)|=>c)) a)
              undefined pol)) @
    sym_eqs in
  let pvs,assig = eliminate_all_equations (0,0) eqs in
  let allassig = itlist (fun v -> (v |-> (v |=> Int 1))) pvs assig in
  let qvars = (0,0)::pvs in
  let diagents =
    end_itlist equation_add (map (fun i -> apply allassig (i,i)) (1--n)) in
  let mk_matrix v =
   ((n,n),
    foldl (fun m (i,j) ass -> let c = tryapplyd ass v (Int 0) in
                              if c =/ Int 0 then m else
                              ((j,i) |-> c) (((i,j) |-> c) m))
          undefined allassig :matrix) in
  let mats = map mk_matrix qvars
  and obj = length pvs,
            itern 1 pvs (fun v i -> (i |--> tryapplyd diagents v (Int 0)))
                undefined in
  let raw_vec = if pvs = [] then vector_0 0 else tool obj mats in
  let find_rounding d =
   (if !debugging then
     (Format.print_string("Trying rounding with limit "^string_of_num d);
      Format.print_newline())
    else ());
    let vec = nice_vector d raw_vec in
    let mat = iter (1,dim vec)
     (fun i a -> matrix_add (matrix_cmul (element vec i) (el i mats)) a)
     (matrix_neg (el 0 mats)) in
    deration(diag mat) in
  let rat,dia =
    if pvs = [] then
       let mat = matrix_neg (el 0 mats) in
       deration(diag mat)
    else
       tryfind find_rounding (map Num.num_of_int (1--31) @
                              map pow2 (5--66)) in
  let poly_of_lin(d,v) =
    d,foldl(fun a i c -> (el (i - 1) lpps |-> c) a) undefined (snd v) in
  let lins = map poly_of_lin dia in
  let sqs = map (fun (d,l) -> poly_mul (poly_const d) (poly_pow l 2)) lins in
  let sos = poly_cmul rat (end_itlist poly_add sqs) in
  if is_undefined(poly_sub sos pol) then rat,lins else raise Sanity;;

let (sumofsquares: poly -> Num.num * (( Num.num * poly) list))  = 
sumofsquares_general_symmetry csdp;;
