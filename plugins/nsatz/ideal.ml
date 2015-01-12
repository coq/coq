(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Nullstellensatz with Groebner basis computation

We use a sparse representation for polynomials:
a monomial is an array of exponents (one for each variable)
with its degree in head
a polynomial is a sorted list of (coefficient, monomial)

 *)

open Utile

exception NotInIdeal

module type S = sig

(* Monomials *)
type mon = int array

val mult_mon : mon -> mon -> mon
val deg : mon -> int
val compare_mon : mon -> mon -> int
val div_mon : mon -> mon -> mon
val div_mon_test : mon -> mon -> bool
val ppcm_mon : mon -> mon -> mon

(* Polynomials *)

type deg = int
type coef
type poly
type polynom 

val repr : poly -> (coef * mon) list
val polconst : coef -> poly
val zeroP : poly
val gen : int -> poly

val equal : poly -> poly -> bool
val name_var : string list ref
val getvar : string list -> int -> string
val lstringP : poly list -> string
val printP : poly -> unit
val lprintP : poly list -> unit

val div_pol_coef : poly -> coef -> poly
val plusP : poly -> poly -> poly
val mult_t_pol : coef -> mon -> poly -> poly
val selectdiv : mon -> poly list -> poly
val oppP : poly -> poly
val emultP : coef -> poly -> poly
val multP : poly -> poly -> poly
val puisP : poly -> int -> poly
val contentP : poly -> coef
val contentPlist : poly list -> coef
val pgcdpos : coef -> coef -> coef
val div_pol : poly -> poly -> coef -> coef -> mon -> poly
val reduce2 : poly -> poly list -> coef * poly

val poldepcontent : coef list ref
val coefpoldep_find : poly -> poly -> poly
val coefpoldep_set : poly -> poly -> poly -> unit
val initcoefpoldep : poly list -> unit
val reduce2_trace : poly -> poly list -> poly list -> poly list * poly
val spol : poly -> poly -> poly
val etrangers : poly -> poly -> bool
val div_ppcm : poly -> poly -> poly -> bool

val genPcPf : poly -> poly list -> poly list -> poly list
val genOCPf : poly list -> poly list

val is_homogeneous : poly -> bool

type certificate =
    { coef : coef; power : int;
      gb_comb : poly list list; last_comb : poly list }

val test_dans_ideal : poly -> poly list -> poly list ->
  poly list * poly * certificate
val in_ideal : deg -> poly list -> poly -> poly list * poly * certificate

end

(***********************************************************************
   Global options
*)
let lexico = ref false
let use_hmon = ref false

(* division of tail monomials *)

let reduire_les_queues = false

(* divide first with new polynomials *)

let nouveaux_pol_en_tete = false

(***********************************************************************
   Functor
*)

module Make (P:Polynom.S) = struct

  type coef = P.t
  let coef0 = P.of_num (Num.Int 0)
  let coef1 = P.of_num (Num.Int 1)
  let coefm1 = P.of_num (Num.Int (-1))
  let string_of_coef c = "["^(P.to_string c)^"]"

(***********************************************************************
   Monomials
 array of integers, first is the degree
*)

type mon = int array
type deg = int
type poly = (coef * mon) list
type polynom = 
   {pol : poly ref;
    num : int;
    sugar : int}

let nvar m =  Array.length m - 1

let deg m = m.(0)

let mult_mon m m' =
  let d = nvar m in
  let m'' = Array.make (d+1) 0 in
  for i=0 to d do
    m''.(i)<- (m.(i)+m'.(i));
  done;
  m''


let compare_mon m m' =
  let d = nvar m in
  if !lexico
  then (
    (* Comparaison de monomes avec ordre du degre lexicographique = on commence par regarder la 1ere variable*)
    let res=ref 0 in
    let i=ref 1 in (* 1 si lexico pur 0 si degre*)
    while (!res=0) && (!i<=d) do
      res:= (compare m.(!i) m'.(!i));
      i:=!i+1;
    done;
    !res)
  else (
     (* degre lexicographique inverse *)
    match compare m.(0) m'.(0) with
    | 0 -> (* meme degre total *)
	let res=ref 0 in
	let i=ref d in
	while (!res=0) && (!i>=1) do
	  res:= - (compare m.(!i) m'.(!i));
	  i:=!i-1;
	done;
	!res
    | x -> x)

let div_mon m m' =
  let d = nvar m in
  let m'' = Array.make (d+1) 0 in
  for i=0 to d do
    m''.(i)<- (m.(i)-m'.(i));
  done;
  m''

let div_pol_coef p c =
  List.map (fun (a,m) -> (P.divP a c,m)) p

(* m' divides m  *)
let div_mon_test m m' =
  let d = nvar m in
  let res=ref true in
  let i=ref 0 in (*il faut que le degre total soit bien mis sinon, i=ref 1*)
  while (!res) && (!i<=d) do
    res:= (m.(!i) >= m'.(!i));
    i:=succ !i;
  done;
  !res

let set_deg m =
  let d = nvar m in
  m.(0)<-0;
  for i=1 to d do
    m.(0)<-  m.(i)+m.(0);
  done;
  m

(* lcm *)
let ppcm_mon m m' =
  let d = nvar m in
  let m'' = Array.make (d+1) 0 in
  for i=1 to d do
    m''.(i)<- (max m.(i) m'.(i));
  done;
  set_deg m''



(**********************************************************************
  Polynomials
  list of (coefficient, monomial) decreasing order 
*)

let repr p = p

let equal =
  Util.List.for_all2eq
    (fun (c1,m1) (c2,m2) -> P.equal c1 c2 && m1=m2)

let hash p =
  let c = List.map fst p in
  let m = List.map snd p in
  List.fold_left (fun h p -> h * 17 + P.hash p) (Hashtbl.hash m) c

module Hashpol = Hashtbl.Make(
  struct
    type t = poly
    let equal = equal
    let hash = hash
  end)


(* A pretty printer for polynomials, with Maple-like syntax. *)

open Format

let getvar lv i =
  try (List.nth lv i)
  with Failure _ -> (List.fold_left (fun r x -> r^" "^x) "lv= " lv)
    ^" i="^(string_of_int i)

let string_of_pol zeroP hdP tlP coefterm monterm string_of_coef
    dimmon string_of_exp lvar p =


  let rec string_of_mon m coefone =
    let s=ref [] in
    for i=1 to (dimmon m) do
      (match (string_of_exp m i) with
        "0" -> ()
      | "1" -> s:= (!s) @ [(getvar !lvar (i-1))]
      | e -> s:= (!s) @ [((getvar !lvar (i-1)) ^ "^" ^ e)]);
    done;
    (match !s with
      [] -> if coefone 
      then  "1"
      else ""
    | l -> if coefone 
    then  (String.concat "*" l)
    else ( "*" ^
           (String.concat "*" l)))
  and string_of_term t start = let a = coefterm t and m = monterm t in
  match (string_of_coef a) with
    "0" -> ""
  | "1" ->(match start with
      true -> string_of_mon m true
    |false -> ( "+ "^
                (string_of_mon m true)))
  | "-1" ->( "-" ^" "^(string_of_mon m true))
  | c -> if (String.get c 0)='-'
  then ( "- "^
         (String.sub c 1 
            ((String.length c)-1))^
         (string_of_mon m false))
  else (match start with
    true -> ( c^(string_of_mon m false))
  |false -> ( "+ "^
              c^(string_of_mon m false)))
  and stringP p start = 
    if (zeroP p)
    then (if start 
    then ("0")
    else "")
    else ((string_of_term (hdP p) start)^
          " "^
          (stringP (tlP p) false))
  in 
  (stringP p true)



let print_pol zeroP hdP tlP coefterm monterm string_of_coef
    dimmon string_of_exp lvar p =

  let rec print_mon m coefone =
    let s=ref [] in
    for i=1 to (dimmon m) do
      (match (string_of_exp m i) with
        "0" -> ()
      | "1" -> s:= (!s) @ [(getvar !lvar (i-1))]
      | e -> s:= (!s) @ [((getvar !lvar (i-1)) ^ "^" ^ e)]);
    done;
    (match !s with
      [] -> if coefone 
      then print_string "1"
      else ()
    | l -> if coefone 
    then print_string (String.concat "*" l)
    else (print_string "*"; 
          print_string (String.concat "*" l)))
  and print_term t start = let a = coefterm t and m = monterm t in
  match (string_of_coef a) with
    "0" -> ()
  | "1" ->(match start with
      true -> print_mon m true
    |false -> (print_string "+ ";
               print_mon m true))
  | "-1" ->(print_string "-";print_space();print_mon m true)
  | c -> if (String.get c 0)='-'
  then (print_string "- ";
        print_string (String.sub c 1 
                        ((String.length c)-1));
        print_mon m false)
  else (match start with
    true -> (print_string c;print_mon m false)
  |false -> (print_string "+ ";
             print_string c;print_mon m false))
  and printP p start = 
    if (zeroP p)
    then (if start 
    then print_string("0")
    else ())
    else (print_term (hdP p) start;
          if start then open_hovbox 0;
          print_space();
          print_cut();
          printP (tlP p) false)
  in open_hovbox 3;
  printP p true;
  print_flush()


let name_var= ref []

let stringP p =
  string_of_pol 
    (fun p -> match p with [] -> true | _ -> false)
    (fun p -> match p with (t::p) -> t |_ -> failwith "print_pol dans dansideal")
    (fun p -> match p with (t::p) -> p |_ -> failwith "print_pol dans dansideal")
    (fun (a,m) -> a)
    (fun (a,m) -> m)
    string_of_coef
    (fun m -> (Array.length m)-1)
    (fun m i -> (string_of_int (m.(i))))
    name_var
    p

let nsP2 = ref max_int

let stringPcut p =
  (*Polynomesrec.nsP1:=20;*)
  nsP2:=10;
  let res =
    if (List.length p)> !nsP2
    then (stringP [List.hd p])^" + "^(string_of_int (List.length p))^" terms"
    else  stringP p in
  (*Polynomesrec.nsP1:= max_int;*)
  nsP2:= max_int;
  res

let rec lstringP l =
  match l with
    [] -> ""
  |p::l -> (stringP p)^("\n")^(lstringP l)

let printP = print_pol 
    (fun p -> match p with [] -> true | _ -> false)
    (fun p -> match p with (t::p) -> t |_ -> failwith "print_pol dans dansideal")
    (fun p -> match p with (t::p) -> p |_ -> failwith "print_pol dans dansideal")
    (fun (a,m) -> a)
    (fun (a,m) -> m)
    string_of_coef
    (fun m -> (Array.length m)-1)
    (fun m i -> (string_of_int (m.(i))))
    name_var


let rec lprintP l =
  match l with
    [] -> ()
  |p::l -> printP p;print_string "\n"; lprintP l


(* Operations *)

let zeroP = []

(* returns a constant polynom ial with d variables *)
let polconst d c =
  let m = Array.make (d+1) 0 in
  let m = set_deg m in 
  [(c,m)]

let plusP p q =
  let rec plusP p q =
    match p with
      [] -> q
    |t::p' -> 
	match q with
	  [] -> p
	|t'::q' ->
            match compare_mon (snd t) (snd t') with
              1 -> t::(plusP p' q)
            |(-1) -> t'::(plusP p q')
            |_ -> let c=P.plusP (fst t) (fst t') in
              match P.equal c coef0 with
                true -> (plusP p' q')
              |false -> (c,(snd t))::(plusP p' q')
  in plusP p q

(* multiplication by (a,monomial) *)
let mult_t_pol a m p =
  let rec mult_t_pol p =
    match p with
      [] -> []
    |(b,m')::p -> ((P.multP a b),(mult_mon m m'))::(mult_t_pol p)
  in mult_t_pol p

let coef_of_int x = P.of_num (Num.Int x)

(* variable i *)
let gen d i =
  let m = Array.make (d+1) 0 in
  m.(i) <- 1;
  let m = set_deg m in 
  [((coef_of_int 1),m)]

let oppP p =
  let rec oppP p =
    match p with
      [] -> []
    |(b,m')::p -> ((P.oppP b),m')::(oppP p)
  in oppP p

(* multiplication by a coefficient *)
let emultP a p =
  let rec emultP p =
    match p with
      [] -> []
    |(b,m')::p -> ((P.multP a b),m')::(emultP p)
  in emultP p

let multP p q =
  let rec aux p =
    match p with
      [] -> []
    |(a,m)::p' -> plusP (mult_t_pol a m q) (aux p')
  in aux p

let puisP p n=
  match p with
    [] -> []
  |_ ->
      let d = nvar (snd (List.hd p)) in
      let rec puisP n =
	match n with
	  0 -> [coef1, Array.make (d+1) 0]
	| 1 -> p
	|_ -> multP p (puisP (n-1))
      in puisP n
	
let rec contentP p =
  match p with
  |[] -> coef1
  |[a,m] -> a
  |(a,m)::p1 ->
      if P.equal a coef1 || P.equal a coefm1
      then a
      else P.pgcdP a (contentP p1)

let contentPlist lp =
  match lp with
  |[] -> coef1
  |p::l1 ->
      List.fold_left
	(fun r q ->
	  if P.equal r coef1 || P.equal r coefm1
	  then r
	  else P.pgcdP r (contentP q))
	(contentP p) l1
	
(***********************************************************************
   Division of polynomials
 *)

let pgcdpos a b  = P.pgcdP a b

let polynom0 =  {pol = ref []; num = 0; sugar = 0}
   
let ppol p = !(p.pol)

let lm p = snd (List.hd (ppol p))

let nallpol = ref 0

let allpol = ref (Array.make 1000 polynom0)

let new_allpol p s =
  nallpol := !nallpol + 1;
  if !nallpol >= Array.length !allpol
  then
    allpol := Array.append !allpol (Array.make !nallpol polynom0);
  let p = {pol = ref p; num = !nallpol; sugar = s} in
  !allpol.(!nallpol)<- p;
  p

(* returns a polynomial of l whose head monomial divides m, else [] *)

let rec selectdiv m l =
  match l with
    [] -> polynom0
  |q::r -> let m'= snd (List.hd (ppol q)) in
    match (div_mon_test m m') with
      true -> q
    |false -> selectdiv m r

let div_pol p q a b m = 
(*  info ".";*)
  plusP (emultP a p) (mult_t_pol b m q)

let hmon = Hashtbl.create 1000

let use_hmon = ref false

let find_hmon m =
  if !use_hmon
  then Hashtbl.find hmon m
  else raise Not_found

let add_hmon m q =
  if !use_hmon
  then Hashtbl.add hmon m q
  else ()

let div_coef a b = P.divP a b


(* remainder r of the division of p by polynomials of l, returns (c,r) where c is the coefficient for pseudo-division : c p = sum_i q_i p_i + r *)

let reduce2 p l =
  let l = if nouveaux_pol_en_tete then List.rev l else l in
  let rec reduce p =
    match p with
      [] -> (coef1,[])
    |t::p' ->
	let (a,m)=t in
      let q = (try find_hmon m 
      with Not_found -> 
	let q = selectdiv m l in
	match (ppol q) with 
          t'::q' -> (add_hmon m q;
		     q)
	|[] -> q) in
      match (ppol q) with
	[] -> if reduire_les_queues
	then
	  let (c,r)=(reduce p') in
          (c,((P.multP a c,m)::r))
	else (coef1,p)
      |(b,m')::q' -> 
          let c=(pgcdpos a b) in
          let a'= (div_coef b c) in
          let b'=(P.oppP (div_coef a c)) in
          let (e,r)=reduce (div_pol p' q' a' b'
                              (div_mon m m')) in
          (P.multP a' e,r)
  in let (c,r) = reduce p in
  (c,r)

(* trace of divisions *)

(* list of initial polynomials *)
let poldep = ref [] 
let poldepcontent = ref []

(* coefficients of polynomials when written with initial polynomials *)
let coefpoldep = Hashtbl.create 51

(* coef of q in p = sum_i c_i*q_i *)
let coefpoldep_find p q =
  try (Hashtbl.find coefpoldep (p.num,q.num))
  with Not_found -> []

let coefpoldep_remove p q =
  Hashtbl.remove coefpoldep (p.num,q.num)

let coefpoldep_set p q c =
  Hashtbl.add coefpoldep (p.num,q.num) c

let initcoefpoldep d lp =
  poldep:=lp;
  poldepcontent:= List.map (fun p -> contentP (ppol p)) lp;
  List.iter
    (fun p -> coefpoldep_set p p (polconst d (coef_of_int 1)))
    lp

(* keeps trace in coefpoldep 
   divides without pseudodivisions *)

let reduce2_trace p l lcp =
  let l = if nouveaux_pol_en_tete then List.rev l else l in
  (* rend (lq,r), ou r = p + sum(lq) *)
  let rec reduce p =
    match p with
      [] -> ([],[])
    |t::p' ->
	let (a,m)=t in
      let q =
	(try find_hmon m 
	with Not_found -> 
	  let q = selectdiv m l in
	  match (ppol q) with 
            t'::q' -> (add_hmon m q;
		       q)
          |[] -> q) in
      match (ppol q) with
	[] ->
	  if reduire_les_queues
	  then
	    let (lq,r)=(reduce p') in
            (lq,((a,m)::r))
	  else ([],p)
      |(b,m')::q' -> 
          let b'=(P.oppP (div_coef a b)) in
          let m''= div_mon m m' in
          let p1=plusP p' (mult_t_pol b' m'' q') in
          let (lq,r)=reduce p1 in
          ((b',m'',q)::lq, r)
  in let (lq,r) = reduce p in
  (*info "reduce2_trace:\n";
     iter
     (fun (a,m,s) ->
     let x = mult_t_pol a m s in
     info ((stringP x)^"\n"))
     lq;
     info "ok\n";*)
  (List.map2
     (fun c0 q ->
       let c =
	 List.fold_left
	   (fun x (a,m,s) ->
	     if equal (ppol s) (ppol q)
	     then
	       plusP x (mult_t_pol a m (polconst (nvar m) (coef_of_int 1)))
	     else x)
	   c0
	   lq in
       c)
     lcp
     !poldep,
   r)     

let homogeneous = ref false
let pol_courant = ref polynom0

(***********************************************************************
   Completion
 *)

let sugar_flag = ref true

let compute_sugar p =
  List.fold_left (fun s (a,m) -> max s m.(0)) 0 p

let mk_polynom p = 
  new_allpol p (compute_sugar p)

let spol ps qs=
  let p = ppol ps in
  let q = ppol qs in
  let m = snd (List.hd p) in
  let m'= snd (List.hd q) in
  let a = fst (List.hd p) in
  let b = fst (List.hd q) in
  let p'= List.tl p in
  let q'= List.tl q in
  let c = (pgcdpos a b) in
  let m''=(ppcm_mon m m') in
  let m1 = div_mon m'' m in
  let m2 = div_mon m'' m' in
  let fsp p' q' =
    plusP 
      (mult_t_pol 
	 (div_coef b c)
	 m1 p')
      (mult_t_pol 
	 (P.oppP (div_coef a c))
         m2 q') in
  let sp = fsp p' q' in
  let sps =
    new_allpol
      sp
      (max (m1.(0) + ps.sugar) (m2.(0) + qs.sugar)) in
  coefpoldep_set sps ps (fsp (polconst (nvar m) (coef_of_int 1)) []);
  coefpoldep_set sps qs (fsp [] (polconst (nvar m) (coef_of_int 1)));
  sps
  

let etrangers p p'=
  let m = snd (List.hd p) in
  let m'= snd (List.hd p') in
  let d = nvar m in
  let res=ref true in
  let i=ref 1 in
  while (!res) && (!i<=d) do
    res:= (m.(!i) = 0) || (m'.(!i)=0);
      i:=!i+1;
  done;
  !res

(* teste if head monomial of p'' divides lcm of lhead monomials of p and p' *)

let div_ppcm p p' p'' =
  let m = snd (List.hd p) in
  let m'= snd (List.hd p') in
  let m''= snd (List.hd p'') in
  let d = nvar m in
  let res=ref true in
  let i=ref 1 in
  while (!res) && (!i<=d) do
    res:= ((max m.(!i) m'.(!i)) >= m''.(!i));
    i:=!i+1;
  done;
  !res

(* code from extraction of Laurent Théry Coq program *)

type 'poly cpRes =
    Keep of ('poly list)
  | DontKeep of ('poly list)

let list_rec f0 f1 =
  let rec f2 = function
      [] -> f0
    | a0::l0 -> f1 a0 l0 (f2 l0)
  in f2

let addRes i = function
    Keep h'0 -> Keep (i::h'0)
  | DontKeep h'0 -> DontKeep (i::h'0)

let slice i a q =
  list_rec
    (match etrangers (ppol i) (ppol a) with
      true -> DontKeep []
    | false -> Keep [])
    (fun b q1 rec_ren ->
      match div_ppcm (ppol i) (ppol a) (ppol b) with
	true ->  DontKeep (b::q1)
      | false ->
          (match div_ppcm (ppol i) (ppol b) (ppol a) with
            true -> rec_ren
          | false -> addRes b rec_ren)) q

(* sugar strategy *)

let addS x l =    l @ [x] (* oblige de mettre en queue sinon le certificat deconne *)
			  
let addSsugar x l =
  if !sugar_flag
  then 
    let sx = x.sugar in
    let rec insere l  =
      match l with
      | [] -> [x]
      | y::l1 ->
	  if sx <= y.sugar
	  then x::l
	  else y::(insere l1)
    in insere l
  else addS x l

(* ajoute les spolynomes de i avec la liste de polynomes aP, 
   a la liste q *)

let genPcPf i aP q =
  (let rec genPc aP0 =
    match aP0 with
      [] -> (fun r -> r)
    | a::l1 -> 
	(fun l ->
          (match slice i a l1 with
            Keep l2 -> addSsugar (spol i a) (genPc l2 l)
          | DontKeep l2 -> genPc l2 l))
  in genPc aP) q

let genOCPf h' =
  list_rec [] (fun a l rec_ren ->
    genPcPf a l rec_ren) h'
    
(***********************************************************************
 critical pairs/s-polynomials
 *)
    
let ordcpair ((i1,j1),m1) ((i2,j2),m2) =
(*  let s1 = (max
	      (!allpol.(i1).sugar + m1.(0)
		   - (snd (hd (ppol !allpol.(i1)))).(0))
	      (!allpol.(j1).sugar + m1.(0)
		   - (snd (hd (ppol !allpol.(j1)))).(0))) in 
  let s2 = (max
	      (!allpol.(i2).sugar + m2.(0)
		   - (snd (hd (ppol !allpol.(i2)))).(0))
	      (!allpol.(j2).sugar + m2.(0)
		   - (snd (hd (ppol !allpol.(j2)))).(0))) in 
  match compare s1 s2 with
  | 1 -> 1
  |(-1) -> -1
  |0 ->  compare_mon m1 m2*)

  compare_mon m1 m2 

let sortcpairs lcp = 
  List.sort ordcpair lcp

let mergecpairs l1 l2 =
  List.merge ordcpair l1 l2 

let ord i j =
  if i<j then (i,j) else (j,i)
    
let cpair p q =
  if etrangers (ppol p) (ppol q)
  then []
  else [(ord p.num q.num,
	 ppcm_mon (lm p) (lm q))]
      
let cpairs1 p lq =
  sortcpairs (List.fold_left (fun r q -> r @ (cpair p q)) [] lq)
    
let cpairs lp =
  let rec aux l =
    match l with
      []|[_] -> []
    |p::l1 -> mergecpairs (cpairs1 p l1) (aux l1)
  in aux lp
    
    
let critere2 ((i,j),m) lp lcp =
  List.exists
    (fun h ->
      h.num <> i && h.num <> j
        && (div_mon_test m (lm h))
	&& (let c1 = ord i h.num in
	not (List.exists (fun (c,_) -> c1 = c) lcp))
	&& (let c1 = ord j h.num in
	not (List.exists (fun (c,_) -> c1 = c) lcp)))
    lp

let critere3 ((i,j),m) lp lcp =
  List.exists
    (fun h ->
      h.num <> i && h.num <> j
        && (div_mon_test m (lm h))
	&& (h.num < j
	   || not (m = ppcm_mon 
		   (lm (!allpol.(i)))
		   (lm h)))
	&& (h.num < i
	  || not (m = ppcm_mon 
		   (lm (!allpol.(j)))
		   (lm h))))
    lp

let add_cpairs p lp lcp =
  mergecpairs (cpairs1 p lp) lcp 

let step = ref 0

let infobuch p q =
  if !step = 0 
  then (info ("[" ^ (string_of_int (List.length p))
              ^ "," ^  (string_of_int (List.length q))
              ^ "]"))

(* in lp new polynomials are at the end *)

let coef_courant = ref coef1

type certificate =
    { coef : coef; power : int;
      gb_comb : poly list list; last_comb : poly list }

let test_dans_ideal p lp lp0 =
  let (c,r) = reduce2 (ppol !pol_courant) lp in
  info ("remainder: "^(stringPcut r)^"\n");
  coef_courant:= P.multP !coef_courant c;
  pol_courant:= mk_polynom r;
  if r=[]
  then (info "polynomial reduced to 0\n";
	let lcp = List.map (fun q -> []) !poldep in
	let c = !coef_courant in
	let (lcq,r) = reduce2_trace (emultP c p) lp lcp in
	info "r ok\n";
	info ("r: "^(stringP r)^"\n");
        let res=ref  (emultP c p) in
	List.iter2
	  (fun cq q -> res:=plusP (!res) (multP cq (ppol q));
	  )
	  lcq !poldep;
	info ("verif sum: "^(stringP (!res))^"\n");
	info ("coefficient: "^(stringP (polconst 1 c))^"\n");
	let rec aux lp =
	  match lp with
	  |[] -> []
	  |p::lp ->
	      (List.map
		 (fun q -> coefpoldep_find p q)
		 lp)::(aux lp)
	in
	let coefficient_multiplicateur = c in
	let liste_polynomes_de_depart = List.rev lp0 in
	let polynome_a_tester = p in
	let liste_des_coefficients_intermediaires =
	  (let lci = List.rev (aux (List.rev lp)) in
	  let lci = ref lci (* (map rev lci) *) in
	  List.iter (fun x -> lci := List.tl (!lci)) lp0;
	  !lci) in
	let liste_des_coefficients =
	  List.map
	    (fun cq -> emultP (coef_of_int (-1)) cq)
	    (List.rev lcq) in
	(liste_polynomes_de_depart,
	 polynome_a_tester,
	 {coef = coefficient_multiplicateur;
	  power = 1;
	  gb_comb = liste_des_coefficients_intermediaires;
	  last_comb = liste_des_coefficients})
       )
  else ((*info "polynomial not reduced to 0\n";
	   info ("\nremainder: "^(stringPcut r)^"\n");*)
    raise NotInIdeal)
      
let divide_rem_with_critical_pair = ref false

let list_diff l x =
  List.filter (fun y -> y <> x) l

let deg_hom p =
  match p with
  | [] -> -1
  | (a,m)::_ -> m.(0)

let pbuchf pq p lp0=
  info "computation of the Groebner basis\n";
  step:=0;
  Hashtbl.clear hmon;
  let rec pbuchf (lp, lpc) =
      infobuch lp lpc;
(*      step:=(!step+1)mod 10;*)
      match lpc with
        [] ->
	  
	 (* info ("List of polynomials:\n"^(fold_left (fun r p -> r^(stringP p)^"\n") "" lp));
	  info "--------------------\n";*)
	  test_dans_ideal (ppol p) lp lp0
      | ((i,j),m) :: lpc2 ->
(*          info "choosen pair\n";*)
	  if critere3 ((i,j),m) lp lpc2
	  then (info "c"; pbuchf (lp, lpc2))
	  else    
	    let a = spol !allpol.(i) !allpol.(j) in
	    if !homogeneous && (ppol a)<>[] && deg_hom (ppol a)
		> deg_hom (ppol !pol_courant)
	    then (info "h"; pbuchf (lp, lpc2))
	    else
(*	      let sa = a.sugar in*)
              let (ca,a0)= reduce2 (ppol a) lp in
              match a0 with
		[] -> info "0";pbuchf (lp, lpc2)
              | _ ->
(*		info "pair reduced\n";*)
		  a.pol := emultP ca (ppol a);
		  let (lca,a0) = reduce2_trace (ppol a) lp
		      (List.map (fun q -> emultP ca (coefpoldep_find a q))
			 !poldep) in
(*		info "paire re-reduced";*)
		  a.pol := a0;
(*		  let a0 = new_allpol a0 sa in*)
		  List.iter2 (fun c q ->
		    coefpoldep_remove a q;
		    coefpoldep_set a q c) lca !poldep;
		  let a0 = a in
		  info ("\nnew polynomial: "^(stringPcut (ppol a0))^"\n");
		  let ct = coef1 (* contentP a0 *) in
		  (*info ("content: "^(string_of_coef ct)^"\n");*)
		  poldep:=addS a0 lp;
		  poldepcontent:=addS ct (!poldepcontent);
		  
		  try test_dans_ideal (ppol p) (addS a0 lp) lp0
		  with NotInIdeal ->
		    let newlpc = add_cpairs a0 lp lpc2 in
		    pbuchf (((addS a0 lp), newlpc))
  in pbuchf pq
    
let is_homogeneous p =
  match p with
  | [] -> true
  | (a,m)::p1 -> let d = m.(0) in
    List.for_all (fun (b,m') -> m'.(0)=d) p1
    
(* returns
   c
   lp = [pn;...;p1]
   p
   lci = [[a(n+1,n);...;a(n+1,1)];
   [a(n+2,n+1);...;a(n+2,1)];
   ...
   [a(n+m,n+m-1);...;a(n+m,1)]]
   lc = [qn+m; ... q1]

   such that
   c*p = sum qi*pi 
   where pn+k = a(n+k,n+k-1)*pn+k-1 + ... + a(n+k,1)* p1
 *)

let in_ideal d lp p =
  Hashtbl.clear hmon;
  Hashtbl.clear coefpoldep;
  nallpol := 0;
  allpol := Array.make 1000 polynom0;
  homogeneous := List.for_all is_homogeneous (p::lp);
  if !homogeneous then info "homogeneous polynomials\n";
  info ("p: "^(stringPcut p)^"\n");
  info ("lp:\n"^(List.fold_left (fun r p -> r^(stringPcut p)^"\n") "" lp));
  (*info ("p: "^(stringP p)^"\n");
  info ("lp:\n"^(fold_left (fun r p -> r^(stringP p)^"\n") "" lp));*)

  let lp = List.map mk_polynom lp in
  let p = mk_polynom p in
  initcoefpoldep d lp;
  coef_courant:=coef1;
  pol_courant:=p;

  let (lp1,p1,cert) =
    try test_dans_ideal (ppol p) lp lp
    with NotInIdeal -> pbuchf (lp, (cpairs lp)) p lp in
  info "computed\n";

  (List.map ppol lp1, p1, cert)
    
(* *)
end

	

