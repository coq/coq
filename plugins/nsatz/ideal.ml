(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Nullstellensatz with Groebner basis computation

We use a sparse representation for polynomials:
a monomial is an array of exponents (one for each variable)
with its degree in head
a polynomial is a sorted list of (coefficient, monomial)

 *)

open Utile

exception NotInIdeal

(***********************************************************************
   Global options
*)
let lexico = ref false

(* division of tail monomials *)

let reduire_les_queues = false

(* divide first with new polynomials *)

let nouveaux_pol_en_tete = false

type metadata = {
  name_var : string list;
}

module Monomial :
sig
type t
val repr : t -> int array
val make : int array -> t
val deg : t -> int
val nvar : t -> int
val var_mon : int -> int -> t
val mult_mon : t -> t -> t
val compare_mon : t -> t -> int
val div_mon : t -> t -> t
val div_mon_test : t -> t -> bool
val ppcm_mon : t -> t -> t
val const_mon : int -> t
end =
struct
type t = int array
type mon = t
let repr m = m
let make m = m
let nvar (m : mon) =  Array.length m - 1

let deg (m : mon) = m.(0)

let mult_mon (m : mon) (m' : mon) =
  let d = nvar m in
  let m'' = Array.make (d+1) 0 in
  for i=0 to d do
    m''.(i)<- (m.(i)+m'.(i));
  done;
  m''


let compare_mon (m : mon) (m' : mon) =
  let d = nvar m in
  if !lexico
  then (
    (* Comparaison de monomes avec ordre du degre lexicographique = on commence par regarder la 1ere variable*)
    let res=ref 0 in
    let i=ref 1 in (* 1 si lexico pur 0 si degre*)
    while (!res=0) && (!i<=d) do
      res:= (Int.compare m.(!i) m'.(!i));
      i:=!i+1;
    done;
    !res)
  else (
     (* degre lexicographique inverse *)
    match Int.compare m.(0) m'.(0) with
    | 0 -> (* meme degre total *)
	let res=ref 0 in
	let i=ref d in
	while (!res=0) && (!i>=1) do
	  res:= - (Int.compare m.(!i) m'.(!i));
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

(* returns a constant polynom ial with d variables *)
let const_mon d =
  let m = Array.make (d+1) 0 in
  let m = set_deg m in 
  m

let var_mon d i =
  let m = Array.make (d+1) 0 in
  m.(i) <- 1;
  let m = set_deg m in 
  m

end

(***********************************************************************
   Functor
*)

module Make (P:Polynom.S) = struct

  type coef = P.t
  let coef0 = P.of_num (Num.Int 0)
  let coef1 = P.of_num (Num.Int 1)
  let string_of_coef c = "["^(P.to_string c)^"]"

(***********************************************************************
   Monomials
 array of integers, first is the degree
*)

open Monomial

type mon = Monomial.t
type deg = int
type poly = (coef * mon) list
type polynom = {
  pol : poly;
  num : int;
}

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
      | "1" -> s:= (!s) @ [(getvar lvar (i-1))]
      | e -> s:= (!s) @ [((getvar lvar (i-1)) ^ "^" ^ e)]);
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

let stringP metadata (p : poly) =
  string_of_pol 
    (fun p -> match p with [] -> true | _ -> false)
    (fun p -> match p with (t::p) -> t |_ -> failwith "print_pol dans dansideal")
    (fun p -> match p with (t::p) -> p |_ -> failwith "print_pol dans dansideal")
    (fun (a,m) -> a)
    (fun (a,m) -> m)
    string_of_coef
    (fun m -> (Array.length (Monomial.repr m))-1)
    (fun m i -> (string_of_int ((Monomial.repr m).(i))))
    metadata.name_var
    p

let nsP2 = 10

let stringPcut metadata (p : poly) =
  (*Polynomesrec.nsP1:=20;*)
  let res =
    if (List.length p)> nsP2
    then (stringP metadata [List.hd p])^" + "^(string_of_int (List.length p))^" terms"
    else  stringP metadata p in
  (*Polynomesrec.nsP1:= max_int;*)
  res

(* Operations *)

let zeroP = []

(* returns a constant polynom ial with d variables *)
let polconst d c =
  let m = const_mon d in
  [(c,m)]

let plusP p q =
  let rec plusP p q accu = match p, q with
  | [], [] -> List.rev accu
  | [], _ -> List.rev_append accu q
  | _, [] -> List.rev_append accu p
  | t :: p', t' :: q' ->
    let c = compare_mon (snd t) (snd t') in
    if c > 0 then plusP p' q (t :: accu)
    else if c < 0 then plusP p q' (t' :: accu)
    else
      let c = P.plusP (fst t) (fst t') in
      if P.equal c coef0 then plusP p' q' accu
      else plusP p' q' ((c, (snd t)) :: accu)
  in
  plusP p q []

(* multiplication by (a,monomial) *)
let mult_t_pol a m p =
  let map (b, m') = (P.multP a b, mult_mon m m') in
  CList.map map p

let coef_of_int x = P.of_num (Num.Int x)

(* variable i *)
let gen d i =
  let m = var_mon d i in 
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
  let rec aux p accu =
    match p with
      [] -> accu
    |(a,m)::p' -> aux p' (plusP (mult_t_pol a m q) accu)
  in aux p []

let puisP p n=
  match p with
    [] -> []
  |_ ->
    if n = 0 then
      let d = nvar (snd (List.hd p)) in
      [coef1, const_mon d]
    else
      let rec puisP p n =
        if n = 1 then p
        else
          let q = puisP p (n / 2) in
          let q = multP q q in
          if n mod 2 = 0 then q else multP p q
      in puisP p n
	
(***********************************************************************
   Division of polynomials
 *)

type table = {
  hmon : (mon, poly) Hashtbl.t option;
  (* coefficients of polynomials when written with initial polynomials *)
  coefpoldep : ((int * int), poly) Hashtbl.t;
  mutable nallpol : int;
  mutable allpol : polynom array;
  (* list of initial polynomials *)
}

let pgcdpos a b  = P.pgcdP a b

let polynom0 = { pol = []; num = 0 }
   
let ppol p = p.pol

let lm p = snd (List.hd (ppol p))

let new_allpol table p =
  table.nallpol <- table.nallpol + 1;
  if table.nallpol >= Array.length table.allpol
  then
    table.allpol <- Array.append table.allpol (Array.make table.nallpol polynom0);
  let p = { pol = p; num = table.nallpol } in
  table.allpol.(table.nallpol) <- p;
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
  plusP (emultP a p) (mult_t_pol b m q)

let find_hmon table m = match table.hmon with
| None -> raise Not_found
| Some hmon -> Hashtbl.find hmon m

let add_hmon table m q =
match table.hmon with
| None -> ()
| Some hmon -> Hashtbl.add hmon m q

let selectdiv table m l =
  try find_hmon table m
  with Not_found ->
    let q = selectdiv m l in
    let q = ppol q in
    match q with
    | [] -> q
    | _ :: _ ->
      let () = add_hmon table m q in
      q

let div_coef a b = P.divP a b


(* remainder r of the division of p by polynomials of l, returns (c,r) where c is the coefficient for pseudo-division : c p = sum_i q_i p_i + r *)

let reduce2 table p l =
  let l = if nouveaux_pol_en_tete then List.rev l else l in
  let rec reduce p =
    match p with
      [] -> (coef1,[])
    |t::p' ->
	let (a,m)=t in
      let q = selectdiv table m l in
      match q with
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

(* coef of q in p = sum_i c_i*q_i *)
let coefpoldep_find table p q =
  try (Hashtbl.find table.coefpoldep (p.num,q.num))
  with Not_found -> []

let coefpoldep_set table p q c =
  Hashtbl.add table.coefpoldep (p.num,q.num) c

(* keeps trace in coefpoldep 
   divides without pseudodivisions *)

let reduce2_trace table p l lcp =
  let lp = l in
  let l = if nouveaux_pol_en_tete then List.rev l else l in
  (* rend (lq,r), ou r = p + sum(lq) *)
  let rec reduce p =
    match p with
      [] -> ([],[])
    |t::p' ->
	let (a,m)=t in
      let q = selectdiv table m l in
      match q with
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
  (List.map2
     (fun c0 q ->
       let c =
	 List.fold_left
	   (fun x (a,m,s) ->
	     if equal s (ppol q)
	     then
	       plusP x (mult_t_pol a m (polconst (nvar m) (coef_of_int 1)))
	     else x)
	   c0
	   lq in
       c)
     lcp
     lp,
   r)     

(***********************************************************************
   Completion
 *)

let spol0 ps qs=
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
  let p0 = fsp (polconst (nvar m) (coef_of_int 1)) [] in
  let q0 = fsp [] (polconst (nvar m) (coef_of_int 1)) in
  (sp, p0, q0)

let etrangers p p'=
  let m = snd (List.hd p) in
  let m'= snd (List.hd p') in
  let d = nvar m in
  let res=ref true in
  let i=ref 1 in
  while (!res) && (!i<=d) do
    res:= ((Monomial.repr m).(!i) = 0) || ((Monomial.repr m').(!i)=0);
      i:=!i+1;
  done;
  !res

let addS x l =    l @ [x] (* oblige de mettre en queue sinon le certificat deconne *)

(***********************************************************************
 critical pairs/s-polynomials
 *)

module CPair =
struct
type t = (int * int) * Monomial.t
let compare ((i1, j1), m1) ((i2, j2), m2) = compare_mon m2 m1
end

module Heap :
sig
  type elt = (int * int) * Monomial.t
  type t
  val length : t -> int
  val empty : t
  val add : elt -> t -> t
  val pop : t -> (elt * t) option
end =
struct
  include Heap.Functional(CPair)
  let length h = fold (fun _ accu -> accu + 1) h 0
  let pop h = try Some (maximum h, remove h) with Heap.EmptyHeap -> None
end

let ord i j =
  if i<j then (i,j) else (j,i)
    
let cpair p q accu =
  if etrangers (ppol p) (ppol q) then accu
  else Heap.add (ord p.num q.num, ppcm_mon (lm p) (lm q)) accu

let cpairs1 p lq accu =
  List.fold_left (fun r q -> cpair p q r) accu lq

let rec cpairs l accu = match l with
| [] | [_] -> accu
| p :: l ->
  cpairs l (cpairs1 p l accu)

let critere3 table ((i,j),m) lp lcp =
  List.exists
    (fun h ->
      h.num <> i && h.num <> j
        && (div_mon_test m (lm h))
	&& (h.num < j
	   || not (m = ppcm_mon 
		   (lm (table.allpol.(i)))
		   (lm h)))
	&& (h.num < i
	  || not (m = ppcm_mon 
		   (lm (table.allpol.(j)))
		   (lm h))))
    lp

let infobuch p q =
  (info (fun () -> Printf.sprintf "[%i,%i]" (List.length p) (Heap.length q)))

(* in lp new polynomials are at the end *)

type certificate =
    { coef : coef; power : int;
      gb_comb : poly list list; last_comb : poly list }

type current_problem = {
  cur_poly : poly;
  cur_coef : coef;
}

exception NotInIdealUpdate of current_problem

let test_dans_ideal cur_pb table metadata p lp len0 =
  (** Invariant: [lp] is [List.tl (Array.to_list table.allpol)] *)
  let (c,r) = reduce2 table cur_pb.cur_poly lp in
  info (fun () -> "remainder: "^(stringPcut metadata r));
  let cur_pb = {
    cur_coef = P.multP cur_pb.cur_coef c;
    cur_poly = r;
  } in
  match r with
  | [] ->
    sinfo "polynomial reduced to 0";
    let lcp = List.map (fun q -> []) lp in
    let c = cur_pb.cur_coef in
    let (lcq,r) = reduce2_trace table (emultP c p) lp lcp in
    sinfo "r ok";
    info (fun () -> "r: "^(stringP metadata r));
    info (fun () ->
      let fold res cq q = plusP res (multP cq (ppol q)) in
      let res = List.fold_left2 fold (emultP c p) lcq lp in
      "verif sum: "^(stringP metadata res)
    );
    info (fun () -> "coefficient: "^(stringP metadata (polconst 1 c)));
    let coefficient_multiplicateur = c in
    let liste_des_coefficients_intermediaires =
      let rec aux accu lp =
        match lp with
        | [] -> accu
        | p :: lp ->
          let elt = List.map (fun q -> coefpoldep_find table p q) lp in
          aux (elt :: accu) lp
      in
      let lci = aux [] (List.rev lp) in
      CList.skipn len0 lci
    in
    let liste_des_coefficients =
      List.rev_map (fun cq -> emultP (coef_of_int (-1)) cq) lcq
    in
      {coef = coefficient_multiplicateur;
      power = 1;
      gb_comb = liste_des_coefficients_intermediaires;
      last_comb = liste_des_coefficients}
  | _ -> raise (NotInIdealUpdate cur_pb)

let deg_hom p =
  match p with
  | [] -> -1
  | (a,m)::_ -> Monomial.deg m

let pbuchf table metadata cur_pb homogeneous (lp, lpc) p =
  (** Invariant: [lp] is [List.tl (Array.to_list table.allpol)] *)
  sinfo "computation of the Groebner basis";
  let () = match table.hmon with
  | None -> ()
  | Some hmon -> Hashtbl.clear hmon
  in
  let len0 = List.length lp in
  let rec pbuchf cur_pb (lp, lpc) =
      infobuch lp lpc;
      match Heap.pop lpc with
      | None ->
	  test_dans_ideal cur_pb table metadata p lp len0
      | Some (((i, j), m), lpc2) ->
	  if critere3 table ((i,j),m) lp lpc2
	  then (sinfo "c"; pbuchf cur_pb (lp, lpc2))
	  else    
	    let (a0, p0, q0) = spol0 table.allpol.(i) table.allpol.(j) in
	    if homogeneous && a0 <>[] && deg_hom a0 > deg_hom cur_pb.cur_poly
	    then (sinfo "h"; pbuchf cur_pb (lp, lpc2))
	    else
(*	      let sa = a.sugar in*)
              match reduce2 table a0 lp with
		_, [] -> sinfo "0";pbuchf cur_pb (lp, lpc2)
              | ca, _ :: _ ->
(*		info "pair reduced\n";*)
                  let map q =
                    let r =
                      if q.num == i then p0 else if q.num == j then q0 else []
                    in
                    emultP ca r
                  in
                  let lcp = List.map map lp in
                  let (lca, a0) = reduce2_trace table (emultP ca a0) lp lcp in
(*		info "paire re-reduced";*)
                  let a = new_allpol table a0 in
		  List.iter2 (fun c q -> coefpoldep_set table a q c) lca lp;
		  let a0 = a in
		  info (fun () -> "new polynomial: "^(stringPcut metadata (ppol a0)));
                  let nlp = addS a0 lp in
		  try test_dans_ideal cur_pb table metadata p nlp len0
		  with NotInIdealUpdate cur_pb ->
		    let newlpc = cpairs1 a0 lp lpc2 in
		    pbuchf cur_pb (nlp, newlpc)
  in pbuchf cur_pb (lp, lpc)
    
let is_homogeneous p =
  match p with
  | [] -> true
  | (a,m)::p1 -> let d = deg m in
    List.for_all (fun (b,m') -> deg m' =d) p1
    
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

let in_ideal metadata d lp p =
  let table = {
    hmon = None;
    coefpoldep = Hashtbl.create 51;
    nallpol = 0;
    allpol = Array.make 1000 polynom0;
  } in
  let homogeneous = List.for_all is_homogeneous (p::lp) in
  if homogeneous then sinfo "homogeneous polynomials";
  info (fun () -> "p: "^(stringPcut metadata p));
  info (fun () -> "lp:\n"^(List.fold_left (fun r p -> r^(stringPcut metadata p)^"\n") "" lp));

  let lp = List.map (fun c -> new_allpol table c) lp in
  List.iter (fun p -> coefpoldep_set table p p (polconst d (coef_of_int 1))) lp;
  let cur_pb = {
    cur_poly = p;
    cur_coef = coef1;
  } in

  let cert =
    try pbuchf table metadata cur_pb homogeneous (lp, Heap.empty) p
    with NotInIdealUpdate cur_pb ->
      try pbuchf table metadata cur_pb homogeneous (lp, cpairs lp Heap.empty) p
      with NotInIdealUpdate _ -> raise NotInIdeal
    in
  sinfo "computed";

  cert

end
