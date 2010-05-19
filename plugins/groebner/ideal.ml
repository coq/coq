(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*
   Nullstellensatz par calcul de base de Grobner

   On utilise une representation creuse des polynomes:
   un monome est un tableau d'exposants (un par variable),
   avec son degre en tete.
   un polynome est une liste de (coefficient,monome).

   L'algorithme de Buchberger a proprement parler est tire du code caml
   extrait du code Coq ecrit par L.Thery.

 *)

open Utile

(* NB: Loic is using a coding-style "let x::q = ... in ..." that
   produces lots of warnings about non-exhaustive pattern matchs.
   Even worse, it is not clear whether a [Match_failure] could
   happen (and be catched by a "with _ ->") or not. Loic told me
   it shouldn't happen.

   In a first time, I used a camlp4 extension (search history
   for lib/refutpat.ml4) for introducing an ad-hoc syntax
   "let* x::q = ...". This is now removed (too complex during
   porting to camlp4).

   Now, we simply use the following function that turns x::q
   into (x,q) and hence an irrefutable pattern. Yes, this adds
   a (small) cost since the intermediate pair is allocated
   (in opt, the cost might even be 0 due to inlining).
   If somebody want someday to remove this extra cost,
   (x::q) could also be turned brutally into (x,q) by Obj.magic
   (beware: be sure no floats are around in this case).
*)

let of_cons = function
  | [] -> assert false
  | x::q -> x,q

exception NotInIdeal

module type S = sig

(* Monomials *)
type mon = int array

val mult_mon : int -> mon -> mon -> mon
val deg : mon -> int
val compare_mon : int -> mon -> mon -> int
val div_mon : int -> mon -> mon -> mon
val div_mon_test : int -> mon -> mon -> bool
val ppcm_mon : int -> mon -> mon -> mon

(* Polynomials *)

type deg = int
type coef
type poly
val repr : poly -> (coef * mon) list
val polconst : deg -> coef -> poly
val zeroP : poly
val gen : deg -> int -> poly

val equal : poly -> poly -> bool
val name_var : string list ref
val getvar : string list -> int -> string
val lstringP : poly list -> string
val printP : poly -> unit
val lprintP : poly list -> unit

val div_pol_coef : poly -> coef -> poly
val plusP : deg -> poly -> poly -> poly
val mult_t_pol : deg -> coef -> mon -> poly -> poly
val selectdiv : deg -> mon -> poly list -> poly
val oppP : poly -> poly
val emultP : coef -> poly -> poly
val multP : deg -> poly -> poly -> poly
val puisP : deg -> poly -> int -> poly
val contentP : poly -> coef
val contentPlist : poly list -> coef
val pgcdpos : coef -> coef -> coef
val div_pol : deg -> poly -> poly -> coef -> coef -> mon -> poly
val reduce2 : deg -> poly -> poly list -> coef * poly

val poldepcontent : coef list ref
val coefpoldep_find : poly -> poly -> poly
val coefpoldep_set : poly -> poly -> poly -> unit
val initcoefpoldep : deg -> poly list -> unit
val reduce2_trace : deg -> poly -> poly list -> poly list -> poly list * poly
val spol : deg -> poly -> poly -> poly
val etrangers : deg -> poly -> poly -> bool
val div_ppcm : deg -> poly -> poly -> poly -> bool

val genPcPf : deg -> poly -> poly list -> poly list -> poly list
val genOCPf : deg -> poly list -> poly list

val is_homogeneous : poly -> bool

type certificate =
    { coef : coef; power : int;
      gb_comb : poly list list; last_comb : poly list }
val test_dans_ideal : deg -> poly -> poly list -> poly list ->
  poly list * poly * certificate
val in_ideal : deg -> poly list -> poly -> poly list * poly * certificate

end

(***********************************************************************
   Global options
*)
let lexico = ref false
let use_hmon = ref false

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
   Monomes
   tableau d'entiers
   le premier coefficient est le degre
 *)

type mon = int array
type deg = int
type poly = (coef * mon) list

(* d représente le nb de variables du monome *)

(* Multiplication de monomes ayant le meme nb de variables = d *)
let mult_mon d m m' =
  let m'' = Array.create (d+1) 0 in
  for i=0 to d do
    m''.(i)<- (m.(i)+m'.(i));
  done;
  m''

(* Degré d'un monome *)
let deg m = m.(0)


let compare_mon d m m' =
  if !lexico
  then (
    (* Comparaison de monomes avec ordre du degre lexicographique
       = on commence par regarder la 1ere variable*)
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

(* Division de monome ayant le meme nb de variables *)
let div_mon d m m' =
  let m'' = Array.create (d+1) 0 in
  for i=0 to d do
    m''.(i)<- (m.(i)-m'.(i));
  done;
  m''

let div_pol_coef p c =
  List.map (fun (a,m) -> (P.divP a c,m)) p

(* m' divise m  *)
let div_mon_test d m m' =
  let res=ref true in
  let i=ref 1 in
  while (!res) && (!i<=d) do
    res:= (m.(!i) >= m'.(!i));
    i:=succ !i;
  done;
  !res


(* Mise en place du degré total du monome *)
let set_deg d m =
  m.(0)<-0;
  for i=1 to d do
    m.(0)<-  m.(i)+m.(0);
  done;
  m


(* ppcm de monomes *)
let ppcm_mon d m m' =
  let m'' = Array.create (d+1) 0 in
  for i=1 to d do
    m''.(i)<- (max m.(i) m'.(i));
  done;
  set_deg d m''



(**********************************************************************

   Polynomes
   liste de couples (coefficient,monome) ordonnee en decroissant

 *)


let repr p = p

let equal =
  Util.list_for_all2eq
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


(*
   A pretty printer for polynomials, with Maple-like syntax.
 *)

open Format

let getvar lv i =
  try (List.nth lv i)
  with _ -> (List.fold_left (fun r x -> r^" "^x) "lv= " lv)
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

let stringP = string_of_pol
    (fun p -> match p with [] -> true | _ -> false)
    (fun p -> match p with (t::p) -> t |_ -> failwith "print_pol dans dansideal")
    (fun p -> match p with (t::p) -> p |_ -> failwith "print_pol dans dansideal")
    (fun (a,m) -> a)
    (fun (a,m) -> m)
    string_of_coef
    (fun m -> (Array.length m)-1)
    (fun m i -> (string_of_int (m.(i))))
    name_var


let stringPcut p =
  if (List.length p)>20
  then (stringP [List.hd p])^" + "^(string_of_int (List.length p))^" termes"
  else  stringP p

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


(* Operations
 *)

let zeroP = []

(* Retourne un polynome constant à d variables *)
let polconst d c =
  let m = Array.create (d+1) 0 in
  let m = set_deg d m in
  [(c,m)]



(* somme de polynomes= liste de couples (int,monomes) *)
let plusP d p q =
  let rec plusP p q =
    match p with
      [] -> q
    |t::p' ->
	match q with
	  [] -> p
	|t'::q' ->
            match compare_mon d (snd t) (snd t') with
              1 -> t::(plusP p' q)
            |(-1) -> t'::(plusP p q')
            |_ -> let c=P.plusP (fst t) (fst t') in
              match P.equal c coef0 with
                true -> (plusP p' q')
              |false -> (c,(snd t))::(plusP p' q')
  in plusP p q


(* multiplication d'un polynome par (a,monome) *)
let mult_t_pol d a m p =
  let rec mult_t_pol p =
    match p with
      [] -> []
    |(b,m')::p -> ((P.multP a b),(mult_mon d m m'))::(mult_t_pol p)
  in mult_t_pol p


(* Retourne un polynome de l dont le monome de tete divise m,  [] si rien *)
let rec selectdiv d m l =
  match l with
    [] -> []
  | q::r ->
      let m'= snd (List.hd q) in
      if div_mon_test d m m' then q else selectdiv d m r


(* Retourne un polynome générateur 'i' à d variables *)
let gen d i =
  let m = Array.create (d+1) 0 in
  m.(i) <- 1;
  let m = set_deg d m in
  [(coef1,m)]



(* oppose d'un polynome *)
let oppP p =
  let rec oppP p =
    match p with
      [] -> []
    |(b,m')::p -> ((P.oppP b),m')::(oppP p)
  in oppP p


(* multiplication d'un polynome par un coefficient par 'a' *)
let emultP a p =
  let rec emultP p =
    match p with
      [] -> []
    |(b,m')::p -> ((P.multP a b),m')::(emultP p)
  in emultP p


let multP d p q =
  let rec aux p =
    match p with
      [] -> []
    |(a,m)::p' -> plusP d (mult_t_pol d a m q) (aux p')
  in aux p


let puisP d p n=
  let rec puisP n =
    match n with
      0 -> [coef1, Array.create (d+1) 0]
    | 1 -> p
    |_ -> multP d p (puisP (n-1))
  in puisP n

let pgcdpos a b  = P.pgcdP a b
let pgcd1 p q =
  if P.equal p coef1 || P.equal p coefm1 then p else P.pgcdP p q

let rec contentP p =
  match p with
  |[] -> coef1
  |[a,m] -> a
  |(a,m)::p1 -> pgcd1 a (contentP p1)

let contentPlist lp =
  match lp with
    |[] -> coef1
    |p::l1 -> List.fold_left (fun r q -> pgcd1 r (contentP q)) (contentP p) l1

(***********************************************************************
   Division de polynomes
 *)

let hmon = (Hashtbl.create 1000 : (mon,poly) Hashtbl.t)

let find_hmon m =
  if !use_hmon
  then Hashtbl.find hmon m
  else raise Not_found

let add_hmon m q =
  if !use_hmon then Hashtbl.add hmon m q

let selectdiv_cache d m l =
  try find_hmon m
  with Not_found ->
    match selectdiv d m l with
	[] -> []
      | q -> add_hmon m q; q

let div_pol d p q a b m =
(*  info ".";*)
  plusP d (emultP a p) (mult_t_pol d b m q)

(* si false on ne divise que le monome de tete *)
let reduire_les_queues = false

(* reste de la division de p par les polynomes de l
  rend le reste et le coefficient multiplicateur *)

let reduce2 d p l =
  let rec reduce p =
    match p with
      [] -> (coef1,[])
    | (a,m)::p' ->
      let q = selectdiv_cache d m l in
      (match q with
	[] ->
	  if reduire_les_queues
	  then
	    let (c,r)=(reduce p') in
            (c,((P.multP a c,m)::r))
	  else (coef1,p)
      |(b,m')::q' ->
          let c=(pgcdpos a b) in
          let a'= (P.divP b c) in
          let b'=(P.oppP (P.divP a c)) in
          let (e,r)=reduce (div_pol d p' q' a' b'
                              (div_mon d m m')) in
          (P.multP a' e,r)) in
  reduce p

(* trace des divisions *)

(* liste des polynomes de depart *)
let poldep = ref []
let poldepcontent = ref []


module HashPolPair = Hashtbl.Make
  (struct
     type t = poly * poly
     let equal (p,q) (p',q') = equal p p' && equal q q'
     let hash (p,q) =
       let c = List.map fst p @ List.map fst q in
       let m = List.map snd p @ List.map snd q in
       List.fold_left (fun h p -> h * 17 + P.hash p) (Hashtbl.hash m) c
   end)

(* table des coefficients des polynomes en fonction des polynomes de depart *)
let coefpoldep = HashPolPair.create 51

(* coefficient de q dans l expression de p = sum_i c_i*q_i *)
let coefpoldep_find p q =
  try (HashPolPair.find coefpoldep (p,q))
  with _ -> []

let coefpoldep_set p q c =
  HashPolPair.add coefpoldep (p,q) c

let initcoefpoldep d lp =
  poldep:=lp;
  poldepcontent:= List.map contentP (!poldep);
  List.iter
    (fun p -> coefpoldep_set p p (polconst d coef1))
    lp

(* garde la trace dans coefpoldep
   divise sans pseudodivisions *)

let reduce2_trace d p l lcp =
  (* rend (lq,r), ou r = p + sum(lq) *)
  let rec reduce p =
    match p with
      [] -> ([],[])
    |t::p' -> let (a,m)=t in
      let q =
	(try Hashtbl.find hmon m
	with Not_found ->
	  let q = selectdiv d m l in
	  match q with
            t'::q' -> (Hashtbl.add hmon m q;q)
          |[] -> q) in
      match q with
	[] ->
	  if reduire_les_queues
	  then
	    let (lq,r)=(reduce p') in
            (lq,((a,m)::r))
	  else ([],p)
      |(b,m')::q' ->
          let b' = P.oppP (P.divP a b) in
          let m''= div_mon d m m' in
          let p1=plusP d p' (mult_t_pol d b' m'' q') in
          let (lq,r)=reduce p1 in
          ((b',m'',q)::lq, r)
  in let (lq,r) = reduce p in
  (*info "reduce2_trace:\n";
     List.iter
     (fun (a,m,s) ->
     let x = mult_t_pol d a m s in
     info ((stringP x)^"\n"))
     lq;
     info "ok\n";*)
  (List.map2
     (fun c0 q ->
       let c =
	 List.fold_left
	   (fun x (a,m,s) ->
	     if equal s q
	     then
	       plusP d x (mult_t_pol d a m (polconst d coef1))
	     else x)
	   c0
	   lq in
       c)
     lcp
     !poldep,
   r)

(***********************************************************************
  Algorithme de Janet (V.P.Gerdt Involutive algorithms...)
*)

(***********************************
  deuxieme version, qui elimine des poly inutiles
*)
let homogeneous = ref false
let pol_courant = ref []


type pol3 =
   {pol : poly;
    anc : poly;
    nmp : mon}

let fst_mon q = snd (List.hd q.pol)
let lm_anc q = snd (List.hd q.anc)

let pol_to_pol3 d p =
  {pol = p; anc = p; nmp = Array.create (d+1) 0}

let is_multiplicative u s i =
  if i=1
  then List.for_all (fun q -> (fst_mon q).(1) <= u.(1)) s
  else
     List.for_all
      (fun q ->
        let v = fst_mon q in
	let res = ref true in
	let j = ref 1 in
	while !j < i && !res do
	  res:= v.(!j) = u.(!j);
	  j:= !j + 1;
	done;
	if !res
	then v.(i) <= u.(i)
	else true)
      s

let is_multiplicative_rev d u s i =
  if i=1
  then
    List.for_all
      (fun q -> (fst_mon q).(d+1-1) <= u.(d+1-1))
      s
  else
     List.for_all
      (fun q ->
        let v = fst_mon q in
	let res = ref true in
	let j = ref 1 in
	while !j < i && !res do
	  res:= v.(d+1- !j) = u.(d+1- !j);
	  j:= !j + 1;
	done;
	if !res
	then v.(d+1-i) <= u.(d+1-i)
	else true)
      s

let monom_multiplicative d u s =
  let m = Array.create (d+1) 0 in
  for i=1 to d do
    if is_multiplicative u s i
    then m.(i)<- 1;
  done;
  m

(* mu monome des variables multiplicative de u *)
let janet_div_mon d u mu v =
  let res = ref true in
  let i = ref 1 in
  while  !i <= d && !res do
    if mu.(!i) = 0
    then res := u.(!i) = v.(!i)
    else res := u.(!i) <= v.(!i);
    i:= !i + 1;
  done;
  !res

let find_multiplicative p mg =
  try Hashpol.find mg p.pol
  with Not_found -> (info "\nPROBLEME DANS LA TABLE DES VAR MULT";
	     info (stringPcut p.pol);
	     failwith "aie")

(* mg hashtable de p -> monome_multiplicatif de g *)

let hashtbl_reductor = ref (Hashtbl.create 51 : (mon,pol3) Hashtbl.t)

(* suppose que la table a été initialisée *)
let find_reductor d v lt mt =
  try Hashtbl.find !hashtbl_reductor v
  with Not_found ->
    let r =
      List.find
	(fun q ->
	  let u = fst_mon q in
	  let mu =  find_multiplicative q mt in
	  janet_div_mon d u mu v
	)
	lt in
    Hashtbl.add !hashtbl_reductor v r;
    r

let normal_form d p g mg onlyhead =
  let rec aux = function
      [] -> (coef1,p)
    | (a,v)::p' ->
	(try
	   let q = find_reductor d v g mg in
	   let (b,u),q' = of_cons q.pol in
	   let c = P.pgcdP a b in
	   let a' = P.divP b c in
	   let b' = P.oppP (P.divP a c) in
	   let m = div_mon d v u in
	   (*      info ".";*)
	   let (c,r) = aux (plusP d (emultP a' p') (mult_t_pol d b' m q')) in
	   (P.multP c a', r)
	 with _ -> (* TODO: catch only relevant exn *)
	   if onlyhead
	   then (coef1,p)
	   else
	     let (c,r)= (aux p') in
	     (c, plusP d [(P.multP a c,v)] r)) in
  aux p

let janet_normal_form d p g mg =
  let (_,r) = normal_form d p g mg false in r

let head_janet_normal_form d p g mg =
  let (_,r) = normal_form d p g mg true in r

let reduce_rem d r lt lq =
  Hashtbl.clear hmon;
  let (_,r) = reduce2 d r (List.map (fun p -> p.pol) (lt @ lq)) in
  Hashtbl.clear hmon;
  r

let tail_normal_form d p g mg =
  let (a,v),p' = of_cons p in
  let (c,r)= (normal_form d p' g mg false) in
  plusP d [(P.multP a c,v)] r

let div_strict d m1 m2 =
  m1 <> m2 && div_mon_test d m2 m1

let criteria d p g lt =
  mult_mon d (lm_anc p) (lm_anc g) = fst_mon p
||
  (let c = ppcm_mon  d (lm_anc p)  (lm_anc g) in
   div_strict d c (fst_mon p))
||
  (List.exists
     (fun t ->
       let cp = ppcm_mon d (lm_anc p) (fst_mon t) in
       let cg = ppcm_mon d (lm_anc g) (fst_mon t) in
       let c = ppcm_mon d (lm_anc p)  (lm_anc g) in
       div_strict d cp c && div_strict d cg c)
     lt)

let head_normal_form d p lt mt =
  let h = ref (p.pol) in
  let res =
  try (
    let v = snd(List.hd !h) in
    let g = ref (find_reductor d v lt mt) in
    if snd(List.hd !h) <> lm_anc p && criteria d p !g lt
    then ((* info "=";*) [])
    else (
      while !h <> [] && (!g).pol <> [] do
	let (a,v),p' = of_cons !h in
	let (b,u),q' = of_cons (!g).pol in
	let c = P.pgcdP a b in
	let a' = P.divP b c in
	let b' = P.oppP (P.divP a c) in
	let m = (div_mon d v u) in
	h := plusP d (emultP a' p') (mult_t_pol d b' m q');
	let v = snd(List.hd !h) in
	g := (
	  try find_reductor d v lt mt
	  with _ -> pol_to_pol3 d []);
      done;
      !h)
    )
  with _ -> ((* info ".";*) !h)
  in
  (*info ("temps de head_normal_form: "
	^(Format.sprintf "@[%10.3f@]s\n" ((Unix.gettimeofday ())-.t1)));*)
  res

let deg_hom p =
  match p with
  | [] -> -1
  | (_,m)::_ -> m.(0)

let head_reduce d lq lt mt =
  let ls = ref lq in
  let lq = ref [] in
  while !ls <> [] do
    let p,ls1 = of_cons !ls in
    ls := ls1;
    if !homogeneous && p.pol<>[] && deg_hom p.pol > deg_hom !pol_courant
    then info "h"
    else
      match head_normal_form d p lt mt with
	  (_,v)::_ as h ->
	    if fst_mon p <> v
	    then lq := (!lq) @ [{pol = h; anc = h; nmp = Array.create (d+1) 0}]
	    else lq := (!lq) @ [p]
	| [] ->
	    (* info "*";*)
	    if fst_mon p = lm_anc p
	    then ls := List.filter (fun q -> not (equal q.anc p.anc)) !ls
  done;
  (*info ("temps de head_reduce: "
	^(Format.sprintf "@[%10.3f@]s\n" ((Unix.gettimeofday ())-.t1)));*)
  !lq

let choose_irreductible d lf =
  List.hd lf
(* bien plus lent
    (List.sort (fun p q -> compare_mon d (fst_mon p.pol) (fst_mon q.pol)) lf)
*)


let hashtbl_multiplicative d lf =
  let mg = Hashpol.create 51 in
  hashtbl_reductor := Hashtbl.create 51;
  List.iter
    (fun g ->
      let (_,u) = List.hd g.pol in
      Hashpol.add mg g.pol (monom_multiplicative d u lf))
    lf;
  (*info ("temps de hashtbl_multiplicative: "
	^(Format.sprintf "@[%10.3f@]s\n" ((Unix.gettimeofday ())-.t1)));*)
  mg

let list_diff l x =
  List.filter (fun y -> y <> x) l

let janet2 d lf p0 =
  hashtbl_reductor := Hashtbl.create 51;
  let t1 = Unix.gettimeofday() in
  info ("------------- Janet2 ------------------\n");
  pol_courant := p0;
  let r = ref p0 in
  let lf = List.map (pol_to_pol3 d) lf in
  let f = choose_irreductible d lf in
  let lt = ref [f] in
  let mt = ref (hashtbl_multiplicative d !lt) in
  let lq = ref (list_diff lf f) in
  lq := head_reduce d !lq !lt !mt;
  r := (* lent head_janet_normal_form  d !r !lt !mt ; *)
    reduce_rem  d !r !lt !lq ;
  info ("reste: "^(stringPcut !r)^"\n");
  while !lq <> [] && !r <> [] do
    let p = choose_irreductible d !lq in
    lq := list_diff !lq p;
    if p.pol = p.anc
    then ( (* on enleve de lt les pol divisibles par p et on les met dans lq *)
      let m = fst_mon p in
      let lt1 = !lt in
      List.iter
	(fun q ->
	  let m'= fst_mon q in
	  if div_strict d m m'
	  then (
	    lq := (!lq) @ [q];
	    lt := list_diff !lt q))
	lt1;
      mt := hashtbl_multiplicative d !lt;
      );
    let h = tail_normal_form d p.pol !lt !mt in
    if h = []
    then info "************ reduction a zero, ne devrait pas arriver *\n"
    else (
      lt := (!lt) @ [{pol = h; anc = p.anc; nmp = Array.copy p.nmp}];
      info ("nouveau polynome: "^(stringPcut h)^"\n");
      mt := hashtbl_multiplicative d !lt;
      r := (* lent head_janet_normal_form  d !r !lt !mt ; *)
	reduce_rem  d !r !lt !lq ;
      info ("reste: "^(stringPcut !r)^"\n");
      if !r <> []
      then (
	List.iter
	  (fun q ->
	    let mq = find_multiplicative q !mt in
	    for i=1 to d do
	      if mq.(i) = 1
	      then q.nmp.(i)<- 0
	      else
		if q.nmp.(i) = 0
		then (
		  (* info "+";*)
		  lq := (!lq) @
		    [{pol = multP d (gen d i) q.pol;
		      anc = q.anc;
		      nmp = Array.create (d+1) 0}];
		  q.nmp.(i)<-1;
		 );
	    done;
	  )
	  !lt;
	lq := head_reduce d !lq !lt !mt;
	info ("["^(string_of_int (List.length !lt))^";"
	      ^(string_of_int (List.length !lq))^"]");
       ));
  done;
  info ("--- Janet2 donne:\n");
  (* List.iter (fun p -> info ("polynome: "^(stringPcut p.pol)^"\n")) !lt; *)
  info ("reste: "^(stringPcut !r)^"\n");
  info ("--- fin Janet2\n");
  info ("temps: "^(Format.sprintf "@[%10.3f@]s\n" ((Unix.gettimeofday ())-.t1)));
  List. map (fun q -> q.pol) !lt

(**********************************************************************
 version 3 *)

let head_normal_form3 d p lt mt =
  let h = ref (p.pol) in
  let res =
  try (
    let v = snd(List.hd !h) in
    let g = ref (find_reductor d v lt mt) in
    if snd(List.hd !h) <> lm_anc p && criteria d p !g lt
    then ((* info "=";*) [])
    else (
      while !h <> [] && (!g).pol <> [] do
	let (a,v),p' = of_cons !h in
        let (b,u),q' = of_cons (!g).pol in
	let c = P.pgcdP a b in
	let a' = P.divP b c in
	let b' = P.oppP (P.divP a c) in
	let m = div_mon d v u in
	h := plusP d (emultP a' p') (mult_t_pol d b' m q');
	let v = snd(List.hd !h) in
	g := (
	  try find_reductor d v lt mt
	  with _ -> pol_to_pol3 d []);
      done;
      !h)
    )
  with _ -> ((* info ".";*) !h)
  in
  (*info ("temps de head_normal_form: "
	^(Format.sprintf "@[%10.3f@]s\n" ((Unix.gettimeofday ())-.t1)));*)
  res


let janet3 d lf p0 =
  hashtbl_reductor := Hashtbl.create 51;
  let t1 = Unix.gettimeofday() in
  info ("------------- Janet2 ------------------\n");
  let r = ref p0 in
  let lf = List.map (pol_to_pol3 d) lf in

  let f,lf1 = of_cons lf in
  let lt = ref [f] in
  let mt = ref (hashtbl_multiplicative d !lt) in
  let lq = ref lf1 in
  r := reduce_rem  d !r !lt !lq ; (* janet_normal_form  d !r !lt !mt ;*)
  info ("reste: "^(stringPcut !r)^"\n");
  while !lq <> [] && !r <> [] do
    let p,lq1 = of_cons !lq in
    lq := lq1;
(*
    if p.pol = p.anc
    then ( (* on enleve de lt les pol divisibles par p et on les met dans lq *)
      let m = fst_mon (p.pol) in
      let lt1 = !lt in
      List.iter
	(fun q ->
	  let m'= fst_mon (q.pol) in
	  if div_strict d m m'
	  then (
	    lq := (!lq) @ [q];
	    lt := list_diff !lt q))
	lt1;
      mt := hashtbl_multiplicative d !lt;
      );
*)
    let h = head_normal_form3 d p !lt !mt in
    if h = []
    then (
      info "*";
      if fst_mon p = lm_anc p
      then
	lq := List.filter (fun q -> not (equal q.anc p.anc)) !lq;
     )
    else (
      let q =
	if fst_mon p <> snd(List.hd h)
	then {pol = h; anc = h; nmp = Array.create (d+1) 0}
	else {pol = h; anc = p.anc; nmp = Array.copy p.nmp}
      in
      lt:= (!lt) @ [q];
      info ("nouveau polynome: "^(stringPcut q.pol)^"\n");
      mt := hashtbl_multiplicative d !lt;
      r := reduce_rem  d !r !lt !lq ; (* janet_normal_form  d !r !lt !mt ;*)
      info ("reste: "^(stringPcut !r)^"\n");
      if !r <> []
      then (
	List.iter
	  (fun q ->
	    let mq = find_multiplicative q !mt in
	    for i=1 to d do
	      if mq.(i) = 1
	      then q.nmp.(i)<- 0
	      else
		if q.nmp.(i) = 0
		then (
		  (* info "+";*)
		  lq := (!lq) @
		    [{pol = multP d (gen d i) q.pol;
		      anc = q.anc;
		      nmp = Array.create (d+1) 0}];
		  q.nmp.(i)<-1;
		 );
	    done;
	  )
	  !lt;
	info ("["^(string_of_int (List.length !lt))^";"
	      ^(string_of_int (List.length !lq))^"]");
       ));
  done;
  info ("--- Janet3 donne:\n");
  (* List.iter (fun p -> info ("polynome: "^(stringPcut p.pol)^"\n")) !lt; *)
  info ("reste: "^(stringPcut !r)^"\n");
  info ("--- fin Janet3\n");
  info ("temps: "^(Format.sprintf "@[%10.3f@]s\n" ((Unix.gettimeofday ())-.t1)));
  List. map (fun q -> q.pol) !lt


(***********************************************************************
   Completion
 *)

let sugar_flag = ref true

let sugartbl = (Hashpol.create 1000 : int Hashpol.t)

let compute_sugar p =
  List.fold_left (fun s (a,m) -> max s m.(0)) 0 p

let sugar p =
  try Hashpol.find sugartbl p
  with Not_found ->
    let s = compute_sugar p in
    Hashpol.add sugartbl p s;
    s

let spol d p q=
  let m = snd (List.hd p) in
  let m'= snd (List.hd q) in
  let a = fst (List.hd p) in
  let b = fst (List.hd q) in
  let p'= List.tl p in
  let q'= List.tl q in
  let c=(pgcdpos a b) in
  let m''=(ppcm_mon d m m') in
  let m1 = div_mon d m'' m in
  let m2 = div_mon d m'' m' in
  let fsp p' q' =
    plusP d
      (mult_t_pol d (P.divP b c) m1 p')
      (mult_t_pol d (P.oppP (P.divP a c)) m2 q') in
  let sp = fsp p' q' in
  coefpoldep_set sp p (fsp (polconst d coef1) []);
  coefpoldep_set sp q (fsp [] (polconst d coef1));
  Hashpol.add sugartbl sp
    (max (m1.(0) + (sugar p)) (m2.(0) + (sugar q)));
  sp

let etrangers d p p'=
  let m = snd (List.hd p) in
  let m'= snd (List.hd p') in
  let res=ref true in
  let i=ref 1 in
  while (!res) && (!i<=d) do
    res:= (m.(!i) = 0) || (m'.(!i)=0);
      i:=!i+1;
  done;
  !res


(* teste si le monome dominant de p''
   divise le ppcm des monomes dominants de p et p' *)

let div_ppcm d p p' p'' =
  let m = snd (List.hd p) in
  let m'= snd (List.hd p') in
  let m''= snd (List.hd p'') in
  let res=ref true in
  let i=ref 1 in
  while (!res) && (!i<=d) do
    res:= ((max m.(!i) m'.(!i)) >= m''.(!i));
    i:=!i+1;
  done;
  !res

(***********************************************************************
   Code extrait de la preuve de L.Thery en Coq
 *)
type 'poly cpRes =
    Keep of ('poly list)
  | DontKeep of ('poly list)

let addRes i = function
    Keep h'0 -> Keep (i::h'0)
  | DontKeep h'0 -> DontKeep (i::h'0)

let rec slice d i a = function
    [] -> if etrangers d i a then DontKeep [] else Keep []
  | b::q1 ->
      if div_ppcm d i a b then DontKeep (b::q1)
      else if div_ppcm d i b a then slice d i a q1
      else addRes b (slice d i a q1)

let rec addS x l = l @[x]

let addSugar x l =
  if !sugar_flag
  then
    let sx = sugar x in
    let rec insere l  =
      match l with
      | [] -> [x]
      | y::l1 ->
	  if sx <= (sugar y)
	  then x::l
	  else y::(insere l1)
    in insere l
  else addS x l

(* ajoute les spolynomes de i avec la liste de polynomes aP,
   a la liste q *)

let rec genPcPf d i aP q =
  match aP with
      [] -> q
    | a::l1 ->
        (match slice d i a l1 with
             Keep l2 -> addSugar (spol d i a) (genPcPf d i l2 q)
           | DontKeep l2 -> genPcPf d i l2 q)

let rec genOCPf d = function
    [] -> []
  | a::l -> genPcPf d a l (genOCPf d l)

let step = ref 0

let infobuch p q =
  if !step = 0
  then (info ("[" ^ (string_of_int (List.length p))
              ^ "," ^  (string_of_int (List.length q))
              ^ "]"))

(***********************************************************************)
(* dans lp les nouveaux sont en queue *)

let coef_courant = ref coef1


type certificate =
    { coef : coef; power : int;
      gb_comb : poly list list; last_comb : poly list }

let test_dans_ideal d p lp lp0 =
  let (c,r) = reduce2 d !pol_courant lp in
  info ("reste: "^(stringPcut r)^"\n");
  coef_courant:= P.multP !coef_courant c;
  pol_courant:= r;
  if r=[]
  then (info "polynome reduit a 0\n";
	let lcp = List.map (fun q -> []) !poldep in
	let c = !coef_courant in
	let (lcq,r) = reduce2_trace d (emultP c p) lp lcp in
	info ("r: "^(stringP r)^"\n");
        let res=ref  (emultP c p) in
	List.iter2
	  (fun cq q -> res:=plusP d (!res) (multP d cq q);
	  )
	  lcq !poldep;
	info ("verif somme: "^(stringP (!res))^"\n");
	info ("coefficient: "^(stringP (polconst d c))^"\n");
	let rec aux lp =
	  match lp with
	  |[] -> []
	  |p::lp ->
	      (List.map
		 (fun q -> coefpoldep_find p q)
		 lp)::(aux lp)
	in
	let liste_polynomes_de_depart = List.rev lp0 in
	let polynome_a_tester = p in
	let liste_des_coefficients_intermediaires =
	  (let lci = List.rev (aux (List.rev lp)) in
	  let lci = ref lci (* (List.map List.rev lci) *) in
	  List.iter (fun x -> lci := List.tl (!lci)) lp0;
	  !lci) in
	let liste_des_coefficients =
	  List.map
	    (fun cq -> emultP coefm1 cq)
	    (List.rev lcq) in
	(liste_polynomes_de_depart,
	 polynome_a_tester,
	 {coef=c;
	  power=1;
	  gb_comb = liste_des_coefficients_intermediaires;
	  last_comb = liste_des_coefficients}))
  else ((*info "polynome non reduit a 0\n";
	info ("\nreste: "^(stringPcut r)^"\n");*)
	raise NotInIdeal)

let divide_rem_with_critical_pair = ref false

let choix_spol d p l =
  if !divide_rem_with_critical_pair
  then (
    let (_,m) = List.hd p in
    try (
      let q =
	List.find
	  (fun q ->
	    let (_,m') = List.hd q in
	    div_mon_test d m m')
	  l in
      q::(list_diff l q))
    with _ -> l)
  else l

let pbuchf d pq p lp0=
  info "calcul de la base de Groebner\n";
  step:=0;
  Hashtbl.clear hmon;
  let rec pbuchf lp lpc =
      infobuch lp lpc;
(*      step:=(!step+1)mod 10;*)
      match lpc with
        [] -> test_dans_ideal d p lp lp0
      | _ ->
	  let a,lpc2 = of_cons (choix_spol d !pol_courant lpc) in
	  if !homogeneous && a<>[] && deg_hom a > deg_hom !pol_courant
	  then (info "h";pbuchf lp lpc2)
	  else
	    let sa = sugar a in
            let (ca,a0)= reduce2 d a lp in
            match a0 with
              [] -> info "0";pbuchf lp lpc2
            | _ ->
		let a1 = emultP ca a in
		List.iter
		  (fun q ->
		    coefpoldep_set a1 q (emultP ca (coefpoldep_find a q)))
		  !poldep;
		let (lca,a0) = reduce2_trace d a1 lp
		    (List.map (fun q -> coefpoldep_find a1 q) !poldep) in
		List.iter2 (fun c q -> coefpoldep_set a0 q c) lca !poldep;
		info ("\nnouveau polynome: "^(stringPcut a0)^"\n");
		let ct = coef1 (* contentP a0 *) in
		(*info ("contenu: "^(string_of_coef ct)^"\n");*)
		Hashpol.add sugartbl a0 sa;
		poldep:=addS a0 lp;
		poldepcontent:=addS ct (!poldepcontent);
		try test_dans_ideal d p (addS a0 lp) lp0
		with NotInIdeal -> pbuchf (addS a0 lp) (genPcPf d a0 lp lpc2)
  in pbuchf (fst pq) (snd pq)

let is_homogeneous p =
  match p with
  | [] -> true
  | (a,m)::p1 -> let d = m.(0) in
    List.for_all (fun (b,m') -> m'.(0)=d) p1

(* rend
   c
   lp = [pn;...;p1]
   p
   lci = [[a(n+1,n);...;a(n+1,1)];
   [a(n+2,n+1);...;a(n+2,1)];
   ...
   [a(n+m,n+m-1);...;a(n+m,1)]]
   lc = [qn+m; ... q1]

   tels que
   c*p = sum qi*pi
   ou pn+k = a(n+k,n+k-1)*pn+k-1 + ... + a(n+k,1)* p1
 *)

let in_ideal d lp p =
  homogeneous := List.for_all is_homogeneous (p::lp);
  if !homogeneous then info "polynomes homogenes\n";
  (* janet2 d lp p;*)
  info ("p: "^stringPcut p^"\n");
  info ("lp:\n"^List.fold_left (fun r p -> r^stringPcut p^"\n") "" lp);
  initcoefpoldep d lp;
  coef_courant:=coef1;
  pol_courant:=p;
  try test_dans_ideal d p lp lp
  with NotInIdeal -> pbuchf d (lp, genOCPf d lp) p lp

end
