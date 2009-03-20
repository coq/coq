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

(***********************************************************************
   Coefficients: polynomes recursifs
   on n'utilise pas les big_int car leur egalite n'est pas generique: on ne peut pas utiliser de tables de hash simplement.
 *)

type coef = Polynom.poly
let coef_of_int = Polynom.cf
let eq_coef = Polynom.eqP
let plus_coef =Polynom.plusP
let mult_coef = Polynom.multP
let sub_coef = Polynom.moinsP
let opp_coef = Polynom.oppP
let div_coef = Polynom.divP (* division exacte *)
let coef0 = Polynom.cf0
let coef1 = Polynom.cf1
let string_of_coef c = "["^(Polynom.string_of_P c)^"]"


let rec pgcd a b = Polynom.pgcdP a b

(*
let htblpgcd = Hashtbl.create 1000

let pgcd a b =
  try
    (let c = Hashtbl.find htblpgcd (a,b) in
    info "*";
    c)
  with _ ->
    (let c =  Polynom.pgcdP a b in
    info "-";
    Hashtbl.add htblpgcd (a,b) c;
    c)
*)

(***********************************************************************
   Monomes
   tableau d'entiers
   le premier coefficient est le degre
 *)

let hmon = Hashtbl.create 1000

type mon = int array

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


(* Comparaison de monomes avec ordre du degre lexicographique = on commence par regarder la 1ere variable*)
(*let compare_mon d m m' =
  let res=ref 0 in
  let i=ref 1 in (* 1 si lexico pur 0 si degre*)
  while (!res=0) && (!i<=d) do
    res:= (compare m.(!i) m'.(!i));
    i:=!i+1;
  done;
  !res
*)

(* degre lexicographique inverse *)
let compare_mon d m m' =
  match compare m.(0) m'.(0) with
  | 0 -> (* meme degre total *)
      let res=ref 0 in
      let i=ref d in
      while (!res=0) && (!i>=1) do
	res:= - (compare m.(!i) m'.(!i));
	i:=!i-1;
      done;
      !res
  | x -> x


(* Division de monome ayant le meme nb de variables *)
let div_mon d m m' =
  let m'' = Array.create (d+1) 0 in
  for i=0 to d do
    m''.(i)<- (m.(i)-m'.(i));
  done;
  m''

let div_pol_coef p c =
  List.map (fun (a,m) -> (div_coef a c,m)) p

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

type poly = (coef * mon) list

let eq_poly =
  Util.list_for_all2eq
    (fun (c1,m1) (c2,m2) -> eq_coef c1 c2 && m1=m2)

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
            |_ -> let c=plus_coef (fst t) (fst t') in
              match eq_coef c coef0 with
                true -> (plusP p' q')
              |false -> (c,(snd t))::(plusP p' q')
  in plusP p q


(* multiplication d'un polynome par (a,monome) *)
let mult_t_pol d a m p =
  let rec mult_t_pol p =
    match p with
      [] -> []
    |(b,m')::p -> ((mult_coef a b),(mult_mon d m m'))::(mult_t_pol p)
  in mult_t_pol p


(* Retourne un polynome de l dont le monome de tete divise m,  [] si rien *)
let rec selectdiv d m l =
  match l with
    [] -> []
  |q::r -> let m'= snd (List.hd q) in
    match (div_mon_test d m m') with
      true -> q
    |false -> selectdiv d m r


(* Retourne un polynome générateur 'i' à d variables *)
let gen d i =
  let m = Array.create (d+1) 0 in
  m.(i) <- 1;
  let m = set_deg d m in 
  [((coef_of_int 1),m)]



(* oppose d'un polynome *)
let oppP p =
  let rec oppP p =
    match p with
      [] -> []
    |(b,m')::p -> ((opp_coef b),m')::(oppP p)
  in oppP p


(* multiplication d'un polynome par un coefficient par 'a' *)
let emultP a p =
  let rec emultP p =
    match p with
      [] -> []
    |(b,m')::p -> ((mult_coef a b),m')::(emultP p)
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

let rec contentP p =
  match p with
  |[] -> coef1
  |[a,m] -> a
  |(a,m)::p1 -> pgcd a (contentP p1)

let contentPlist lp =
  match lp with
  |[] -> coef1
  |p::l1 -> List.fold_left (fun r q -> pgcd r (contentP q)) (contentP p) l1

(***********************************************************************
   Division de polynomes
 *)

let pgcdpos a b  = pgcd a b


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
    |t::p' -> let (a,m)=t in
      let q = (try Hashtbl.find hmon m 
      with Not_found -> 
	let q = selectdiv d m l in
	match q with 
          t'::q' -> (Hashtbl.add hmon m q;q)
	|[] -> q) in
      match q with
	[] -> if reduire_les_queues
	then
	  let (c,r)=(reduce p') in
          (c,((mult_coef a c,m)::r))
	else (coef1,p)
      |(b,m')::q' -> 
          let c=(pgcdpos a b) in
          let a'= (div_coef b c) in
          let b'=(opp_coef (div_coef a c)) in
          let (e,r)=reduce (div_pol d p' q' a' b'
                              (div_mon d m m')) in
          (mult_coef a' e,r)
  in let (c,r) = reduce p in
  (c,r)

(* trace des divisions *)

(* liste des polynomes de depart *)
let poldep = ref [] 
let poldepcontent = ref []

(* table des coefficients des polynomes en fonction des polynomes de depart *)
let coefpoldep = Hashtbl.create 51

(* coefficient de q dans l expression de p = sum_i c_i*q_i *)
let coefpoldep_find p q =
  try (Hashtbl.find coefpoldep (p,q))
  with _ -> []

let coefpoldep_set p q c =
  Hashtbl.add coefpoldep (p,q) c

let initcoefpoldep d lp =
  poldep:=lp;
  poldepcontent:= List.map contentP (!poldep);
  List.iter
    (fun p -> coefpoldep_set p p (polconst d (coef_of_int 1)))
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
          let b'=(opp_coef (div_coef a b)) in
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
	     if eq_poly s q
	     then
	       plusP d x (mult_t_pol d a m (polconst d (coef_of_int 1)))
	     else x)
	   c0
	   lq in
       c)
     lcp
     !poldep,
   r)     

(***********************************************************************
   Completion
 *)
let homogeneous = ref false

let spol d p q=
  let m = snd (List.hd p) in
  let m'= snd (List.hd q) in
  let a = fst (List.hd p) in
  let b = fst (List.hd q) in
  let p'= List.tl p in
  let q'= List.tl q in
  let c=(pgcdpos a b) in
  let m''=(ppcm_mon d m m') in
  let fsp p' q' =
    plusP d
      (mult_t_pol d
	 (div_coef b c)
	 (div_mon d m'' m) p')
      (mult_t_pol d
	 (opp_coef (div_coef a c))
         (div_mon d m'' m') q') in
  let sp = fsp p' q' in
  coefpoldep_set sp p (fsp (polconst d (coef_of_int 1)) []);
  coefpoldep_set sp q (fsp [] (polconst d (coef_of_int 1)));
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

let list_rec f0 f1 =
  let rec f2 = function
      [] -> f0
    | a0::l0 -> f1 a0 l0 (f2 l0)
  in f2

let addRes i = function
    Keep h'0 -> Keep (i::h'0)
  | DontKeep h'0 -> DontKeep (i::h'0)

let slice d i a q =
  list_rec
    (match etrangers d i a with
      true -> DontKeep []
    | false -> Keep [])
    (fun b q1 rec_ren ->
      match div_ppcm d i a b with
	true ->  DontKeep (b::q1)
      | false ->
          (match div_ppcm d i b a with
            true -> rec_ren
          | false -> addRes b rec_ren)) q

let rec addS x l = l @[x]

(* ajoute les spolynomes de i avec la liste de polynomes aP, 
   a la liste q *)

let genPcPf d i aP q =
  (let rec genPc aP0 =
    match aP0 with
      [] -> (fun r -> r)
    | a::l1 -> 
	(fun l ->
          (match slice d i a l1 with
            Keep l2 -> addS (spol d i a) (genPc l2 l)
          | DontKeep l2 -> genPc l2 l))
  in genPc aP) q

let genOCPf d h' =
  list_rec [] (fun a l rec_ren ->
    genPcPf d a l rec_ren) h'

let step = ref 0

let infobuch p q =
  if !step = 0 
  then (info ("[" ^ (string_of_int (List.length p))
              ^ "," ^  (string_of_int (List.length q))
              ^ "]"))

(***********************************************************************)
(* dans lp les nouveaux sont en queue *)

let coef_courant = ref coef1
let pol_courant = ref []

let test_dans_ideal d p lp lp0 =
  let (c,r) = reduce2 d !pol_courant lp in
  info ("reste: "^(stringPcut r)^"\n");
  coef_courant:= mult_coef !coef_courant c;
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
	  let lci = ref lci (* (List.map List.rev lci) *) in
	  List.iter (fun x -> lci := List.tl (!lci)) lp0;
	  !lci) in
	let liste_des_coefficients =
	  List.map
	    (fun cq -> emultP (coef_of_int (-1)) cq)
	    (List.rev lcq) in
	(coefficient_multiplicateur,
	 liste_polynomes_de_depart,
	 polynome_a_tester,
	 liste_des_coefficients_intermediaires,
	 liste_des_coefficients))
  else ((*info "polynome non reduit a 0\n";
	info ("\nreste: "^(stringPcut r)^"\n");*)
	(c,[],[],[],[]))
      
let choix_spol p l = l
    
let deg_hom p =
  match p with
  | [] -> -1
  | (a,m)::_ -> m.(0)

let pbuchf d pq p lp0=
  info "calcul de la base de Groebner\n";
  step:=0;
  Hashtbl.clear hmon;
  let rec pbuchf x = 
      let (lp, lpc) = x in
      infobuch lp lpc; 
(*      step:=(!step+1)mod 10;*)
      match lpc with
        [] -> test_dans_ideal d p lp lp0
      | _ ->
	  (match choix_spol !pol_courant lpc with
	  |[] -> assert false
	  |(a::lpc2) ->
	  if !homogeneous && a<>[] && deg_hom a > deg_hom !pol_courant
	  then (info "h";pbuchf (lp, lpc2))
	  else
          let (ca,a0)= reduce2 d a lp in
          match a0 with
            [] -> info "0";pbuchf (lp, lpc2)
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
	      poldep:=addS a0 lp;
	      poldepcontent:=addS ct (!poldepcontent);

	      let (c1,lp1,p1,lci1,lc1)
		  = test_dans_ideal d p (addS a0 lp) lp0 in
	      if lc1<>[]
	      then (c1,lp1,p1,lci1,lc1)
	      else
                pbuchf
                  (((addS a0 lp),
                    (genPcPf d a0 lp lpc2))))
  in pbuchf pq 

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
  info ("p: "^(stringPcut p)^"\n");
  info ("lp:\n"^(List.fold_left (fun r p -> r^(stringPcut p)^"\n") "" lp));
  initcoefpoldep d lp;
  coef_courant:=coef1;
  pol_courant:=p;
  homogeneous := List.for_all is_homogeneous (p::lp);
  if !homogeneous then info "polynomes homogenes\n";
  let (c1,lp1,p1,lci1,lc1) = test_dans_ideal d p lp lp in
  if lc1<>[]
  then (c1,lp1,p1,lci1,lc1)
  else pbuchf d (lp, (genOCPf d lp)) p lp


