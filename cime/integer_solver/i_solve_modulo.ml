(***************************************************************************

  This module provides a function for solving systems of linear equations
  over the integers modulo a given integer $n$.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Solve
open I_solve
open Printf


(* 
  i_solve_modulo prend comme arguments
   - un entier n modulo lequel on travaille
     Au niveau de l'unification, ca correspond a l'unification ACUN(n),
     ou N(n) est la nilpotence d'ordre n: x^n = 1.
   - un vecteur d'entiers [|v0;v0+v1;...;v0+v1+...+vk|] ou` v0 represente
     le nombre de variables non instanciees, et vi, i>0, le nombre
     de variables instanciees dans la theorie Ti, 
   - un systeme d'equations ligne par ligne
   - une liste qui correspond a pe.edge

  et retourne un couple de vecteurs de solutions tel que:
  le premier element contient les solutions homogenes, i.e. qui valent
  0 sur les variables instanciees, 
  le second les autres solutions, sachant que les composantes associees 
  a des variables instanciees ne peuvent prendre que les valeurs 0 et 1, 
  et que de plus, si une composante associee a une variable instanciee 
  dans la theorie Ti vaut 1, alors toutes les composantes associees a 
  des variables instanciees dans une theorie Tj , i <> j, valent 0, Ti et
  Tj etant toutes deux des theories REGULIERES, COLLAPSE-FREE. 

  On va essayer autant que faire se peut de ne pas instancier des 
  variables par une valeur contenant une variable marquee interdite.
  
  Si des identifications de variables instanciees sont necessaires, on
  aura AVEC_IDENT, sinon SANS_IDENT.

*)

type etat =
    {         
      modulo : int;             (* pour le cas modulo *)
      e   : (int * int) list;   (* correspond a pe.edge *)
      vt  : int array;          (* vecteur de type des vars (inst. ou pas) *)
      nv  : int;                (* nombre de variables de depart           *)
      nc  : int;                (* nombre total de variables instanciees   *)
      mutable  ne  : int;       (* nombre d'equations courant              *)
      mutable  nvc  : int;      (* nombre de variables courant             *)
      mutable  a   : int array;(* a et b representent les equations courantes*)
      mutable  b   : int array; (* aX+b=0 vis-a-vis desquelles on transforme *)
      mutable  grand_a   : int array array;
      mutable  grand_b   : int array array;
      mutable  grand_c   : int array array;
      mutable  grand_d   : int array array
    }
    
exception Matrice_Nulle
exception Systeme_Sans_Solution
exception Non_Inversible
  
(*
  show imprime l'etat e
*)

(*i      
let show e =
  printf "show\n";
  printf "vt =";
  for i=0 to pred (Array.length e.vt) do 
    printf " %d" e.vt.(i)
  done;
  printf "\n";
  printf "nv = %d\n" e.nv;
  printf "nc = %d\n" e.nc;
  printf "ne = %d\n" e.ne;
  printf "nvc = %d\n" e.nvc;
  printf " A | B \n";
  for i=0 to (pred e.ne) do
    for j=0 to (pred e.nvc) do
      printf "%d " e.grand_a.(i).(j)
    done;
    printf " | ";
    for j=0 to (pred e.nc) do
      printf "%d " e.grand_b.(i).(j)
    done
  done;
  printf "\n C | D\n";
  for i=0 to (pred e.nv) do
    for j=0 to (pred e.nvc) do
      printf "%d " e.grand_c.(i).(j)
    done;
    printf " | ";
    for j=0 to (pred e.nc) do
      printf "%d " e.grand_d.(i).(j)
    done
  done;
  flush stdout
 
i*)
   
(*
  [inverse_modulo n m] calcule l'inverse de m modulo n, et leve
  l'exception [Non_Inversible] si m n'est pas inversible. n et m
  sont des entiers naturels.
*)

let inverse_modulo n m = 
  let u = Array.create 3 0
  and v = Array.create 3 0
  and t = Array.create 3 0 in
    u.(0) <- 1;
    u.(2) <- n;
    v.(1) <- 1;
    v.(2) <- m;
    while v.(2) > 0 do
      let q = u.(2) / v.(2) in
        for i= 0 to 2 do
          t.(i) <- u.(i) - (q * v.(i));
          u.(i) <- v.(i);
          v.(i) <- t.(i)
        done
    done;
    if u.(2) = 1
    then u.(1)
    else raise Non_Inversible
      
let pgcd n m = 
  let u = Array.create 3 0
  and v = Array.create 3 0
  and t = Array.create 3 0 in
    u.(0) <- 1;
    u.(2) <- n;
    v.(1) <- 1;
    v.(2) <- m;
    while v.(2) > 0 do
      let q = u.(2) / v.(2) in
        for i= 0 to 2 do
          t.(i) <- u.(i) - (q * v.(i));
          u.(i) <- v.(i);
          v.(i) <- t.(i)
        done
    done;
    u.(2)

(*
  [divise c n v] teste si l'entier c divise les n premiers elements 
  du vecteur v.
*)
  

let init_modulo n mat vect_type pe_edge = 
  let nb_eq = Array.length mat
  and nb_var = vect_type.(0)
  and nb_cst = vect_type.(pred (Array.length vect_type)) - vect_type.(0) in
    if (nb_var + nb_cst) = Array.length mat.(0)
    then 
      let grand_o = Array.create_matrix nb_var nb_cst 0
      and grand_id = Array.create_matrix nb_var nb_var 0 
      and grand_aa = Array.create_matrix nb_eq nb_var 0 
      and grand_bb = Array.create_matrix nb_eq nb_cst 0 in 
	begin
	  for j=0 to (pred nb_var) do
            grand_id.(j).(j) <- 1
	  done;
	  for i=0 to (pred nb_eq) do
            for j=0 to (pred nb_var) do
	      grand_aa.(i).(j) <- zmod mat.(i).(j) n
	    done;
	    for j=0 to (pred nb_cst) do
	      grand_bb.(i).(j) <- zmod mat.(i).(nb_var + j) n
	    done
	  done;

	  let e =  
	    {
	      modulo = n;
              e = pe_edge;
              vt = vect_type;
              nv = nb_var;
	      nc = nb_cst;
              ne = nb_eq;
              nvc = nb_var;
              a = Array.create nb_var 0;
              b = Array.create nb_cst 0;
              grand_a = grand_aa;
              grand_b = grand_bb;
              grand_c = grand_id;
              grand_d = grand_o} in 
       (* show e; *) 
	    e 
	end
    else failwith "A et v_type ont des dimensions incompatibles"

(*
   [selection1 e (i,j,invc)] teste si le fait d'utiliser l'equation no i
   pour eliminer la variable no j (lors d'une etape de type 1 ne va 
   pas instancier cette derniere par un terme contenant une variable 
   prohibee par la contrainte edge.
*)

let selection1 e i j invc =
  let n = e.modulo in 
    List.for_all 
      (function (l,k) -> 
         let l'= l - e.nv in
           (zmod (e.grand_d.(k).(l') - 
		  (invc*e.grand_c.(k).(j)*e.grand_b.(i).(l'))) n) = 0)
      e.e

(* recherche de la position d'un coefficient inversible modulo n dans une
   matrice d'entiers : inversc e n dimx dimy mat retourne (i,j) tel que 
   mat(i,j) est inversible. Si aucun coefficient n'est inversible, l'exception
   Not_found est levee. Seules les dimx premieres lignes et les dimy
   premieres colonnes sont considerees. Si c'est possible, on choisit
   un coefficient retenu par la fonction selection1.
*)

let inversc e n dimx dimy mat = 
  let list_pos_inv = ref [] in
    try 
      for i=0 to (pred dimx) do
        for j=0 to (pred dimy) do
          try 
	    begin
	      let inv = inverse_modulo n mat.(i).(j) in
              let res = (i,j,inv) in
                list_pos_inv := [res];
                if (selection1 e i j inv)
                then raise Exit
	    end
          with 
	      Non_Inversible -> ()
            | Exit -> raise Exit
        done
      done;
      begin
	try 
	  List.hd !list_pos_inv
        with 
	    Failure _ -> raise Not_found
      end
    with Exit -> List.hd !list_pos_inv

(*
   [selection23 e (i,j)] teste si le fait d'utiliser l'equation no i
   pour eliminer la variable no j (lors d'une etape de type 2 ou 3 
   ne va pas instancier cette derniere par un terme contenant une 
   variable prohibee par la contrainte edge.
*)
let selection23 e (i,j) =
  let nb_var = e.nvc
  and nb_cst = e.nc
  and c = e.grand_a.(i).(j)
  and n = e.modulo in
    if divides c nb_var e.grand_a.(i)
    then 
      begin
	let d = pgcd c n in
	let n' = n/d in
	  if divides d nb_cst e.grand_b.(i)
	  then 
	    List.for_all 
              (function (l,k) -> 
		 let l'= l - e.nv in
                   (zmod (e.grand_d.(k).(l') - 
			  (e.grand_c.(k).(j)*
			   (inverse_modulo n' e.grand_b.(i).(l')))) n) = 0)
              e.e
	  else raise Systeme_Sans_Solution
      end
    else true

(* recherche des positions du plus petit coefficient non nul en valeur 
   absolue dans une matrice d'entiers : ppc n dimx dimy mat retourne la 
   liste des couples (i,j) tels que mat(i,j) est la valeur desiree. Si 
   la matrice est nulle, l'exception Matrice_Nulle est levee. Seules les 
   dimx premieres lignes et les dimy premieres colonnes sont considerees.  
*)

let ppc n dimx dimy mat = 
  let list_pos_min = ref []
  and min = ref 0 in
    for i=0 to (pred dimx) do
      for j=0 to (pred dimy) do
	if (((!min) = 0) & (mat.(i).(j) <> 0))
	then 
	  begin 
            min := abs mat.(i).(j);
            list_pos_min := [(i,j)]
          end
	else 
	  if (((abs mat.(i).(j)) < !min) & (mat.(i).(j) <> 0))
          then 
	    begin
              min := abs mat.(i).(j);
              list_pos_min := [(i,j)]
            end
          else 
	    if (((abs mat.(i).(j)) = !min) & (mat.(i).(j) <> 0))
            then list_pos_min := (i,j)::(!list_pos_min)                   
      done
    done;
    if !min = 0
    then raise Matrice_Nulle
    else !list_pos_min


let etape1 i0 j0 invc e = 
(*
  elimination de la variable j0 dans le systeme grace a l'equation i0
  ou elle apparait avec un coefficent c inversible d'inverse invc.
*)
  let nb_var = e.nvc
  and nb_var_dep = e.nv
  and nb_cst = e.nc
  and nb_eq = e.ne
  and n = e.modulo in
(*
  on met dans a et b les coefficients de l'equation i0, multiplies par
  l'inverse de c modulo n.
*)
    for j=0 to (pred nb_var) do
      e.a.(j) <- zmod (e.grand_a.(i0).(j) * invc) n
    done;
    for j=0 to (pred nb_cst) do
      e.b.(j) <- zmod (e.grand_b.(i0).(j) * invc) n
    done;
(*
  mise a jour de la matrice A et de la matrice de constantes B
  la ligne i0 (dans A et B) correspond a l'equation utilisee, 
  et l'information sera conservee dans la partie X = CYn + D,
  la colonne j0 (dans A) correspond a la variable eliminee,
  et vaut 0. 
*)
    for i=0 to (pred nb_eq) do 
      if i <> i0
      then 
	begin
	  for j=0 to (pred nb_cst) do
            e.grand_b.(i).(j) <- 
            zmod (e.grand_b.(i).(j) - (e.grand_a.(i).(j0) * e.b.(j))) n
          done;
          for j=0 to (pred nb_var) do
            if j <> j0 
            then e.grand_a.(i).(j) <- 
              zmod (e.grand_a.(i).(j) - (e.grand_a.(i).(j0) * e.a.(j))) n
          done
	end
    done;
    
(*
  mise a jour de C et D. La colonne j0 vaut 0 dans C, car la variable
  j0 a ete eliminee, et les variables de depart ne s'expriment plus
  en fonction d'elle.
*)
    for i=0 to (pred nb_var_dep) do
      for j=0 to (pred nb_cst) do
        e.grand_d.(i).(j) <- 
        zmod (e.grand_d.(i).(j) - (e.grand_c.(i).(j0) * e.b.(j))) n
      done;
      for j=0 to (pred nb_var) do
        if j <> j0 
        then 
	  e.grand_c.(i).(j) <- 
          zmod (e.grand_c.(i).(j) - (e.grand_c.(i).(j0) * e.a.(j))) n
      done
    done;
    
(*
  A, B, C, D ont ete mis a jour, mais il reste a eliminer effectivement
  la ligne i0 (correspondant a l'equation eliminee) dans A et B, et
  la colonne j0 (correspondant a la variable eliminee) dans A et C.
  Ce sera fait par des decalages.
*)
    for i=i0 to (nb_eq - 2) do
      for j=0 to (pred nb_cst) do
	e.grand_b.(i).(j) <- e.grand_b.(i+1).(j)
      done;
      for j=0 to (pred nb_var) do
        e.grand_a.(i).(j) <- e.grand_a.(i+1).(j)
      done
  done;
    
    for j=j0 to (nb_var -2) do
      for i=0 to (nb_eq - 2) do
        e.grand_a.(i).(j) <- e.grand_a.(i).(j+1)
      done;
      for i=0 to (pred e.nv) do
        e.grand_c.(i).(j) <- e.grand_c.(i).(j+1)
      done
    done;
(*
  mise a jour du nombre de variables et d'equations courants
*)
    e.nvc <- pred e.nvc;
    e.ne <- pred e.ne;
    e
      
let etape2 i0 j0 d e = 
(*
  Tous les coefficients variables de l'equation i0 sont des multiples 
  de c=ai0j0, et les coefficients constants sont tous des multiples de 
  d = pgcd(c,n).
  E <=> 
  c*(a00'y0 +ai01'y1 +...+yj0 +...+ai0(nb_var-1)'y(nb_var-1)) +bi0 =0 mod n
  
  bi0 = d*bi0', donc
  E <=>
 d*((c/d)*(a00'y0 +ai01'y1 +...+yj0 +...+ai0(nb_var-1)'y(nb_var-1)) +bi0')=0 
                                                                         mod n
  E <=>
  (c/d)*(a00'y0 +ai01'y1 +...+yj0 +...+ai0(nb_var-1)'y(nb_var-1)) +bi0' = 0 
                                                                      mod (n/d)
  
  or c/d et n/d sont premiers entre eux, et donc c/d est inversible 
  modulo n/d. Soit inv_(n/d)(c/d) l'inverse de c/d modulo n/d.
  E <=>                          ^
  yj0 = - (a00'y0 +ai01'y1 +...+yj0 +...+ai0(nb_var-1)'y(nb_var-1)) 
        - inv_(n/d)(c/d)*bi0' + n/d*y'j0
  on elimine yj0 du systeme grace a cette equation, et ce faisant on 
  introduit une nouvelle variable y'j0, mais le nombre d'equations a 
  diminue d'un: E n'est plus presente.
*)

  let nb_var = e.nvc
  and nb_var_dep = e.nv
  and nb_cst = e.nc
  and nb_eq = e.ne
  and c = e.grand_a.(i0).(j0)
  and n = e.modulo in
  let n' = n/d in

(*
  on met dans a et b les coefficients de l'equation i0
*)
    for j=0 to (pred nb_var) do
      e.a.(j) <- e.grand_a.(i0).(j)
    done;
    for j=0 to (pred nb_cst) do
      e.b.(j) <- e.grand_b.(i0).(j)
    done;

(*
  mise a jour de A,B,C,D. 
  la ligne i0 (dans A et B) correspond a l'equation utilisee, 
  et l'information sera conservee dans la partie X = CYn + D,
  la colonne j0 (dans A) correspond a la variable remplacee. 
*)

(* 
   mise a jour de B.
*)

    for j=0 to (pred nb_cst) do
      let coef = inverse_modulo n' (e.b.(j)/n) in 
	for i=0 to (pred nb_eq) do 
          if i <> i0 
          then 
	    e.grand_b.(i).(j) <- 
            zmod (e.grand_b.(i).(j) - (e.grand_a.(i).(j0) * coef)) n
        done
    done;

(*
   mise a jour de A.
*)

    for j=0 to (pred nb_var) do
     if j <> j0 
     then 
       let coef = e.a.(j)/c in
         for i=0 to (pred nb_eq) do
           if i <> i0 
           then 
	     e.grand_a.(i).(j) <- 
             zmod (e.grand_a.(i).(j) - (e.grand_a.(i).(j0) * coef)) n
         done
     else 
       for i=0 to (pred nb_eq) do
         if i <> i0 
         then e.grand_a.(i).(j0) <- zmod (e.grand_a.(i).(j0) * n') n
       done
    done;
(*
  mise a jour de D.
*)
    for j=0 to (pred nb_cst) do
      let coef = inverse_modulo n' (e.b.(j) / n) in
	for i=0 to (pred nb_var_dep) do
          e.grand_d.(i).(j) <- 
          zmod (e.grand_d.(i).(j) - (e.grand_c.(i).(j0) * coef)) n
	done
    done;

(*
  mise a jour de C.
*)

    for j=0 to (pred nb_var) do 
      if j <> j0
      then let coef = zquo e.a.(j) c in
	for i=0 to (pred nb_var_dep) do
          e.grand_c.(i).(j) <- 
          zmod (e.grand_c.(i).(j) - (e.grand_c.(i).(j0) * coef)) n
	done
      else for i=0 to (pred nb_var_dep) do
	e.grand_c.(i).(j0) <- zmod (n' * e.grand_c.(i).(j0)) n
      done
    done;

(*
  A, B, C, D ont ete mis a jour, mais il reste a eliminer effectivement
  la ligne i0 (correspondant a l'equation eliminee) dans A et B.
  Ce sera fait par des decalages.
*)
    for i=i0 to (nb_eq - 2) do
      for j=0 to (pred nb_cst) do
	e.grand_b.(i).(j) <- e.grand_b.(i+1).(j)
      done;
      for j=0 to (pred nb_var) do
        e.grand_a.(i).(j) <- e.grand_a.(i+1).(j)
      done
    done;
    
(*
  mise a jour du nombre d'equations courant
*)
    e.ne <- pred e.ne;
    e

let etape3 i0 j0 e = 
(*
  elimination de la variable j0 dans le systeme grace a l'equation i0
  ou elle apparait avec un coefficent non-nul et non-inversible
*)
  let nb_var = e.nvc
  and nb_var_dep = e.nv
  and nb_cst = e.nc
  and nb_eq = e.ne
  and c = e.grand_a.(i0).(j0)
  and n = e.modulo in

(*
  On est dans le cas ou  yj0 est eliminee au profit de d'une nouvelle 
  variable y'j0 telle que
  y'j0 = [ai01/ai0j0] y1 + ...+ [ai0j0/ai0j0] yj0 + ... + [ai0n/ai0j0] yn
  [a/b] est defini comme le produit du signe de a/b et du quotient 
  entier des valeurs absolues de a et b. 
  Nota : l'equation i0 est toujours presente.
*)

(*
  on met dans a et b les coefficients de l'equation i0
*)
    for j=0 to (pred nb_var) do
      e.a.(j) <- e.grand_a.(i0).(j)
    done;
    for j=0 to (pred nb_cst) do
      e.b.(j) <- e.grand_b.(i0).(j)
    done;

(*
  mise a jour de C. Le matrice de constantes D ne change pas. 
*)
    for j=0 to (pred nb_var) do 
      if j <> j0
      then 
	let coef = zquo e.a.(j) c in
          for i=0 to (pred nb_var_dep) do
            e.grand_c.(i).(j) <- 
            zmod (e.grand_c.(i).(j) - (e.grand_c.(i).(j0) * coef)) n
	  done
    done;

(*
  mise a jour de la matrice A, la colonne j0 correspond a la nouvelle 
  variable, mais ne change pas. La matrice de constantes B ne change pas. 
*)
    for j=0 to (pred nb_var) do
      if j <> j0
      then 
	let coef = zquo e.a.(j) c in
          for i=0 to (pred nb_eq) do
            e.grand_a.(i).(j) <- 
            zmod (e.grand_a.(i).(j) - (e.grand_a.(i).(j0) * coef)) n
	  done
    done;
    
(*
  le nombre d'equations a resoudre et le nombre de variables courant
  n'ont pas change. 
*)
    e

let appliquer_etape e =
(* show e; *)
  let nb_var = e.nvc
  and nb_eq = e.ne
  and n = e.modulo in
    try 
      let (i0,j0,invc) = inversc e n nb_eq nb_var e.grand_a in
	etape1 i0 j0 invc e
    with 
	Not_found -> 
	  begin
	    try 
	      let l = ppc n nb_eq nb_var e.grand_a in
              let (i0,j0) = 
		try List.find (selection23 e) l
		with Not_found -> (List.hd l) in
              let c = e.grand_a.(i0).(j0) in
                if (divides c nb_var e.grand_a.(i0)) 
                then 
		  let d = pgcd c n in
                    etape2 i0 j0 d e
                else etape3 i0 j0 e
            with 
		Matrice_Nulle -> raise Matrice_Nulle
              | Systeme_Sans_Solution -> raise Systeme_Sans_Solution
	  end
	  

let rec repeter_etape e = 
  try repeter_etape (appliquer_etape e)
  with 
      Matrice_Nulle -> e
    | Systeme_Sans_Solution -> raise Systeme_Sans_Solution

let grand_b_est_nul e = 
  let nb_cst = e.nc 
  and nb_eq = e.ne in
    try 
      for i=0 to (pred nb_eq) do
        for j=0 to (pred nb_cst) do
          if (e.grand_b.(i).(j) <> 0)
          then raise Exit
        done
      done;
      true
    with Exit -> false
	
	
let i_solve_modulo n vect_type mat pe_edge = 
  let e = init_modulo n mat vect_type pe_edge in 
    try 
      let _ = 
	try 
	  repeter_etape e 
	with 
	    x -> 
	      print_string "trouve\n";
	      raise x in
	if (grand_b_est_nul e)
	then 
	  begin
            let solutions_homogenes = 
	      Array.create_matrix e.nvc (e.nv + e.nc) 0 
            and solutions_particulieres = 
	      Array.create_matrix e.nc (e.nv + e.nc) 0 in
	    
              for j=0 to (pred e.nvc) do
		for i=0 to (pred e.nv) do
                  solutions_homogenes.(j).(i) <- e.grand_c.(i).(j)
		done
              done;
	    
              for j=0 to (pred e.nc) do
		for i=0 to (pred e.nv) do
                  solutions_particulieres.(j).(i) <- e.grand_d.(i).(j)
		done;
		solutions_particulieres.(j).(e.nv + j) <- 1
              done;
	      
              Without_identifications 
		(solutions_homogenes,solutions_particulieres)
              
          end

	else 
	  begin (* il faut faire des identifications sur les var. inst. *)
            let mat = Array.create_matrix e.ne e.nc 0 in
              for i=0 to (pred e.ne) do
		for j=0 to (pred e.nc) do
                  mat.(i).(j) <- e.grand_b.(i).(j)
		done
              done;
              let cst_vect_type = Array.copy vect_type in
		for i=0 to (pred (Array.length vect_type)) do
		  cst_vect_type.(i) <- vect_type.(i) - vect_type.(0)
		done;
		let identifications = dioph_solve cst_vect_type mat in
		let solutions_homogenes = 
		  Array.create_matrix e.nvc (e.nv + e.nc) 0 
		and solutions_particulieres = 
		  Array.create_matrix (Array.length identifications) 
                    (e.nv + e.nc) 0 in
		
		  for j=0 to (pred e.nvc) do
		    for i=0 to (pred e.nv) do
                      solutions_homogenes.(j).(i) <- e.grand_c.(i).(j)
		    done
		  done;
		
		  for j=0 to (pred (Array.length identifications)) do
		    for i=0 to (pred e.nv) do
	              for k=0 to (pred e.nc) do
			solutions_particulieres.(j).(i) <- 
			solutions_particulieres.(j).(i) + 
			(e.grand_d.(i).(k) * identifications.(j).(k))
	              done
		    done;
		    for i=e.nv to (pred (e.nv + e.nc)) do
	              solutions_particulieres.(j).(i) <- 
                      identifications.(j).(i - e.nv)
		    done
		  done; 
		
		  With_identifications 
		    (solutions_homogenes,solutions_particulieres)
		    
          end
	
    with Systeme_Sans_Solution -> No_sol
	

