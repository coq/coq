(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Piles
open Type_de_donnees_dioph



let is_solution nb_eq n = 
  List.for_all (function i -> (i = 0)) (Array.to_list n.defaut)


let extract_solution n = 
  let l = Array.length n.n_uplet in
  let s = Array.create l 0 in
    for i=0 to (pred l) do
      s.(i) <- n.n_uplet.(i).valeur
    done;
    s



let add_solution s my_state = 
  my_state.sol <- s::(my_state.sol)


let add_contraint_noeud nb_var s n = 

  (* calcul de c, la contrainte associee a la solution s pour le noeud n *)
  let c = Array.create nb_var 0 in
    for i = 0 to (pred (nb_var)) do
      if (s.(i) > n.n_uplet.(i).valeur)
      then c.(i) <- s.(i) -  n.n_uplet.(i).valeur
    done;

  (* test pour savoir si c est comparable avec une contrainte deja presente *)
(*
    let ajout_effectif_de_c = ref false in
    let rec ajout_soigneux_c = fun
      [] res -> ajout_effectif_de_c := true ; c::res
    | (y::l) res -> begin
                    match (comparaison c y) with
                    EQUIVALENT -> (y::l) @ res
                  | STRICTEMENT_INFERIEUR -> (ajout_soigneux_c l res)
                  | STRICTEMENT_SUPERIEUR -> (y::l) @ res
                  | INCOMPARABLE -> ajout_soigneux_c l (y::res)
              end
    in 
    let new_contraint = ajout_soigneux_c n.contraint []
    in if (!ajout_effectif_de_c)
       then begin
            n.contraint <- new_contraint;
*)
    begin 
      n.contraint <- c::n.contraint;

  (* calcul des composantes de n.n_uplet, gelees par l'ajout de c *)
      let latitude = ref 0 
      and indice_latitude = ref nb_var in
	try 
	  for i = 0 to (pred nb_var) do
            latitude := !latitude + c.(i);
            if (!latitude > 1) 
            then raise Exit;
            if c.(i) > 0
            then indice_latitude := i
          done;
          if (!latitude = 1)
          then n.n_uplet.(!indice_latitude).frozen <- true
        with Exit -> ()
    end
           


(*
let add_contraint_noeud = 
      Time_profiler.profile3 "add_contraint_noeud" add_contraint_noeud;;
*)

let add_contraint_stack nb_var solution my_stack = 
  do_pile (add_contraint_noeud nb_var solution) my_stack


(*
let add_contraint_stack = 
      Time_profiler.profile3 "add_contraint_stack" add_contraint_stack;;
*)


let add_contraint solution my_state =
  let nb_var = my_state.nv 
  and my_state_st = my_state.st in 
    add_contraint_stack nb_var solution my_state_st


(*
let add_contraint = Time_profiler.profile2 "add_contraint" add_contraint;;
*)

