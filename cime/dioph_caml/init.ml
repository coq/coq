(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Piles;;
open Type_de_donnees_dioph;;


let init_state nb_eq v_type system = 
 let nb_var = v_type.(pred (Array.length v_type))
 in
 let td = Array.create_matrix nb_var nb_eq 0
 in for i=0 to (pred nb_eq) do
    for j=0 to (pred nb_var) do
    td.(j).(i) <- system.(i).(j)
    done
    done;

  (* initialisation de la pile *)

    let p = pile_vide nb_var in
    for j=0 to (pred nb_var) do

  (* creation du noeud correspondant au jieme vecteur canonique *)
  (* puis empilement                                            *)

    let ej = Array.create nb_var {frozen = false; valeur = 0}
    in for i=0 to (pred nb_var) do
       ej.(i) <- {frozen = (i < j); valeur = if i=j then 1 else 0}
       done;

  (* gel des composantes dans les autres theories si la composante 
     correspond a une theorie d'instanciation *)
       if (v_type.(0) <= j)
       then begin
            ej.(j).frozen <- true;
            for i=1 to (pred (pred (Array.length v_type))) do
            if (v_type.(i) > j) 
            then for k=v_type.(i) to (pred (v_type.(i+1))) do
                 ej.(k).frozen <- true
                 done
            done
            end;


   let d = Array.create nb_eq 0
   in for i=0 to (pred nb_eq) do
      d.(i) <- system.(i).(j)
      done;

   let nj = {n_uplet = ej;
             defaut = d;
             contraint = []}
   in empile nj p
  
   done;



   {ne = nb_eq;
    nv = nb_var;
    vt = v_type;
    aci_syst = [||];
    syst = system;
    tab_def = td;
    st = p;
    sol = []}
;;

(*
let init_state = Time_profiler.profile3 "init_state" init_state
;;
*)

