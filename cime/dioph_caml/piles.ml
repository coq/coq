(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Type_de_donnees_dioph


let noeud_vide () = {n_uplet = [||];
                     defaut = [||];
                     contraint = []}

let pile_vide n = 
    let nv = noeud_vide () in
    let vp = Array.create n nv in
    {hmax = n;
     h = 0;
     v = vp}

let empile x p = 
    if ( p.h < p.hmax)
    then begin
         p.v.(p.h) <- x;
         p.h <- succ p.h
	 end
    else failwith "empile"
         

let sommet p =
    if (p.h > 0)
    then begin
         p.h <- (pred p.h);
         p.v.(p.h)
         end
   else failwith "sommet"

let hauteur p = p.h

let do_pile f p =
   for i=0 to (pred p.h) do
       f p.v.(i)
   done
