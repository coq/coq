(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Orderings_generalities

let rec rec_comparaison v1 v2 n i = function
    Equivalent ->
      if i < n
      then
	if v1.(i) = v2.(i) 
	then rec_comparaison v1 v2 n (succ i) Equivalent
	else 
	  if v1.(i) < v2.(i)
	  then rec_comparaison v1 v2 n (succ i) Less_than
	  else rec_comparaison v1 v2 n (succ i) Greater_than
      else Equivalent

  | Less_than ->
      if i < n
      then
	if v1.(i) <= v2.(i) 
	then rec_comparaison v1 v2 n (succ i) Less_than
	else Uncomparable
      else Less_than

  | Greater_than ->
      if i < n
      then
	if v1.(i) >= v2.(i) 
	then rec_comparaison v1 v2 n (succ i) Greater_than
	else Uncomparable
      else Greater_than

  | Uncomparable -> Uncomparable
  | _ -> assert false


let comparaison v1 v2 = 
  let n1 = Array.length v1
  and n2 = Array.length v2 in
    if n1 <> n2
    then 
      failwith 
	"comparaison : comparaison sur deux vecteurs de longueurs differentes"
    else 
      rec_comparaison v1 v2 n1 0 Equivalent

(*
let comparaison = Time_profiler.profile2 "comparaison" comparaison
*)




