(***************************************************************************

  Various basic functions on lists : body

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

let rec power_generic f a x = function
    0 -> a
  | 1 -> x
  | 2 -> f x x
  | n -> 
      let y = (power_generic f a x (n/2)) in
	if (n mod 2)=0 
	then  f y y
	else  f x (f y y)

let power x = power_generic (@) [] x;;


(* For compatibility with CSL *)

let add x l = if List.mem x l then l else x::l;;
  
let union l1 l2 = List.fold_right add l1 l2;;

let intersect l1 l2 = 
  List.fold_right (fun e l->if List.mem e l2 then e::l else l) l1 [];;

let index a = 
  let rec f n = function 
      b::tl -> if b=a then n else f (n+1) tl
    | _ -> raise Not_found 
  in f 0;;

let except = 
  let rec f a = function 
      b::tl -> if a=b then tl else b::(f a tl)
    | _ -> [] 
  in f;;

let rec remove x l = 
  match l with
      ((y,_) as z)::tl -> if x=y then tl else z::(remove x tl)
    | _ -> []
;;  

let flat_map f l = 
  List.fold_right (fun x l->(f x)@l) l []
;;

let subtract f = function
    [] -> f
  | e  -> 
      let rec subtract_e = function
          [] -> []
       	| elem::l -> 
	    if List.mem elem e then subtract_e l else elem :: subtract_e l 
      in subtract_e f
;;


let rec do_list_combine f = function
    [],[] -> ()
  | a::al,b::bl -> f (a,b); do_list_combine f (al,bl)
  | _ -> raise (Invalid_argument "do_list_combine")
;;


let rec map_filter f p = function
    [] -> []
  | a::al -> 
      if (p a)
      then (f a)::(map_filter f p al)
      else map_filter f p al


let rec map_with_exception e f = function
    [] -> []
  | h :: t ->
      let partial_res = map_with_exception e f t in
	try 
	  (f h) :: partial_res
	with e ->  partial_res

(* We should do something better : consider [\n] and [\t].*)

let rec split s =
  try
    let n = String.index s ' '
    in
      if n=0
      then
	split (String.sub s 1 (pred (String.length s)))
      else
	(String.sub s 0 n)
	::(split (String.sub s (n+1) ((String.length s)-n-1)))
  with Not_found -> if s="" then [] else [s]
;;


let mapi f l =
  let rec rec_mapi n = function 
      [] -> []
    | h::t -> (f n h)::(rec_mapi (n+1) t) in
    rec_mapi 0 l 

let flat_mapi f l =
  let rec rec_flat_mapi n = function
      [] -> []
    | h::t -> (f n h) @ (rec_flat_mapi (n+1) t) in
    rec_flat_mapi 0 l


let rec fold_right_env f env l =
  match l with
    | [] -> env,[]
    | h::t ->
	let env1,e1 = f env h in
	let envk,l' = fold_right_env f env1 t in
	envk,e1::l'

