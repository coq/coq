
open Util
open Miniml

(* [occurs : int -> ml_ast -> bool]
   [occurs k M] returns true if (Rel k) occurs in M. *)

let rec occurs k = function
  | MLrel i          -> i=k
  | MLapp(t,argl)    -> (occurs k t) or (occurs_list k argl)
  | MLlam(_,t)       -> occurs (k+1) t
  | MLcons(_,_,argl) -> occurs_list k argl
  | MLcase(t,pv)     -> 
      (occurs k t) or
      (List.exists (fun (k',t') -> occurs (k+k') t')
      	 (array_map_to_list (fun (_,l,t') -> 
      	       	           let k' = List.length l in (k',t')) pv))
  | MLfix(_,_,l,cl)  -> let k' = List.length l in occurs_list (k+k') cl
  | _                -> false

and occurs_list k l =
  List.exists (fun t -> occurs k t) l

