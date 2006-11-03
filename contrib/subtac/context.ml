open Term
open Names

type t = rel_declaration list (* name, optional coq interp, algorithmic type *)

let assoc n t = 
  let _, term, typ = List.find (fun (x, _, _) -> x = n) t in
    term, typ

let assoc_and_index x l =
  let rec aux i = function
      (y, term, typ) :: tl -> if x = y then i, term, typ else aux (succ i) tl
    | [] -> raise Not_found
  in aux 0 l

let id_of_name = function
    Name id -> id
  | Anonymous -> raise (Invalid_argument "id_of_name")
(*

let subst_ctx ctx c = 
  let rec aux ((ctx, n, c) as acc) = function
      (name, None, typ) :: tl -> 
	aux (((id_of_name name, None, rel_to_vars ctx typ) :: ctx), 
	     pred n, c) tl
    | (name, Some term, typ) :: tl ->
	let t' = Term.substnl [term] n c in
	  aux (ctx, n, t') tl
    | [] -> acc
  in 
  let (x, _, z) = aux ([], pred (List.length ctx), c) (List.rev ctx) in 
    (x, rel_to_vars x z)
*)

let subst_env env c = (env, c)
