open Names
open Pp

open Libnames

let mk_prefix pre id = id_of_string (pre^(string_of_id id))
let mk_rel_id = mk_prefix "R_"

let msgnl m =
  ()

let invalid_argument s = raise (Invalid_argument s)

(* let idtbl = Hashtbl.create 29 *)
(* let reset_name () = Hashtbl.clear idtbl *)

(* let fresh_id s = *)
(*   try *)
(*     let id = Hashtbl.find idtbl s in *)
(*     incr id; *)
(*     id_of_string (s^(string_of_int !id)) *)
(*   with Not_found -> *)
(*     Hashtbl.add idtbl s (ref (-1)); *)
(*     id_of_string s *)

(* let fresh_name s = Name (fresh_id s) *)
(* let get_name ?(default="H") = function *)
(*   | Anonymous -> fresh_name default *)
(*   | Name n -> Name n *)



let fresh_id avoid s = Nameops.next_ident_away (id_of_string s) avoid

let fresh_name avoid s = Name (fresh_id avoid s)

let get_name avoid ?(default="H") = function
  | Anonymous -> fresh_name avoid default
  | Name n -> Name n

let array_get_start a =
  try 
    Array.init
      (Array.length a - 1)
      (fun i -> a.(i))
  with Invalid_argument "index out of bounds" -> 
    invalid_argument "array_get_start"
      
let id_of_name = function
    Name id -> id
  | _ -> raise Not_found

let locate  ref =
    let (loc,qid) = qualid_of_reference ref in
    Nametab.locate qid

let locate_ind ref =
  match locate ref with
    | IndRef x -> x
    | _ -> raise Not_found

let locate_constant ref =
  match locate ref with
    | ConstRef x -> x
    | _ -> raise Not_found


let locate_with_msg msg f x =
  try
    f x
  with
    | Not_found -> raise (Util.UserError("", msg))
    | e -> raise e


let filter_map filter f =
  let rec it = function
    | [] -> []
    | e::l ->
	if filter e
	then
	  (f e) :: it l
	else it l
  in
  it


let chop_rlambda_n  =
  let rec chop_lambda_n acc n rt =
      if n == 0
      then List.rev acc,rt
      else
	match rt with
	  | Rawterm.RLambda(_,name,t,b) -> chop_lambda_n ((name,t)::acc) (n-1) b
	  | _ -> raise (Util.UserError("chop_rlambda_n",str "chop_rlambda_n: Not enough Lambdas"))
  in
  chop_lambda_n []

let chop_rprod_n  =
  let rec chop_prod_n acc n rt =
      if n == 0
      then List.rev acc,rt
      else
	match rt with
	  | Rawterm.RProd(_,name,t,b) -> chop_prod_n ((name,t)::acc) (n-1) b
	  | _ -> raise (Util.UserError("chop_rprod_n",str "chop_rprod_n: Not enough products"))
  in
  chop_prod_n []



let list_union_eq eq_fun l1 l2 =
  let rec urec = function
    | [] -> l2
    | a::l -> if List.exists (eq_fun a) l2 then urec l else a::urec l
  in
  urec l1

let list_add_set_eq eq_fun x l =
  if List.exists (eq_fun x) l then l else x::l

  


let const_of_id id =
  let _,princ_ref = 
    qualid_of_reference (Libnames.Ident (Util.dummy_loc,id))
  in
  try Nametab.locate_constant princ_ref
  with Not_found -> Util.error ("cannot find "^ string_of_id id)

let def_of_const t =
   match (Term.kind_of_term t) with
    Term.Const sp -> 
      (try (match (Global.lookup_constant sp) with
             {Declarations.const_body=Some c} -> Declarations.force c
	     |_ -> assert false)
       with _ -> assert false)
    |_ -> assert false

let coq_constant s =
  Coqlib.gen_constant_in_modules "RecursiveDefinition" 
    (Coqlib.init_modules @ Coqlib.arith_modules) s;;

let constant sl s =
  constr_of_reference
    (Nametab.locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let find_reference sl s =
    (Nametab.locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let eq = lazy(coq_constant "eq")
let refl_equal = lazy(coq_constant "refl_equal")

