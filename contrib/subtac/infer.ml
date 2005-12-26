open Natural
open Names
open Term
open Rawterm
open Util
open Sast
open Scoq
open Pp
open Ppconstr

let ($) f g = fun x -> f (g x)

let app_option f default = function Some x -> f x | None -> default

let concat_map f l = 
  let rec aux accu = function
      [] -> List.rev accu
    | hd :: tl -> 
	aux (f hd @ accu) tl
  in aux [] l

let unique l = 
  let l' = List.sort Pervasives.compare l in
  let rec aux accu = function
      [] -> List.rev accu
    | x :: (y :: _) as tl when x = y -> 
	aux accu tl
    | hd :: tl ->
	aux (hd :: accu) tl
  in aux [] l'

type term_pp = Pp.std_ppcmds

type subtyping_error = 
  | UncoercibleInferType of loc * term_pp * term_pp
  | UncoercibleInferTerm of loc * term_pp * term_pp * term_pp * term_pp
  | UncoercibleRewrite of term_pp * term_pp

type typing_error = 
  | NonFunctionalApp of loc * term_pp * term_pp
  | NonConvertible of loc * term_pp * term_pp
  | NonSigma of loc * term_pp

exception Subtyping_error of subtyping_error
exception Typing_error of typing_error
  
exception Debug_msg of string

let typing_error e = raise (Typing_error e)
let subtyping_error e = raise (Subtyping_error e)

type sort = Term.sorts
type sort_loc = sort located

(* Decorated terms *)
type dterm = 
    DRel of nat
  | DLambda of (name located * dtype_loc) * dterm_loc * dtype_loc
  | DApp of dterm_loc * dterm_loc * dtype_loc
  | DLetIn of (name located) * dterm_loc * dterm_loc * dtype_loc
  | DLetTuple of (name located * dtype_loc * dtype_loc) list * dterm_loc * dterm_loc * dtype_loc
  | DIfThenElse of dterm_loc * dterm_loc * dterm_loc * dtype_loc
  | DSum of ((name located) * dterm_loc) * (dterm_loc * dtype_loc) * dtype_loc
  | DCoq of constr * dtype_loc
and dterm_loc = dterm located
and dtype = 
  | DTApp of dtype_loc * dtype_loc * dtype_loc * sort_loc
  | DTPi of (name located * dtype_loc) * dtype_loc * sort_loc
  | DTSigma of (name located * dtype_loc) * dtype_loc * sort_loc
  | DTSubset of (identifier located * dtype_loc) * dtype_loc * sort_loc
  | DTRel of nat
  | DTTerm of dterm_loc * dtype_loc * sort_loc
  | DTSort of sort_loc
  | DTInd of (identifier located) * dtype_loc * inductive * sort_loc
  | DTCoq of types * dtype_loc * sort_loc
and dtype_loc = dtype located

let print_name = function
    Name s -> str (string_of_id s)
  | Anonymous -> str "_"

let print_name_loc (_, n) = print_name n

let string_of_list l =
  let rec aux = function
      hd :: ((_ :: _) as tl) ->
	hd ++ str "," ++ aux tl
    | hd :: [] -> hd
    | [] -> mt()
  in aux l

type context = (name * dtype_loc) list

let print_dtype_locref : (context -> dtype_loc -> std_ppcmds) ref = 
  ref (fun ctx t -> mt())

let print_context ctx = 
  let cmds, _ = 
    List.fold_right 
      (fun (x, t) (acc, ctx) ->
	 let xpr = print_name x ++ str " : " ++ !print_dtype_locref ctx t in
	   (xpr :: acc), ((x, t) :: ctx))
      ctx ([], [])
  in string_of_list cmds

let type_of_rel ctx n = 
  try snd (List.nth ctx n)
  with e ->
    debug 3 (str "Error in type_of_rel, searching for index " ++ str (string_of_int n)
	     ++ str " in context " ++ print_context ctx ++ str ": " ++
	     str (Printexc.to_string e));
    raise e

let name_of_rel ctx n = 
  try fst (List.nth ctx n)
  with e ->
    debug 3 (str "Error in name_of_rel, searching for index " ++ str (string_of_int n)
	     ++ str " in context " ++ print_context ctx ++ str ": " ++
	     str (Printexc.to_string e));
    raise e

let rec sort_of_dtype ctx = function
  | DTApp (_, _, _, x) 
  | DTPi (_, _, x)
  | DTSigma (_, _, x)
  | DTSubset (_, _, x)
  | DTTerm (_, _, x)
  | DTSort x
  | DTInd (_, _, _, x)
  | DTCoq (_, _, x) -> x
  | DTRel i -> sort_of_dtype_loc ctx (type_of_rel ctx i)

and sort_of_dtype_loc ctx (_, t) = sort_of_dtype ctx t
    
let rec no_var n (loc, t) = 
  match t with
  | DTApp (x, y, t, _) -> (no_var n x) && (no_var n y)
  | DTPi ((_, x), y, _) -> (no_var n x) && (no_var (succ n) y)
  | DTSigma ((_, x), y, _) -> (no_var n x) && (no_var (succ n) y)
  | DTSubset ((_, x), y, _) -> (no_var n x) && (no_var (succ n) y)
  | DTRel i when i <> n -> false
  | x -> true
      

let rec lift_rec n k (loc, t) = 
  let t' = 
    match t with
      | DTApp (x, y, t, s) -> DTApp (lift_rec n k x, lift_rec n k y,
				     lift_rec n k t, s)
      | DTPi ((id, x), y, s) -> 
	  DTPi ((id, lift_rec n k x), lift_rec n (succ k) y, s)
      | DTSigma ((id, x), y, s) -> 
	  DTSigma ((id, lift_rec n k x), lift_rec n (succ k) y, s)
      | DTSubset ((id, x), y, s) -> 
	  DTSubset ((id, lift_rec n k x), lift_rec n (succ k) y, s)
      | (DTRel i) as x -> 
	  if i < k then x else DTRel (n + i)
      | DTTerm (t, tt, s) -> DTTerm (lift_term_rec n k t, lift_rec n k tt, s)
      | DTCoq (c, t, s) -> DTCoq (Term.liftn n k c, lift_rec n k t, s)
      | DTSort _
      | DTInd _ -> t
  in loc, t'

and lift_term_rec n k (loc, s) =
  let s' = 
    match s with
	DRel i ->
	  if i < k then s else DRel (n + i)
      | DLambda ((nl, dt), dt', dtlam) ->
	  DLambda ((nl, lift_rec n k dt), lift_term_rec n (succ k) dt', 
		   lift_rec n k dtlam)	    
      | DApp (dte, dte', dt) ->
	  DApp (lift_term_rec n k dte, lift_term_rec n k dte', lift_rec n k dt)
      | DLetIn (nl, dte, dte', dt) ->
	  DLetIn (nl, lift_term_rec n k dte, lift_term_rec n (succ k) dte', 
		  lift_rec n k dt)
      | DLetTuple (nl, dte, dte', dt) ->
	  DLetTuple (nl, lift_term_rec n k dte, 
		     lift_term_rec n (List.length nl + k) dte', 
		     lift_rec n k dt)
      | DIfThenElse (db, de, de', dt) ->
	  DIfThenElse (lift_term_rec n k db, lift_term_rec n k de,
		       lift_term_rec n k de', lift_rec n k dt)
      | DSum ((x, tx), (ty, dty), dt) ->
	  DSum ((x, lift_term_rec n k tx), 
		(lift_term_rec n (succ k) ty, lift_rec n (succ k) dty),
		lift_rec n k dt)
      | DCoq (c, t) -> DCoq (Term.liftn n k c, lift_rec n k t)	  
  in loc, s'
	
let lift n t = lift_rec n 0 t
let lift_term n t = lift_term_rec n 0 t

let rec unlift_rec n k (loc, t) = 
  let t' = 
    match t with
      | DTApp (x, y, t, s) -> DTApp (unlift_rec n k x, unlift_rec n k y, unlift_rec n k t, s)
      | DTPi ((id, x), y, s) -> 
	  DTPi ((id, unlift_rec n k x), unlift_rec n (succ k) y, s)
      | DTSigma ((id, x), y, s) -> 
	  DTSigma ((id, unlift_rec n k x), unlift_rec n (succ k) y, s)
      | DTSubset ((id, x), y, s) -> 
	  DTSubset ((id, unlift_rec n k x), unlift_rec n (succ k) y, s)
      | (DTRel i) as x -> 
	  if i < k then x else DTRel (i - n)
      | DTTerm (t, tt, s) -> DTTerm (unlift_term_rec n k t, unlift_rec n k tt, s)
      | DTCoq (c, t, s) -> DTCoq (c, unlift_rec n k t, s)
      | DTSort _
      | DTInd _ -> t
  in loc, t'

and unlift_term_rec n k (loc, s) =
  let s' = 
    match s with
	DRel i ->
	  if i < k then s else DRel (i - n)
      | DLambda ((nl, dt), dt', dtlam) ->
	  DLambda ((nl, unlift_rec n k dt), unlift_term_rec n (succ k) dt', 
		   unlift_rec n k dtlam)	    
      | DApp (dte, dte', dt) ->
	  DApp (unlift_term_rec n k dte, unlift_term_rec n k dte', unlift_rec n k dt)
      | DLetIn (nl, dte, dte', dt) ->
	  DLetIn (nl, unlift_term_rec n k dte, unlift_term_rec n (succ k) dte', 
		  unlift_rec n k dt)
      | DLetTuple (nl, dte, dte', dt) ->
	  DLetTuple (nl, unlift_term_rec n k dte, 
		     unlift_term_rec n (List.length nl + k) dte', 
		     unlift_rec n k dt)
      | DIfThenElse (db, de, de', dt) ->
	  DIfThenElse (unlift_term_rec n k db, unlift_term_rec n k de,
		       unlift_term_rec n k de', unlift_rec n k dt)
      | DSum ((x, tx), (ty, dty), dt) ->
	  DSum ((x, unlift_term_rec n k tx), 
		(unlift_term_rec n k ty, unlift_rec n k dty),
		unlift_rec n k dt)
      | DCoq (c, t) -> DCoq (c, unlift_rec n k t)	  
  in loc, s'

let unlift n t = unlift_rec n 0 t

let rec type_of_dterm ctx t =
  match t with
      DRel (i) -> 
	(try let t = type_of_rel ctx i in lift (succ i) t
	 with e -> debug 3 (str "Couldn't find type of rel in type_of_dterm");
	   raise e)
    | DLambda (_, _, dt) -> dt
    | DApp (dte, dte', dt) -> dt
    | DLetIn (nl, dte, dte', dt) -> dt
    | DLetTuple (nl, dte, dte', dt) -> dt
    | DIfThenElse (db, de, de', dt) -> dt
    | DSum (_, _, dt) -> dt
    | DCoq (_, dt) -> dt
  
let type_of_dterm_loc ctx (_, t) = type_of_dterm ctx t
      
let rec subst_term_type_rec (loc, s) t k =
  let s' = 
    match s with
	DRel i ->
	  if k < i then DRel (pred i)
	  else if k = i then 
	    match snd (lift_rec k 0 t) with
		DTRel i -> DRel i
	      | DTTerm (t, _, _) -> snd t
	      | _ -> failwith ("Substitution of a type in a term")
	  else (* k > i *) s
      | DLambda ((ln, dt), e, t') -> 
	  DLambda ((ln, subst_rec dt t k), subst_term_type_rec e t (succ k),
		   subst_rec t' t k)
      | DApp (x, y, ta) -> 
	  DApp (subst_term_type_rec x t k, subst_term_type_rec y t k, subst_rec ta t k)
      | DLetIn (nl, e, e', t') ->
	  DLetIn (nl, subst_term_type_rec e t k, subst_term_type_rec e' t (succ k), 
		  subst_rec t' t k)
      | DLetTuple (nl, e, e', t') ->
	  DLetTuple (nl, subst_term_type_rec e t k, subst_term_type_rec e' t (k + List.length nl), 
		     subst_rec t' t k)
      | DIfThenElse (b, e, e', t') ->
	  DIfThenElse (subst_term_type_rec b t k, subst_term_type_rec e t k,
		       subst_term_type_rec e' t k, subst_rec t' t k)
      | DSum ((nl, dt), (dt', tt'), t') ->
	  DSum ((nl, subst_term_type_rec dt t k),
		(subst_term_type_rec dt' t (succ k), subst_rec tt' t (succ k)),
		subst_rec t' t k)
      | DCoq (c, dt) -> DCoq (c, subst_rec dt t k)
  in loc, s'

and subst_term_rec (loc, s) t k =
  let ttype =
    let dtype = type_of_dterm [] (snd t) in
      (dummy_loc, (DTTerm (t, dtype, sort_of_dtype_loc [] dtype))) 
  in
  let s' = 
    match s with
	DRel i ->
	  if k < i then DRel (pred i)
	  else if k = i then snd (lift_term_rec k 0 t)
	  else (* k > i *) s
      | DLambda ((ln, dt), e, t') -> 
	  (* !!! *)
	  DLambda ((ln, subst_rec dt ttype k), 
		   subst_term_rec e t (succ k), subst_rec t' ttype k)
      | DApp (x, y, ta) -> 
	  DApp (subst_term_rec x t k, subst_term_rec y t k, subst_rec ta ttype k)
      | DLetIn (nl, e, e', t') ->
	  DLetIn (nl, subst_term_rec e t k, subst_term_rec e' t (succ k), 
		  subst_rec t' ttype k)
      | DLetTuple (nl, e, e', t') ->
	  DLetTuple (nl, subst_term_rec e t k, subst_term_rec e' t 
		       (k + List.length nl), 
		     subst_rec t' ttype k)
      | DIfThenElse (b, e, e', t') ->
	  DIfThenElse (subst_term_rec b t k, subst_term_rec e t k,
		       subst_term_rec e' t k, subst_rec t' ttype k)
      | DSum ((nl, dt), (dt', tt'), t') ->
	  DSum ((nl, subst_term_rec dt t k),
		(subst_term_rec dt' t (succ k), subst_rec tt' tt' (succ k)),
		subst_rec t' ttype k)
      | DCoq (c, dt) -> 
	  
	  DCoq (c, subst_rec dt ttype k)
  in loc, s'

and subst_rec (loc, s) (t : dtype_loc) k = 
  let s' = 
    match s with
	DTPi ((id, a), b, s) -> DTPi ((id, subst_rec a t k), 
				      subst_rec b t (succ k), s)
      | DTSigma ((id, a), b, s) -> DTSigma ((id, subst_rec a t k), 
					    subst_rec b t (succ k), s)
      | DTSubset ((id, a), b, s) -> DTSubset ((id, subst_rec a t k), 
					      subst_rec b t (succ k), s)
      | DTRel i ->
	  if k < i then DTRel (pred i)
	  else if k = i then snd (lift k t)
	  else (* k > i *) s
      | DTApp (x, y, t', s) -> DTApp (subst_rec x t k, subst_rec y t k, 
				      subst_rec t' t k, s)
      | DTTerm (x, tt, s) -> DTTerm (subst_term_type_rec x t k, subst_rec tt t k, s)
      | DTCoq (c, ct, s) -> DTCoq (c, subst_rec ct t k, s)
      | DTSort _ | DTInd _ -> s
  in loc, s'

let subst s t = subst_rec s t 0
let subst_term s t = subst_term_rec s t 0

let rec print_dterm' ctx = function
  | DRel n -> 
      (try 
	 print_name (name_of_rel ctx n) ++ str ("(" ^ (string_of_int n) ^ ")")
       with Failure _ -> str ("UNBOUND_REL_" ^ (string_of_int n)))
  | DLambda ((namel, t),  e, _) -> str "fun " ++ print_name (snd namel) ++ spc () ++
      str ":" ++ spc () ++ print_dtype' ctx (snd t) ++ spc () ++ str "=>" ++ spc ()
      ++ print_dterm_loc ((snd namel, t) :: ctx) e
  | DApp (x, y, _) -> (print_dterm_loc ctx x) ++ spc () ++ 
      str "(" ++ (print_dterm_loc ctx y) ++ str ")"
  | DLetIn (n, e, e', _) -> 
      let te = 
	try type_of_dterm_loc ctx e 
	with e -> debug 3 (str "Couldn't find type_of_dterm in print_dterm'");
	  raise e
      in
	str "let" ++ spc () ++ print_name_loc n 
	++ spc () ++ str "=" ++ spc () ++ print_dterm_loc ctx e ++ 
	  print_dterm_loc ((snd n, te) :: ctx) e'
  | DLetTuple (nl, t, e, _) ->
      str "let" ++ spc () ++ str "(" ++ 
	string_of_list (List.rev_map (fun (n, _, _) -> print_name_loc n) nl)
      ++ str ")" ++ spc () ++ str "=" ++ spc () ++ 
	print_dterm_loc ctx t ++ str "in" ++ spc () ++
	print_dterm_loc ((List.map (fun (x, y, z) -> (snd x, y)) nl) @ ctx) e	
  | DIfThenElse (b, t, t', _) ->
      let ctx' = (Name (id_of_string "H"), (dummy_loc, DTRel 0)) :: ctx in
	str "if" ++ spc () ++ print_dterm_loc ctx b ++ spc () ++ 
	  str "then" ++ spc () ++ print_dterm_loc ctx' t ++ spc () ++
	  str "else" ++ spc () ++ print_dterm_loc ctx' t'
  | DSum ((n, t), (t', tt'), _) ->
      let ctx' = 
	try (snd n, type_of_dterm_loc ctx t) :: ctx
	with e -> debug 3 (str "Couldn't find type_of_dterm in print_dterm' (sum)");
	  raise e
      in
	str "(" ++ print_name (snd n) ++ str ":=" 
	++ print_dterm_loc ctx t ++ str "," 
	++ print_dterm_loc ctx' t' ++ str ":" 
	++ print_dtype_loc ctx' tt' ++ str ")"
  | DCoq (cstr, t) -> pr_term cstr

and print_dterm_loc ctx (_, x) = print_dterm' ctx x
  (*debug_msg 1 (str ":" ++ print_dtype_loc ctx (type_of_dterm ctx x))*)

and print_dtype' ctx = function
  | DTApp (x, y, t, s) -> print_dtype_loc ctx x ++ spc() ++ 
      str "(" ++ print_dtype_loc ctx y ++ str ")"
  | DTPi ((id, x), y, s) -> 
      str "(" ++ print_name_loc id ++ str ":" ++ print_dtype_loc ctx x ++ str ")"
      ++ spc() ++ print_dtype_loc ((snd id, x) :: ctx) y
  | DTSigma ((id, x), y, s) -> 
      str "[" ++ print_name_loc id ++ str ":" ++ print_dtype_loc ctx x ++ str "]"
      ++ spc() ++ print_dtype_loc ((snd id, x) :: ctx) y
  | DTSubset ((id, x), y, s) ->
      str "{" ++ str (string_of_id (snd id)) ++ str ":" ++ print_dtype_loc ctx x ++ str "|"
      ++ spc() ++ print_dtype_loc ((Name (snd id), x) :: ctx) y ++ str "}"	
  | (DTRel i) as x -> 
      (try print_name (name_of_rel ctx i) ++ str ("(" ^ (string_of_int i) ^ ")")
       with Failure _ -> str ("_UNBOUND_REL_" ^ (string_of_int i)))
  | DTTerm (t, tt, s) -> str "Term:(" ++ print_dterm_loc ctx t ++ str ")"
  | DTInd (n, t, i, s) -> str (string_of_id (snd n))
  | DTCoq (c, t, s) -> 
      debug_msg 1 (str "Coq:(") ++ pr_term c ++ 
	debug_msg 1 (str ":" ++ print_dtype_loc ctx t ++ str ")")
  | DTSort s -> 
      pr_term (mkSort (snd s))

and print_dtype_loc ctx (_, t) = print_dtype' ctx t

let _ = print_dtype_locref := print_dtype_loc

let rec reduce_term t = 
  match t with
    | DLambda ((n, x), y, dt) -> DLambda ((n, reduce_type_loc x), reduce_term_loc y, reduce_type_loc dt)
    | DApp (dte, dte', dt) -> snd (subst_term dte' dte)
    | DLetIn (nl, dte, dte', dt) -> snd (subst_term dte' dte)
    | DLetTuple (nl, dte, dte', dt) -> t (* TODO *)
    | DIfThenElse (db, de, de', dt) -> t (* TODO *)
    | DSum _ | DRel _ | DCoq _ -> t
	
and reduce_term_loc (loc, t) = (loc, reduce_term t)

and reduce_type = function
  | DTApp (x, y, t, s) -> snd (subst y x)
  | DTPi ((id, x), y, s) -> DTPi ((id, reduce_type_loc x), reduce_type_loc y, s)
  | DTSigma ((id, x), y, s) -> DTSigma ((id, reduce_type_loc x), reduce_type_loc y, s)
  | DTSubset ((id, x), y, s) -> DTSubset ((id, reduce_type_loc x), reduce_type_loc y, s)
  | (DTRel i) as x -> x      
  | DTTerm (t, tt, s) -> DTTerm (reduce_term_loc t, reduce_type_loc tt, s)
  | DTInd (n, t, i, s) as x -> x
  | DTCoq (c, t, s) as x -> x
  | DTSort _ as x -> x

and reduce_type_loc (loc, t) = (loc, reduce_type t)


let rec type_equiv ctx u v =
  trace (str "Check type equivalence: " ++ print_dtype_loc ctx u ++ str " and " ++ print_dtype_loc ctx v);
  match snd u, snd v with
      DTCoq (_, x, _), y -> type_equiv ctx x v
    | x, DTCoq (_, y, _) -> type_equiv ctx u y

    | DTApp (_, _, t, _), _ -> type_equiv ctx t v
    | _, DTApp (_, _, t, _) -> type_equiv ctx u t

    | (DTPi ((_, x), y, _), DTPi ((n', x'), y', _)) ->
	type_equiv ctx x x' && type_equiv ((snd n', x') :: ctx) y y'
    | (DTSigma ((_, x), y, _), DTSigma ((n', x'), y', _)) ->
	type_equiv ctx x x' && type_equiv ((snd n', x') :: ctx) y y'
    | (DTSubset ((_, x), y, _), DTSubset ((_, x'), y', _)) ->
	type_equiv ctx x x'
    | (DTRel x, DTRel y) -> x = y
    | (DTInd (n, _, i, _), DTInd (n', _, i', _)) -> i == i' || i = i'
    | _ -> false

let convertible ctx u v = 
  type_equiv ctx (reduce_type_loc u) (reduce_type_loc v)

let rec check_subtype ctx u v =
  trace (str "Check subtype: " ++ print_dtype_loc ctx u ++ str " and " ++ print_dtype_loc ctx v);  
  match (snd u, snd v) with
      DTCoq (_, t, _), _ -> check_subtype ctx t v
    | _, DTCoq (_, t, _) -> check_subtype ctx u t

    | DTInd (_, t, _, _), _ -> check_subtype ctx t v
    | _, DTInd (_, t, _, _) -> check_subtype ctx u t

    | DTApp (_, _, t, _), _ -> check_subtype ctx t v
    | _, DTApp (_, _, t, _) -> check_subtype ctx u t

    | DTRel i, _ -> 
	let t = 
	  try type_of_rel ctx i
	  with e ->
	    debug 3 (str "Couldn't find type_of_rel in check_subtype");
	    raise e
	in check_subtype ctx (lift (succ i) t) v
    | _, DTRel i -> 
	let t = 
	  try type_of_rel ctx i
	  with e -> debug 3 (str "Couldn't find type_of_rel in check_subtype");
	    raise e
	in
	  check_subtype ctx u (lift (succ i) t)

    | (DTPi ((_, x), y, _), DTPi ((n', x'), y', _)) ->
	check_subtype ctx x' x && check_subtype ((snd n', x') :: ctx) y y'

    | (DTSigma ((_, x), y, _), DTSigma ((n', x'), y', _)) ->
	check_subtype ctx x x' && check_subtype ((snd n', x') :: ctx) y y'

    | (DTSubset ((_, x), y, _), _) -> check_subtype ctx x v
    | (_, DTSubset ((_, x), y, _)) -> check_subtype ctx u x
    | (DTSort s, DTSort s') ->
	(match snd s, snd s' with
	     Prop _, Type _ -> true
	   | x, y -> x = y)
    | _ -> convertible ctx u v

let rec mu ctx = function
  | DTSubset ((_, x), y, _) -> mu ctx (snd x)
  | DTCoq (_, x, _) -> mu ctx (snd x)
  | DTInd (_, t, _, _) -> mu ctx (snd t)
  | DTApp (_, _, t, _) -> mu ctx (snd t)
  | DTRel i -> mu ctx (snd (type_of_rel ctx i))
  | x -> x
    
exception Not_implemented of string

let notimpl s = raise (Not_implemented s)

let type_application ctx ((locx, x) as tx) ((locy, y) as ty) =
  let narg, targ, tres, sres =
    match mu ctx x with
      | DTPi ((n, x), y, z) -> n, x, y, z
      | x -> 
	  typing_error (NonFunctionalApp (locx,
					  (print_dtype_loc ctx tx),
					  (print_dtype' ctx x)))
  in
    try
      if check_subtype ctx ty targ then
	let dtres = subst tres ty in
	  debug 1 (str "Subst of " ++ print_dtype_loc ctx ty ++ str " in " ++
		   print_dtype_loc ((snd narg, targ) :: ctx) tres);
	  debug 1 (str "Subst in result type: " ++ print_dtype_loc ctx dtres);
	  dummy_loc, DTApp (tx, ty, dtres, sort_of_dtype_loc ctx dtres)
      else 
	subtyping_error (UncoercibleInferType 
			   (locy, print_dtype_loc ctx ty, print_dtype_loc ctx targ))
	  
    with e -> raise e (* Todo check exception etc.. *)


let rec dtype_of_types ctx c = 
  let dt = 
    match kind_of_term c with
      | Rel i     -> 
	    DTRel (pred i)
      | Var id    -> 
	  let ref = Nametab.locate (Libnames.make_short_qualid id) in
	  let t = Libnames.constr_of_global ref in
	    snd (dtype_of_types ctx t)
      | Meta mv -> notimpl "Meta"
      | Evar pex -> notimpl "Evar"
      | Sort s -> DTSort (dummy_loc, s)
      | Cast (c, _, t) -> snd (dtype_of_types ctx t)
      | Prod (n, t, t') -> 
	  let dt = dtype_of_types ctx t in
	  let ctx' = (n, dt) :: ctx in
	  let dt' = dtype_of_types ctx' t' in
	    DTPi (((dummy_loc, n), dt), dt', sort_of_dtype_loc ctx' dt')
      | Lambda (n, t, e) -> notimpl "Lambda"
      | LetIn (n, e, t, e') -> notimpl "LetIn"
      | App (f, el) -> 
	  snd (List.fold_left 
		 (fun acc el -> 
		    let tel = dtype_of_types ctx el in
		      type_application ctx acc tel)
		 (dtype_of_types ctx f) (Array.to_list el))
      | Const cst -> 
	  let t = Global.lookup_constant cst in
	  let dt = dtype_of_types ctx t.Declarations.const_type in
	    DTCoq (c, dt, sort_of_dtype_loc ctx dt)
      | Ind i ->
	  let (_, ind) = Inductive.lookup_mind_specif (Global.env ()) i in
	    DTInd ((dummy_loc, ind.Declarations.mind_typename), 
		   dtype_of_types ctx ind.Declarations.mind_nf_arity,
		   i, (dummy_loc, ind.Declarations.mind_sort))
	      (* 	  let t = Inductiveops.type_of_inductive (Global.env ()) i in *)
(* 	    debug "Lookup inductive"; *)
	      (* 	  let dt = dtype_of_types ctx t in  *)
(* 	    DTCoq (t, dt, sort_of_dtype_loc ctx dt) *)

      | Construct con -> 
	  let t = Inductiveops.type_of_constructor (Global.env ()) con in
	  let dt = dtype_of_types ctx t in
	    DTCoq (c, dt, sort_of_dtype_loc ctx dt)
      | Case _ -> notimpl "Case"
      | Fix fixpt -> notimpl "Fixpoint"
      | CoFix cofixpt -> notimpl "CoFixpoint"
  in dummy_loc, dt

let rec dtype_of_constr ctx c = 
  let dt = 
    match kind_of_term c with
      | Rel i     -> DTRel (pred i)
      | Var id    -> 
	  let ref = Nametab.locate (Libnames.make_short_qualid id) in
	  let t = Libnames.constr_of_global ref in
	    snd (dtype_of_constr ctx t)
      | Meta mv -> notimpl "Meta"
      | Evar pex -> notimpl "Evar"
      | Sort s -> DTSort (dummy_loc, s)
      | Cast (_,_,t) -> snd (dtype_of_constr ctx t)
      | Prod (n, t, t') -> 
	  let dt = dtype_of_constr ctx t in
	  let ctx' = (n, dt) :: ctx in
	  let dt' = dtype_of_constr ctx' t' in
	    DTPi (((dummy_loc, n), dt), dt', sort_of_dtype_loc ctx' dt')
      | Lambda (n, t, e) -> notimpl "Lambda"
      | LetIn (n, e, t, e') -> notimpl "LetIn"
      | App (f, el) -> 
	  snd (List.fold_left 
		 (fun acc el -> 
		    type_application ctx acc (dtype_of_constr ctx el))
		 (dtype_of_constr ctx f) (Array.to_list el))
      | Const cst -> 
	  let t = Global.lookup_constant cst in
	  let dt = dtype_of_constr ctx t.Declarations.const_type in
	    snd dt
		  
      | Ind i ->
	  let (_, ind) = Inductive.lookup_mind_specif (Global.env ()) i in
	    DTInd ((dummy_loc, ind.Declarations.mind_typename), 
		   dtype_of_types ctx ind.Declarations.mind_nf_arity,
		   i, (dummy_loc, ind.Declarations.mind_sort))

      | Construct con -> 
	  let t = Inductiveops.type_of_constructor (Global.env ()) con in
	  let dt = dtype_of_constr ctx t in
	    snd dt
      | Case _ -> notimpl "Case"
      | Fix fixpt -> notimpl "Fixpoint"
      | CoFix cofixpt -> notimpl "CoFixpoint"
  in dummy_loc, dt
      
let list_assoc_index x l =
  let rec aux i = function
      (y, _) :: tl -> if x = y then i else aux (succ i) tl
    | [] -> debug 2 (str "raising not_found in list_assoc_index");
	raise Not_found
  in aux 0 l
  
let coqref ctx (loc, r) = 
  let qualid = Libnames.make_short_qualid r in
    try 
      let gr = Nametab.locate qualid in
	debug 3 (str "Resolved " ++ str (string_of_id r) ++ str " globally");
	Libnames.constr_of_global gr
    with Not_found ->
      debug 3 (str "Error in coqref");
      Nametab.error_global_not_found_loc loc qualid

let coqtermref ctx r =
  let constr = coqref ctx r in
  let dtype = dtype_of_constr ctx constr in
    DCoq (constr, dtype), dtype
      
let coqtyperef ctx r =
  let constr = coqref ctx r in
  let dtype = dtype_of_types ctx constr in
    snd dtype, dtype
	
let debug_loc n (loc, e) = 
  debug n (Toplevel.print_toplevel_error (Stdpp.Exc_located (loc, Debug_msg e)))
  
let rec dtype n ctx (loc, t) =
  let t' = 
    match t with
	TApp (x, y) -> 
	  let tx, ty = dtype n ctx x, dtype n ctx y in
	    snd (type_application ctx tx ty)
      | TPi ((name, t), t') -> 
	  let dt = dtype n ctx t in
	  let dt' = dtype (succ n) ((snd name, dt) :: ctx) t' in
	    DTPi ((name, dt), dt', (dummy_loc, type_0))
      | TSigma ((name, t), t') -> 
	  let dt = dtype n ctx t in
	  let dt' = dtype (succ n) ((snd name, dt) :: ctx) t' in
	    DTSigma ((name, dt), dt', (dummy_loc, type_0))
      | TSubset ((i, t), t') -> 
	  let dt = dtype n ctx t in
	  let ctx' = (Name (snd i), dt) :: ctx in
	  let dt' = dtype (succ n) ctx' t' in
	    DTSubset ((i, dt), dt', sort_of_dtype_loc ctx dt)
      | TIdent (loc, i) ->
	  let name = Name i in
	    if List.mem_assoc name ctx then
	      let typ = List.assoc name ctx in
	      let index = list_assoc_index name ctx in
		debug 3 (str "Resolved " ++ str (string_of_id i) ++ str " locally");
		DTRel index
	    else fst (coqtyperef ctx (loc, i))
      | TTerm t -> let t, tt = dterm n ctx t in DTTerm (t, tt, sort_of_dtype_loc ctx tt)
  in (loc, t')

and dterm n ctx (loc, t) =
  let t', tt' =
    match t with
      | SIdent li -> 
	  begin
	    let name = Name (snd li) in
	      if List.mem_assoc name ctx then		
		let typ = List.assoc name ctx in
		let index = list_assoc_index name ctx in
		let typ' = lift (succ index) typ in
		  debug 3 (str "Resolved " ++ str (string_of_id (snd li)) ++ str " locally");
		  DRel index, typ'
	      else coqtermref ctx li
	  end
	    
      | SLambda (((loc, name) as ln, t), e) -> 
	  let dt = dtype n ctx t in
	  let name = Name name in
	  let ln = loc, name in
	  let ctx' = (name, dt) :: ctx in
	  let de, te = dterm (succ n) ctx' e in
	  let dpi = dummy_loc, DTPi ((ln, dt), te, sort_of_dtype_loc ctx' te) in
	    DLambda ((ln, dt), de, dpi), dpi
	      
      | SLetIn ((loc, name) as ln, e, e') -> 
	  let de, te = dterm n ctx e in
	  let de', te' = dterm (succ n) ((name, te) :: ctx) e' in
	    DLetIn (ln, de, de', te'), te'
	      
      | SApp (f, e) ->
	  let dt, tf = dterm n ctx f in
	  let narg, targ, tres, sres =
	    match mu ctx (snd tf) with
	      | DTPi ((n, x), y, z) -> n, x, y, z
	      | x -> typing_error (NonFunctionalApp
				     (fst f, print_dterm_loc ctx dt,
				      print_dtype' ctx x))
	  in
	  let de, te = dterm n ctx e in
	    (try
	       if check_subtype ctx te targ then
		 let term = (dummy_loc, DTTerm (de, te, sort_of_dtype_loc ctx te)) in
		 let dtres = subst tres term in
		   debug 1 (str "Subst of " ++ print_dtype_loc ctx term ++ str " in " ++
			      print_dtype_loc ((snd narg, targ) :: ctx) tres);
		   debug 1 (str "Subst in result type: " ++ print_dtype_loc ctx dtres);
		   DApp (dt, de, dtres), dtres
	       else 
		 subtyping_error 
		   (UncoercibleInferTerm (fst e, 
					  print_dtype_loc ctx te,
					  print_dtype_loc ctx targ,
					  print_dterm_loc ctx de,
					  print_dterm_loc ctx dt))

		 
	     with e -> raise e (* Todo check exception etc.. *))

      | SSumDep (((loc, id), t), (t', tt')) -> 
	  let dt, tt = dterm n ctx t in
	  let ctx' = (Name id, tt) :: ctx in
	  let tt' = dtype (succ n) ctx' tt' in
	  let dt', _ = dterm (succ n) ctx' t' in
	  let rest = dummy_loc, 
	    DTSigma (((loc, Name id), tt), tt', sort_of_dtype_loc ctx' tt') 
	  in
	    DSum (((loc, Name id), dt), (dt', tt'), rest), rest
	      
      | SSumInf (t, t') ->
	  let dt, tt = dterm n ctx t in
	  let ctx' = (Anonymous, tt) :: ctx in
	  let dt', tt' = dterm (succ n) ctx' t' in
	  let rest = dummy_loc,
	    DTSigma (((dummy_loc, Anonymous), tt), tt', sort_of_dtype_loc ctx' tt')
	  in
	    DSum (((dummy_loc, Anonymous), dt), (dt', tt'), rest), rest

      | SIfThenElse (b, t, t') ->
	  let dn, tn = dterm n ctx b in
	  let ctx' = (Name (id_of_string "H"), 
		      (dummy_loc, 
		       DTCoq (Term.mkVar (id_of_string "H"),
			      (dummy_loc, DTSort (dummy_loc, mk_Set)),
			      (dummy_loc, type_0)))) :: ctx
	  in
	  let dt, tt = dterm (succ n) ctx' t
	  and dt', tt' = dterm (succ n) ctx' t' in	    
	    if convertible ctx' tt tt' then
	      DIfThenElse (dn, dt, dt', tt), (unlift 1 tt)
	    else typing_error (NonConvertible (loc, print_dtype_loc ctx' tt,
					       print_dtype_loc ctx' tt'))
	      
      | SLetTuple (nl, t, t') ->
	  let dt, tt = dterm n ctx t in
	    debug 2 (str "Let tuple e type: " ++ print_dtype_loc ctx tt);
	  let rec aux n lctx tt l = 
	    match snd tt, l with
		DTSigma ((nl, t), t', s), nl' :: ((_ :: _) as tl) ->
		  aux (succ n) ((nl', t, tt) :: lctx) t' tl
	      | _, [nl] -> 
		  (nl, tt, tt) :: lctx
	      | _, _ -> typing_error (NonSigma (fst tt, print_dtype_loc ctx tt))
	  in
	  let ctx' = aux 0 [] tt nl in
	  let ctx'' = (List.map (fun (nl, t, t') -> (snd nl, t)) ctx') @ ctx in
	  let dt', tt' = dterm ((List.length nl) + n) ctx'' t' in
	  let t = DLetTuple (ctx', dt, dt', unlift (List.length nl) tt') in
	    debug 2 (str "Parsed let-tuple: " ++ print_dterm' ctx t);
	    debug 2 (str "ctx' = ");
	    debug 2 (str "ctx' = " ++
		       let cmds, _ = 
			 (List.fold_right
			    (fun (x, t, t') (acc, ctx)  ->
			       let acc' = print_name_loc x ++ str ":" ++
				 print_dtype_loc ctx t
			       in
			       let ctx' = (snd x, t) :: ctx in
				 (acc ++ spc () ++ acc', ctx'))
			    ctx' (mt (), ctx))
		       in cmds);
	    
	    debug 2 (str "Parsed let-tuple in-term: " ++ print_dterm_loc ctx'' dt');
	    debug 2 (str "Parsed let-tuple type: " ++ 
		       print_dtype_loc ((List.map (fun (x, t, _) -> snd x, t) ctx') @ ctx) tt');
	    t, tt'
		     
	  
  in (loc, t'), tt'

let infer ctx t = dterm 0 ctx t
let infer_type ctx t = dtype 0 ctx t

