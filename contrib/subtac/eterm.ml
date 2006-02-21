(**
   - Get types of existentials ;
   - Flatten dependency tree (prefix order) ;
   - Replace existentials by De Bruijn indices in term, applied to the right arguments ;
   - Apply term prefixed by quantification on "existentials".
*)

open Term
open Names
open Evd
open List
open Pp

let reverse_array arr = 
  Array.of_list (List.rev (Array.to_list arr))
    

(** Utilities to find indices in lists *)
let list_index x l =
  let rec aux i = function
      k :: tl -> if k = x then i else aux (succ i) tl
    | [] -> raise Not_found
  in aux 0 l

let list_assoc_index x l =
  let rec aux i = function
      (k, v) :: tl -> if k = x then i else aux (succ i) tl
    | [] -> raise Not_found
  in aux 0 l

(** Substitute evar references in t using De Bruijn indices, 
  where n binders were passed through. *)
let subst_evars evs n t = 
  let evar_index id = 
    let idx = list_assoc_index id evs in
      idx + 1
  in
  let rec substrec depth c = match kind_of_term c with
    | Evar (k, args) ->
	(try 
	   msgnl (str "Evar " ++ int k ++ str " found");
	   let ex = 
(* 	     mkVar (id_of_string ("Evar" ^ string_of_int k));*)
  	     mkRel (evar_index k + depth)  
	   in
	   let args = List.rev_map (map_constr_with_binders succ substrec depth) (Array.to_list args) in
	     mkApp (ex, Array.of_list args)
	 with Not_found -> 
	   msgnl (str "Evar " ++ int k ++ str " not found!!!");
	   c)
    | _ -> map_constr_with_binders succ substrec depth c
  in 
    substrec 0 t
      
(** Substitute variable references in t using De Bruijn indices, 
  where n binders were passed through. *)
let subst_vars acc n t = 
  let var_index id = 
    let idx = list_index id acc in
      idx + 1
  in
  let rec substrec depth c = match kind_of_term c with
    | Var v -> (try mkRel (depth + (var_index v)) with Not_found -> c)
    | _ -> map_constr_with_binders succ substrec depth c
  in 
    substrec 0 t

(** Rewrite type of an evar ([ H1 : t1, ... Hn : tn |- concl ])
  to a product : forall H1 : t1, ..., forall Hn : tn, concl.
  Changes evars and hypothesis references to De Bruijn indices.
*)
let etype_of_evar evs ev =
  let rec aux acc n = function
      (id, copt, t) :: tl ->
	let t' = subst_evars evs n t in
	let t'' = subst_vars acc 0 t' in
 	  mkNamedProd_or_LetIn (id, copt, t'') (aux (id :: acc) (succ n) tl)
    | [] ->
	let t' = subst_evars evs n ev.evar_concl in
	  subst_vars acc 0 t'	
  in aux [] 0 (rev (Environ.named_context_of_val ev.evar_hyps))


open Tacticals
    
let eterm evm t = 
  (* 'Serialize' the evars, we assume that the types of the existentials
     refer to previous existentials in the list only *)
  let evl = to_list evm in
  let evts = 
    (* Remove existential variables in types and build the corresponding products *)
    fold_left 
      (fun l (id, y) -> 
	 let y' = (id, etype_of_evar l y) in
	   y' :: l) 
      [] evl 
  in 
  let t' = (* Substitute evar refs in the term to De Bruijn indices *)
    subst_evars evts 0 t 
  in
  let t'' = 
    (* Make the lambdas 'generalizing' the existential variables *)
    fold_left
      (fun acc (id, c) ->
	 mkLambda (Name (id_of_string ("Evar" ^ string_of_int id)),
		   c, acc))
      t' evts
      

  in
  let _declare_evar (id, c) =
    let id = id_of_string ("Evar" ^ string_of_int id) in
      ignore(Declare.declare_variable id (Names.empty_dirpath, Declare.SectionLocalAssum c,
					  Decl_kinds.IsAssumption Decl_kinds.Definitional))
  in
  let _declare_assert acc (id, c) =
    let id = id_of_string ("Evar" ^ string_of_int id) in
      tclTHEN acc (Tactics.assert_tac false (Name id) c)
  in
    msgnl (str "Term constructed in Eterm" ++
	   Termops.print_constr_env (Global.env ()) t'');
   Tactics.apply_term (Reduction.nf_betaiota t'') (map (fun _ -> Evarutil.mk_new_meta ()) evts)
       
open Tacmach

let etermtac (evm, t) = eterm evm t
