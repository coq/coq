(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Options
open Names
open Term
open Declarations
open Libobject
open Lib
open Util
open Miniml

(*s Dummy names. *)

let anonymous = id_of_string "x"
let prop_name = id_of_string "_"

(*s In an ML type, update the arguments to all inductive types [(sp,_)] *)		  

let rec update_args sp vl = function  
  | Tapp ( Tglob r :: l ) -> 
      (match r with 
	| IndRef (s,_) when s = sp -> Tapp ( Tglob r :: vl)
	| _ -> Tapp (Tglob r :: (List.map (update_args sp vl) l)))
  | Tapp l -> Tapp (List.map (update_args sp vl) l) 
  | Tarr (a,b)-> 
      Tarr (update_args sp vl a, update_args sp vl b)
  | a -> a

(*s [occurs k t] returns true if [(Rel k)] occurs in [t]. *)

let rec occurs k = function
  | MLrel i -> i = k
  | MLapp(t,argl) -> (occurs k t) || (occurs_list k argl)
  | MLlam(_,t) -> occurs (k + 1) t
  | MLcons(_,argl) -> occurs_list k argl
  | MLcase(t,pv) -> 
      (occurs k t) ||
      (array_exists
	 (fun (_,l,t') -> let k' = List.length l in occurs (k + k') t') pv)
  | MLfix(_,l,cl) -> let k' = Array.length l in occurs_vect (k + k') cl
  | _ -> false

and occurs_list k l = List.exists (occurs k) l

and occurs_vect k v = array_exists (occurs k) v

(*s map over ML asts *)

let rec ast_map f = function
  | MLapp (a,al) -> MLapp (f a, List.map f al)
  | MLlam (id,a) -> MLlam (id, f a)
  | MLletin (id,a,b) -> MLletin (id, f a, f b)
  | MLcons (c,al) -> MLcons (c, List.map f al)
  | MLcase (a,eqv) -> MLcase (f a, Array.map (ast_map_eqn f) eqv)
  | MLfix (fi,ids,al) -> MLfix (fi, ids, Array.map f al)
  | MLcast (a,t) -> MLcast (f a, t)
  | MLmagic a -> MLmagic (f a)
  | MLrel _ | MLglob _ | MLexn _ | MLprop | MLarity as a -> a

and ast_map_eqn f (c,ids,a) = (c,ids,f a)


(*s Lifting on terms.
    [ml_lift k t] lifts the binding depth of [t] across [k] bindings. 
    We use a generalization [ml_lift k n t] lifting the vars
    of [t] under [n] bindings. *)

let ml_liftn k n c = 
  let rec liftrec n = function
    | MLrel i as c -> if i < n then c else MLrel (i+k)
    | MLlam (id,t) -> MLlam (id, liftrec (n+1) t)
    | MLletin (id,a,b) -> MLletin (id, liftrec n a, liftrec (n+1) b)
    | MLcase (t,pl) -> 
	MLcase (liftrec n t,
      	       	Array.map (fun (id,idl,p) -> 
			     let k = List.length idl in
			     (id, idl, liftrec (n+k) p)) pl)
    | MLfix (n0,idl,pl) -> 
	MLfix (n0,idl,
	       let k = Array.length idl in Array.map (liftrec (n+k)) pl)
    | a -> ast_map (liftrec n) a
  in 
  if k = 0 then c else liftrec n c

let ml_lift k c = ml_liftn k 1 c

let ml_pop c = ml_lift (-1) c

(*s Substitution. [ml_subst e t] substitutes [e] for [Rel 1] in [t]. 
    It uses a generalization [subst] substituting [m] for [Rel n]. 
    Lifting (of one binder) is done at the same time. *)

let rec ml_subst v =
  let rec subst n m = function
    | MLrel i as a ->
	if i = n then
	  m
	else 
	  if i < n then a else MLrel (i-1)
    | MLlam (id,t) ->
	MLlam (id, subst (n+1) (ml_lift 1 m) t)
    | MLletin (id,a,b) ->
	MLletin (id, subst n m a, subst (n+1) (ml_lift 1 m) b)
    | MLcase (t,pv) ->
	MLcase (subst n m t,
		Array.map (fun (id,ids,t) ->
			     let k = List.length ids in
      	       		     (id,ids,subst (n+k) (ml_lift k m) t)) pv)
    | MLfix (i,ids,cl) -> 
	MLfix (i,ids, 
	       let k = Array.length ids in
	       Array.map (subst (n+k) (ml_lift k m)) cl)
    | a ->
        ast_map (subst n m) a
  in 
  subst 1 v

(*s Simplification of any [MLapp (MLapp (_,_),_)] *)

let rec merge_app a = match a with 
  | MLapp (f,l) -> 
      let f' = merge_app f in 
      let l' = List.map merge_app l in 
      (match f' with 
	 | MLapp (f'',l'') -> MLapp (f'',l'' @ l')
	 | _ -> MLapp (f', l'))
  | _ -> ast_map merge_app a

(*s Number of occurences of [Rel 1] in [a]. *)

let nb_occur a =
  let cpt = ref 0 in
  let rec count n = function
    | MLrel i -> if i = n then incr cpt
    | MLlam (id,t) -> count (n + 1) t
    | MLletin (id,a,b) -> count n a; count (n + 1) b
    | MLcase (t,pv) ->
	count n t;
	Array.iter (fun (_,l,t) -> let k = List.length l in count (n + k) t) pv
    | MLfix (_,ids,cl) -> 
	let k = Array.length ids in Array.iter (count (n + k)) cl
    | MLapp (a,l) -> count n a; List.iter (count n) l
    | MLcons (_,l) ->  List.iter (count n) l
    | MLmagic a -> count n a
    | MLcast (a,_) -> count n a
    | MLprop | MLexn _ | MLglob _ | MLarity -> ()
  in 
  count 1 a; !cpt


(*s Beta-iota reductions + simplifications*)

let constructor_index = function
  | ConstructRef (_,j) -> pred j
  | _ -> assert false

let is_atomic = function 
  | MLrel _ | MLglob _ | MLexn _ | MLprop | MLarity -> true
  | _ -> false

let rec betaiota = function
  | MLapp (f, []) ->
      betaiota f
  | MLapp (f, a) ->
      let f' = betaiota f 
      and a' = List.map betaiota a in
      (match f' with
	 (* beta redex *)
	 | MLlam (id,t) -> 
	     (match nb_occur t with
		| 0 -> betaiota (MLapp (ml_pop t, List.tl a'))
		| 1 -> betaiota (MLapp (ml_subst (List.hd a') t, List.tl a'))
		| _ -> 
		    let a'' = List.map (ml_lift 1) (List.tl a') in
		    betaiota (MLletin (id, List.hd a', MLapp (t, a''))))
	 (* application of a let in: we push arguments inside *)
	 | MLletin (id,e1,e2) ->
	     MLletin (id, e1, betaiota (MLapp (e2, List.map (ml_lift 1) a')))
	 (* application of a case: we push arguments inside *)
	 | MLcase (e,br) ->
	     let br' = 
	       Array.map 
      	       	 (fun (n,l,t) -> 
		    let k = List.length l in
		    let a'' = List.map (ml_lift k) a' in
      	       	    (n, l, betaiota (MLapp (t,a'')))) 
		 br 
	     in
      	     betaiota (MLcase (e,br'))
	 | _ ->
	     MLapp (f',a'))
  | MLcase (e,br) ->
      (match betaiota e with
	 (* iota redex *)
	 | MLcons (r,a) ->
	     let j = constructor_index r in
	     let (_,ids,c) = br.(j) in
	     let c' = List.fold_right (fun id t -> MLlam (id,t)) ids c in
	     betaiota (MLapp (c',a))
	 | e' -> 
	     MLcase (e', Array.map (fun (n,l,t) -> (n,l,betaiota t)) br))
  | MLletin(_,c,e) when (is_atomic c) || (nb_occur e <= 1) -> 
      (* expansion of a letin in special cases *)
      betaiota (ml_subst c e)
  | a -> 
      ast_map betaiota a
    
let normalize a = betaiota (merge_app a)

let normalize_decl = function
 | Dglob (id, a) -> Dglob (id, normalize a)
 | d -> d

(*s Extraction parameters *)

module Refset = 
  Set.Make(struct type t = global_reference let compare = compare end)

type extraction_params = {
  modular : bool;       (* modular extraction *)
  module_name : string; (* module name if [modular] *)
  optimization : bool;  (* we need optimization *)
  to_keep : Refset.t;   (* globals to keep *)
  to_expand : Refset.t; (* globals to expand *)
}

(*s Utility functions used for the decision of expansion *)

let rec ml_size = function
  | MLapp(t,l) -> List.length l + ml_size t + ml_size_list l
  | MLlam(_,t) -> 1 + ml_size t
  | MLcons(_,l) -> ml_size_list l
  | MLcase(t,pv) -> 
      1 + ml_size t + (Array.fold_right (fun (_,_,t) a -> a + ml_size t) pv 0)
  | MLfix(_,_,f) -> ml_size_array f
  | MLletin (_,_,t) -> ml_size t
  | MLcast (t,_) -> ml_size t
  | MLmagic t -> ml_size t
  | _ -> 0

and ml_size_list l = List.fold_left (fun a t -> a + ml_size t) 0 l

and ml_size_array l = Array.fold_left (fun a t -> a + ml_size t) 0 l

let is_fix = function MLfix _ -> true | _ -> false

let rec is_constr = function
  | MLcons _   -> true
  | MLlam(_,t) -> is_constr t
  | _          -> false


(*s Strictness *)

(* A variable is strict if the evaluation of the whole term implies
   the evaluation of this variable. Non-strict variables can be found 
   behind Match, for example. Expanding a term [t] is a good idea when 
   it begins by at least one non-strict lambda, since the corresponding 
   argument to [t] might be unevaluated in the expanded code. *)

exception Toplevel

let lift n l = List.map ((+) n) l

let pop n l = List.map (fun x -> if x-n<0 then raise Toplevel else x-n) l 

(* This function returns a list of de Bruijn indices of non-strict variables,
   or raises [Toplevel] if it has an internal non-strict variable. 
   In fact, not all variables are checked for strictness, only the ones which 
   de Bruijn index is in the candidates list [cand]. The flag [add] controls 
   the behaviour when going through a lambda: should we add the corresponding 
   variable to the candidates?  We use this flag to check only the external 
   lambdas, those that will correspond to arguments. *)

let rec non_stricts add cand = function 
  | MLlam (id,t) -> 
      let cand = lift 1 cand in
      let cand = if add then 1::cand else cand in
      pop 1 (non_stricts add cand t)
  | MLrel n -> 
      List.filter ((<>) n) cand  
(*i old particular case 
  | MLapp (MLrel n, _) -> 
      List.filter ((<>) n) cand  
	(* In [(x y)] we say that only x is strict. (WHY?) *) i*)
  | MLapp (t,l)-> 
      let cand = non_stricts false cand t in 
      List.fold_left (non_stricts false) cand l 
  | MLcons (_,l) -> 
      List.fold_left (non_stricts false) cand l
  | MLletin (_,t1,t2) -> 
      let cand = non_stricts false cand t1 in 
      pop 1 (non_stricts add (lift 1 cand) t2)
  | MLfix (_,i,f)-> 
      let n = Array.length i in
      let cand = lift n cand in 
      let cand = Array.fold_left (non_stricts false) cand f in 
      pop n cand
  | MLcase (t,v) -> 
      (* The only interesting case: for a variable to be non-strict, 
	 it is sufficient that it appears non-strict in at least one branch,
	 so he make an union (in fact a merge). *)
      let cand = non_stricts false cand t in 
      Array.fold_left 
	(fun c (_,i,t)-> 
	   let n = List.length i in 
	   let cand = lift n cand in 
	   let cand = pop n (non_stricts add cand t) in
	   Sort.merge (<=) cand c) [] v
	(* [merge] may duplicates some indices, but I don't mind. *)
  | MLcast (t,_) -> 
      non_stricts add cand t
  | MLmagic t -> 
      non_stricts add cand t
  | _ -> 
      cand

(* The real test: we are looking for internal non-strict variables, so we start with 
   no candidates, and the only positive answer is via the [Toplevel] exception. *)

let is_not_strict t = 
  try 
    let _ = non_stricts true [] t in false
  with 
    | Toplevel -> true

(*s Expansion decision *)

(* [expansion_test] answers the following question: 
   If we could expand [t] (the user said nothing special), 
   should we expand ? 
   
   We don't expand fixpoints, but always inductive constructors.
   Last case of expansion is a term not to big with at least one 
   non-strict variable (i.e. a variable that may not be evaluated). *)

let expansion_test t = 
  (not (is_fix t))
  &&
  ((is_constr t) 
   ||
   (ml_size t < 10 && is_not_strict t))

(* If the user doesn't say he wants to keep [t], we expand in two cases:
   \begin{itemize}
   \item the user explicitly requests it 
   \item [expansion_test] answers that the expansion is a good idea, and 
   we are free to act (no [noopt] given as argument)
   \end{itemize} *)

let expand prm r t = 
  (not (Refset.mem r prm.to_keep)) (* the user DOES want to keep it *)
  &&
  (Refset.mem r prm.to_expand (* the user DOES want to expand it *) 
   || 
   (prm.optimization && expansion_test t)) 

(*s Optimization *)

let subst_glob_ast r m = 
  let rec substrec = function
    | MLglob r' as t -> if r = r' then m else t
    | t -> ast_map substrec t
  in
  substrec

let subst_glob_decl r m = function
  | Dglob(r',t') -> Dglob(r', subst_glob_ast r m t')
  | d -> d

let warning_expansion r = 
  wARN (hOV 0 [< 'sTR "The constant"; 'sPC;
		 Printer.pr_global r; 'sPC; 'sTR "is expanded." >])

let rec optimize prm = function
  | [] -> 
      []
  | (Dtype _ | Dabbrev _) as d :: l -> 
      d :: (optimize prm l)
  | Dglob (_, MLprop) :: l ->
      optimize prm l
  (*i
  | Dglob(id,(MLexn _ as t)) as d :: l ->
      let l' = List.map (expand (id,t)) l in optimize prm l'
  i*)	    
  | Dglob (r,t) :: l ->
      let t = normalize t in
      let b = expand prm r t in
      let l = if b then 
	begin
	  if_verbose warning_expansion r;
	  List.map (subst_glob_decl r t) l
	end
      else l in 
      if prm.modular || l = [] || not b then 
	Dglob (r,t) :: (optimize prm l)
      else
	optimize prm l


(*s Table for direct ML extractions. *)

module Refmap = 
  Map.Make(struct type t = global_reference let compare = compare end)

let empty_extractions = (Refmap.empty, Refset.empty)

let extractions = ref empty_extractions

let ml_extractions () = snd !extractions

let add_ml_extraction r s = 
  let (map,set) = !extractions in
  extractions := (Refmap.add r s map, Refset.add r set)

let is_ml_extraction r = Refset.mem r (snd !extractions)

let find_ml_extraction r = Refmap.find r (fst !extractions)

(*s Registration of operations for rollback. *)

let (in_ml_extraction,_) = 
  declare_object ("ML extractions",
		  { cache_function = (fun (_,(r,s)) -> add_ml_extraction r s);
		    load_function = (fun (_,(r,s)) -> add_ml_extraction r s);
		    open_function = (fun _ -> ());
		    export_function = (fun x -> Some x) })

(*s Registration of the table for rollback. *)

open Summary

let _ = declare_summary "ML extractions"
	  { freeze_function = (fun () -> !extractions);
	    unfreeze_function = ((:=) extractions);
	    init_function = (fun () -> extractions := empty_extractions);
	    survive_section = true }

(*s Grammar entries. *)

open Vernacinterp

let string_of_varg = function
  | VARG_IDENTIFIER id -> string_of_id id
  | VARG_STRING s -> s
  | _ -> assert false

let no_such_reference q =
  errorlabstrm "reference_of_varg" 
    [< Nametab.pr_qualid q; 'sTR ": no such reference" >]

let reference_of_varg = function
  | VARG_QUALID q -> 
      (try Nametab.locate q with Not_found -> no_such_reference q)
  | _ -> assert false

(*s \verb!Extract Constant qualid => string! *)

let extract_constant r s = match r with
  | ConstRef _ -> 
      add_anonymous_leaf (in_ml_extraction (r,s))
  | _ -> 
      errorlabstrm "extract_constant"
	[< Printer.pr_global r; 'sPC; 'sTR "is not a constant" >]

let _ = 
  vinterp_add "EXTRACT_CONSTANT"
    (function 
       | [id; s] -> 
	   (fun () -> 
	      extract_constant (reference_of_varg id) (string_of_varg s))
       | _ -> assert false)

(*s \verb!Extract Inductive qualid => string [ string ... string ]! *)

let extract_inductive r (id2,l2) = match r with
  | IndRef ((sp,i) as ip) ->
      let mib = Global.lookup_mind sp in
      let n = Array.length mib.mind_packets.(i).mind_consnames in
      if n <> List.length l2 then
	error "not the right number of constructors";
      add_anonymous_leaf (in_ml_extraction (r,id2));
      list_iter_i
	(fun j s -> 
	   add_anonymous_leaf 
	     (in_ml_extraction (ConstructRef (ip,succ j),s))) l2
  | _ -> 
      errorlabstrm "extract_inductive"
	[< Printer.pr_global r; 'sPC; 'sTR "is not an inductive type" >]

let _ = 
  vinterp_add "EXTRACT_INDUCTIVE"
    (function 
       | [q1; VARG_VARGLIST (id2 :: l2)] ->
	   (fun () -> 
	      extract_inductive (reference_of_varg q1) 
		(string_of_varg id2, List.map string_of_varg l2))
       | _ -> assert false)
