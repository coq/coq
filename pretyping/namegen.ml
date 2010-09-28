(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created from contents that was formerly in termops.ml and
   nameops.ml, Nov 2009 *)

(* This file is about generating new or fresh names and dealing with
   alpha-renaming *)

open Util
open Names
open Term
open Nametab
open Nameops
open Libnames
open Environ
open Termops

(**********************************************************************)
(* Globality of identifiers *)

let rec is_imported_modpath mp =
  let current_mp,_ = Lib.current_prefix() in
    match mp with
      | MPfile dp ->
	  let rec find_prefix = function
	    |MPfile dp1 -> not (dp1=dp)
	    |MPdot(mp,_) -> find_prefix mp
	    |MPbound(_) -> false
	  in find_prefix current_mp
      | p -> false

let is_imported_ref = function
  | VarRef _ -> false
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) ->
      let (mp,_,_) = repr_mind kn in is_imported_modpath mp
  | ConstRef kn ->
      let (mp,_,_) = repr_con kn in is_imported_modpath mp

let is_global id =
  try
    let ref = locate (qualid_of_ident id) in
    not (is_imported_ref ref)
  with Not_found ->
    false

let is_constructor id =
  try
    match locate (qualid_of_ident id) with
      | ConstructRef _ as ref -> not (is_imported_ref ref)
      | _ -> false
  with Not_found ->
    false

(**********************************************************************)
(* Generating "intuitive" names from its type *)

let lowercase_first_char id = (* First character of a constr *)
  lowercase_first_char_utf8 (string_of_id id)

let sort_hdchar = function
  | Prop(_) -> "P"
  | Type(_) -> "T"

let hdchar env c =
  let rec hdrec k c =
    match kind_of_term c with
    | Prod (_,_,c)    -> hdrec (k+1) c
    | Lambda (_,_,c)  -> hdrec (k+1) c
    | LetIn (_,_,_,c) -> hdrec (k+1) c
    | Cast (c,_,_)    -> hdrec k c
    | App (f,l)       -> hdrec k f
    | Const kn -> lowercase_first_char (id_of_label (con_label kn))
    | Ind x -> lowercase_first_char (basename_of_global (IndRef x))
    | Construct x -> lowercase_first_char (basename_of_global (ConstructRef x))
    | Var id  -> lowercase_first_char id
    | Sort s -> sort_hdchar s
    | Rel n ->
	(if n<=k then "p" (* the initial term is flexible product/function *)
	 else
	   try match Environ.lookup_rel (n-k) env with
	     | (Name id,_,_)   -> lowercase_first_char id
	     | (Anonymous,_,t) -> hdrec 0 (lift (n-k) t)
	   with Not_found -> "y")
    | Fix ((_,i),(lna,_,_)) ->
	let id = match lna.(i) with Name id -> id | _ -> assert false in
	lowercase_first_char id
    | CoFix (i,(lna,_,_)) ->
	let id = match lna.(i) with Name id -> id | _ -> assert false in
	lowercase_first_char id
    | Meta _|Evar _|Case (_, _, _, _) -> "y"
  in
  hdrec 0 c

let id_of_name_using_hdchar env a = function
  | Anonymous -> id_of_string (hdchar env a)
  | Name id   -> id

let named_hd env a = function
  | Anonymous -> Name (id_of_string (hdchar env a))
  | x         -> x

let mkProd_name   env (n,a,b) = mkProd (named_hd env a n, a, b)
let mkLambda_name env (n,a,b) = mkLambda (named_hd env a n, a, b)

let lambda_name = mkLambda_name
let prod_name = mkProd_name

let prod_create   env (a,b) = mkProd (named_hd env a Anonymous, a, b)
let lambda_create env (a,b) =  mkLambda (named_hd env a Anonymous, a, b)

let name_assumption env (na,c,t) =
  match c with
    | None      -> (named_hd env t na, None, t)
    | Some body -> (named_hd env body na, c, t)

let name_context env hyps =
  snd
    (List.fold_left
       (fun (env,hyps) d ->
	  let d' = name_assumption env d in (push_rel d' env, d' :: hyps))
       (env,[]) (List.rev hyps))

let mkProd_or_LetIn_name env b d = mkProd_or_LetIn (name_assumption env d) b
let mkLambda_or_LetIn_name env b d = mkLambda_or_LetIn (name_assumption env d)b

let it_mkProd_or_LetIn_name env b hyps =
  it_mkProd_or_LetIn b (name_context env hyps)
let it_mkLambda_or_LetIn_name env b hyps =
  it_mkLambda_or_LetIn b (name_context env hyps)

(**********************************************************************)
(* Fresh names *)

let default_x = id_of_string "x"

(* Looks for next "good" name by lifting subscript *)

let next_ident_away_from id bad =
  let rec name_rec id = if bad id then name_rec (lift_subscript id) else id in
  name_rec id

(* Restart subscript from x0 if name starts with xN, or x00 if name
   starts with x0N, etc *)

let restart_subscript id =
  if not (has_subscript id) then id else
    (* Ce serait sans doute mieux avec quelque chose inspiré de
     *** make_ident id (Some 0) *** mais ça brise la compatibilité... *)
    forget_subscript id

(* Now, there are different renaming strategies... *)

(* 1- Looks for a fresh name for printing in cases pattern *)

let next_name_away_in_cases_pattern na avoid =
  let id = match na with Name id -> id | Anonymous -> default_x in
  next_ident_away_from id (fun id -> List.mem id avoid or is_constructor id)

(* 2- Looks for a fresh name for introduction in goal *)

(* The legacy strategy for renaming introduction variables is not very uniform:
   - if the name to use is fresh in the context but used as a global
     name, then a fresh name is taken by finding a free subscript
     starting from the current subscript;
   - but if the name to use is not fresh in the current context, the fresh
     name is taken by finding a free subscript starting from 0 *)

let next_ident_away_in_goal id avoid =
  let id = if List.mem id avoid then restart_subscript id else id in
  let bad id = List.mem id avoid || (is_global id & not (is_section_variable id)) in
  next_ident_away_from id bad

let next_name_away_in_goal na avoid =
  let id = match na with Name id -> id | Anonymous -> id_of_string "H" in
  next_ident_away_in_goal id avoid

(* 3- Looks for next fresh name outside a list that is moreover valid
   as a global identifier; the legacy algorithm is that if the name is
   already used in the list, one looks for a name of same base with
   lower available subscript; if the name is not in the list but is
   used globally, one looks for a name of same base with lower subscript
   beyond the current subscript *)

let next_global_ident_away id avoid =
  let id = if List.mem id avoid then restart_subscript id else id in
  let bad id = List.mem id avoid || is_global id in
  next_ident_away_from id bad

(* 4- Looks for next fresh name outside a list; if name already used,
   looks for same name with lower available subscript *)

let next_ident_away id avoid =
  if List.mem id avoid then
    next_ident_away_from (restart_subscript id) (fun id -> List.mem id avoid)
  else id

let next_name_away_with_default default na avoid =
  let id = match na with Name id -> id | Anonymous -> id_of_string default in
  next_ident_away id avoid

let next_name_away = next_name_away_with_default "H"

let make_all_name_different env =
  let avoid = ref (ids_of_named_context (named_context env)) in
  process_rel_context
    (fun (na,c,t) newenv ->
       let id = next_name_away na !avoid in
       avoid := id::!avoid;
       push_rel (Name id,c,t) newenv)
    env

(* 5- Looks for next fresh name outside a list; avoids also to use names that
   would clash with short name of global references; if name is already used,
   looks for name of same base with lower available subscript beyond current
   subscript *)

let visibly_occur_id id c =
  let rec occur c = match kind_of_term c with
    | Const _ | Ind _ | Construct _ | Var _
	  when shortest_qualid_of_global Idset.empty (global_of_constr c)
	    = qualid_of_ident id -> raise Occur
    | _ -> iter_constr occur c
  in
  try occur c; false
  with Occur -> true
    | Not_found -> false (* Happens when a global is not in the env *)

let next_ident_away_for_default_printing t id avoid =
  let bad id = List.mem id avoid or visibly_occur_id id t in
  next_ident_away_from id bad

let next_name_away_for_default_printing t na avoid =
  let id = match na with
  | Name id   -> id
  | Anonymous ->
      (* In principle, an anonymous name is not dependent and will not be *)
      (* taken into account by the function compute_displayed_name_in; *)
      (* just in case, invent a valid name *)
      id_of_string "H" in
  next_ident_away_for_default_printing t id avoid

(**********************************************************************)
(* Displaying terms avoiding bound variables clashes *)

(* Renaming strategy introduced in December 1998:

   - Rule number 1: all names, even if unbound and not displayed, contribute
     to the list of names to avoid
   - Rule number 2: only the dependency status is used for deciding if
     a name is displayed or not

   Example:
   bool_ind: "forall (P:bool->Prop)(f:(P true))(f:(P false))(b:bool), P b" is
   displayed "forall P:bool->Prop, P true -> P false -> forall b:bool, P b"
   but f and f0 contribute to the list of variables to avoid (knowing
   that f and f0 are how the f's would be named if introduced, assuming
   no other f and f0 are already used).
*)

type renaming_flags =
  | RenamingForCasesPattern
  | RenamingForGoal
  | RenamingElsewhereFor of constr

let next_name_for_display flags =
  match flags with
  | RenamingForCasesPattern -> next_name_away_in_cases_pattern
  | RenamingForGoal -> next_name_away_in_goal
  | RenamingElsewhereFor t -> next_name_away_for_default_printing t

(* Remark: Anonymous var may be dependent in Evar's contexts *)
let compute_displayed_name_in flags avoid na c =
  if na = Anonymous & noccurn 1 c then
    (Anonymous,avoid)
  else
    let fresh_id = next_name_for_display flags na avoid in
    let idopt = if noccurn 1 c then Anonymous else Name fresh_id in
    (idopt, fresh_id::avoid)

let compute_and_force_displayed_name_in flags avoid na c =
  if na = Anonymous & noccurn 1 c then
    (Anonymous,avoid)
  else
    let fresh_id = next_name_for_display flags na avoid in
    (Name fresh_id, fresh_id::avoid)

let compute_displayed_let_name_in flags avoid na c =
  let fresh_id = next_name_for_display flags na avoid in
  (Name fresh_id, fresh_id::avoid)

let rec rename_bound_vars_as_displayed avoid c =
  let rec rename avoid c =
    match kind_of_term c with
    | Prod (na,c1,c2)  ->
	let na',avoid' = compute_displayed_name_in (RenamingElsewhereFor c2) avoid na c2 in
	mkProd (na', c1, rename avoid' c2)
    | LetIn (na,c1,t,c2) ->
	let na',avoid' = compute_displayed_let_name_in (RenamingElsewhereFor c2) avoid na c2 in
	mkLetIn (na',c1,t, rename avoid' c2)
    | Cast (c,k,t) -> mkCast (rename avoid c, k,t)
    | _ -> c
  in
  rename avoid c
