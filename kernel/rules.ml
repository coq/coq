(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Term
open Environ
open Declarations
open Cime
open Reduction
open Typeops
open Symbol
open Entries
open Names
open Ordering
open Precedence

(* check monotone arguments *)
let check_mons arity mons antimons =
  let f i =
    if List.mem i mons then (
      if List.mem i antimons then
	error (string_of_int i ^
	       " is declared both monotone and anti-monotone.")
      else Pos
    ) else (
      if List.mem i antimons then Neg
      else Nul
    )
  in Array.init arity f

(* check that a symbol declaration is correct *)
let check_symbol env t se =
  let ar = se.symb_entry_arity
  and eq = se.symb_entry_eqth
  and st = se.symb_entry_status
  and mons = se.symb_entry_mons
  and antimons = se.symb_entry_mons in
  let deltas = check_mons ar mons antimons in
    if nb_prod t < ar then error "Type not compatible with arity.";
    if not (is_linear st) then error "Non-linear status.";
    { symb_arity = se.symb_entry_arity;
      symb_eqth = se.symb_entry_eqth;
      symb_status = se.symb_entry_status;
      symb_mons = deltas;
      symb_termin = General_Schema; }

(* say if a constr is headed by a symbol *)
let is_symbol_headed env c =
  match kind_of_term c with
    | App (f,_) ->
        begin
	  match kind_of_term f with
	    | Const kn -> is_symbol (lookup_constant kn env)
	    | _ -> false
        end
    | Const kn -> is_symbol (lookup_constant kn env)
    | _ -> false

(* get head symbol of a symbol headed LHS *)
let head_symbol c =
  match kind_of_term c with
    | App (f,_) ->
        begin
	  match kind_of_term f with
	    | Const kn -> kn
	    | _ -> error "Ill-formed rule."
        end
    | Const kn -> kn
    | _ -> error "Ill-formed rule."

(* get head symbol and its arguments *)
let head_symbol_and_args =
  let empty = Array.make 0 mkProp in fun c ->
    match kind_of_term c with
      | App (f,va) ->
          begin
	    match kind_of_term f with
	      | Const kn -> (kn,va)
	      | _ -> error "Ill-formed rule."
          end
      | Const kn -> (kn, empty)
      | _ -> error "Ill-formed rule."

(* say if a constr is algebraic *)
let is_algebraic env =
  let rec is_alg c =
    match kind_of_term c with
      |  App (f,va) ->
           begin
	     match kind_of_term f with
	       | Const kn -> is_symbol (lookup_constant kn env)
		   & array_for_all is_alg va
               | Construct _ -> array_for_all is_alg va
	       | _ -> false
           end
      | Construct _ | Rel _ -> true
      | Const kn -> is_symbol (lookup_constant kn env)
      | _ -> false
  in is_alg

(* say if an algebraic constr is linear *)
let is_linear =
  let vars = ref [] in
  let rec is_lin c =
    match kind_of_term c with
      | Rel i -> if List.mem i !vars then false else (vars := i::!vars; true)
      | App (f,va) -> array_for_all is_lin va
      | _ -> true
  in fun c -> vars := []; is_lin c

(* insert an element in a sorted list *)
let insert inf x =
  let rec ins = function
    | y::l' as l -> if inf x y then x::l else y::(ins l')
    | _ -> [x]
  in ins

(* give the variables and the number of occurrences *)
let var_occs =
  let vars = ref [] and inf x y = (fst x) <= (fst y) in
  let rec occs c =
    match kind_of_term c with
      | Rel i ->
	  begin
	    try incr (List.assoc i !vars)
	    with Not_found -> vars := insert inf (i,ref 1) !vars
	  end
      | App (f,va) -> Array.iter occs va
      | _ -> ()
  in fun c -> vars := []; occs c; List.map (fun (x,r) -> (x,!r)) !vars

(* say if a rule if non-duplicating *)
let is_non_dupl (l,r) =
  let rec is_greater = function
    | ((x1,n1)::l1' as l1), ((x2,n2)::l2' as l2) ->
	if x1=x2 then n1>=n2
	else if x1<x2 then is_greater (l1',l2)
	else is_greater (l1,l2')
    | _ -> true
  in is_greater (var_occs l, var_occs r)

(* check subject reduction *)
let is_welltyped env envl envr (l,r) =
  let kn,args = head_symbol_and_args l in
  let cb = lookup_constant kn env in
  let t = hnf_prod_applist env cb.const_type (Array.to_list args) in
  let tl = j_type (typing envl l) and tr = j_type (typing envr r) in
    try let _ = conv envl tl t and _ = conv envr tr t in true
    with NotConvertible -> false

(* say if symbols in [c] are smaller or equivalent to [kn]
   and if symbols equivalent to [kn] are applied to arguments
   smaller than [vl] *)
let are_rec_calls_smaller env prec kn status vl =
  let rec are_rc_smaller c =
    match kind_of_term c with
      | App (f,va) ->
	  begin
	    match kind_of_term f with
	      | Const kn' ->
		  begin
		    match compare prec kn' kn with
		      | Smaller -> array_for_all are_rc_smaller va
		      | Equivalent -> is_struct_smaller_vec status va vl
			  & array_for_all are_rc_smaller va
		      | _ -> false
		  end
	      | _ -> are_rc_smaller f & array_for_all are_rc_smaller va
	  end
      | Const kn' -> compare prec kn' kn = Smaller
      | Construct _ | Rel _ -> true
      | Lambda (_,t,b) | Prod (_,t,b) -> are_rc_smaller t & are_rc_smaller b
      | _ -> false
  in are_rc_smaller

(* say if a rule satisfies the General Schema *)
let satisfies_GS env (l,r) =
  let kn,vl = head_symbol_and_args l in
  let cb = lookup_constant kn env in
  are_rec_calls_smaller env (prec env) kn (status cb) vl r

(* check that the addition of some rules is correct *)
let check_rules env re =

  (* check context and substitution *)
  let ctx = List.map (fun (id,t) -> (id,LocalAssum t)) re.rules_entry_ctx
  and subs = List.map (fun (id,t) -> (id,LocalDef t)) re.rules_entry_subs in
  let envr,ctx',_ = infer_local_decls env ctx in
  let envl,subs',_ = infer_local_decls envr subs in
  let rules = re.rules_entry_list in

  (* check LHS *)
  let is_LHS_ok (l,r) = is_algebraic env l & is_symbol_headed env l in
    if not (List.for_all is_LHS_ok rules)
    then error "There is an ill-formed rule.";

  (* check subject reduction *)
  if not (List.for_all (is_welltyped env envl envr) rules)
  then error "There is a rule not type-preserving.";

  (* check confluence *)
  if not (is_confluent (cime env) rules)
  then error "Non-confluent rules";

  (* check left-linearity *)
  let is_linear_rule (l,_) = is_linear l in
    if not (List.for_all is_linear_rule rules)
    then error "There is a rule not left-linear.";

  (* check termination *)
  if not (List.for_all (satisfies_GS env) rules)
  then error "There is a rule not satisfying the termination criterion.";

  (* end check_rules *)
  print_endline "Rules accepted.";
  { rules_ctx = ctx'; rules_subs = subs'; rules_list = rules }
