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
open Positivity
open Type_errors

(***********************************************************************)
(*                       symbol declarations                           *)
(***********************************************************************)

(* check monotone arguments *)
let check_mons arity mons antimons =
  let f i =
    if List.mem i mons then (
      if List.mem i antimons then
	symbol_error (Both_monotonic_and_antimonotonic i)
      else Pos
    ) else (
      if List.mem i antimons then Neg
      else Nul
    )
  in Array.init arity f

(* say if a type is compatible with commutativity alone *)
let check_C t =
  match kind_of_term t with
    | Prod (Anonymous,u,v) ->
	(match kind_of_term v with
	   | Prod (Anonymous,u',v) ->
	       if not (eq_constr u u') then
		 symbol_error Type_not_compatible_with_eqth
	   | _ -> symbol_error Type_not_compatible_with_eqth)
    | _ -> symbol_error Type_not_compatible_with_eqth

(* say if a type is compatible with commutativity and associativity *)
let check_AC t =
  match kind_of_term t with
    | Prod (Anonymous,u,v) ->
	(match kind_of_term v with
	   | Prod (Anonymous,u',u'') ->
	       if not (eq_constr u u' & eq_constr u u'') then
		 symbol_error Type_not_compatible_with_eqth
	   | _ -> symbol_error Type_not_compatible_with_eqth)
    | _ -> symbol_error Type_not_compatible_with_eqth

(* say if a type is compatible with an equational theory *)
let check_eqth = function
  | C -> check_C
  | AC -> check_AC
  | _ -> (fun _ -> ())

(* compute accessibility of arguments *)
let compute_access env ar t =
  let l,u = decompose_prod_n ar t in
    match kind_of_term (get_head u) with
      | Ind (kn,_) ->
	  let f (_,v) = occur_mind env kn Pos v in  
	    array_init_by_list_map ar false f l
      | Const kn ->
	  let f (_,v) = occur_const env kn Pos v in  
	    array_init_by_list_map ar false f l
      | _ -> Array.make ar false

(* check that a symbol declaration is correct *)
let check_symbol env t se =
  let ar = se.symb_entry_arity and eq = se.symb_entry_eqth
  and st = se.symb_entry_status and mons = se.symb_entry_mons
  and antimons = se.symb_entry_antimons
  and prec_defs = se.symb_entry_prec_defs in
    if nb_prod t < ar then symbol_error Type_not_compatible_with_arity;
    check_eqth eq t;
    let deltas = check_mons ar mons antimons
    and accs = compute_access env ar t in
      { symb_arity = ar; symb_eqth = eq;
	symb_status = st; symb_mons = deltas;
	symb_termin = General_Schema; symb_acc = accs;
	symb_prec_defs = prec_defs }

(***********************************************************************)
(*                        rules declarations                           *)
(***********************************************************************)

exception Error_in_rule of rule_error

let rule_err e = raise (Error_in_rule e)

(* check that kn is a symbol *)
let check_if_symbol env kn =
  if not (is_symbol (lookup_constant kn env)) then
    rule_err (Not_a_symbol kn)

(* say if a constr is headed by a symbol *)
let check_if_symbol_headed env c =
  match kind_of_term (collapse c) with
    | App (f,_) ->
        (match kind_of_term f with
	   | Const kn -> check_if_symbol env kn
	   | _ -> rule_err Not_symbol_headed)
    | Const kn -> check_if_symbol env kn
    | _ -> rule_err Not_symbol_headed

(* get head symbol of a symbol headed term *)
let head_symbol c =
  match kind_of_term (collapse c) with
    | App (f,_) ->
	(match kind_of_term f with
	   | Const kn -> kn
	   | _ -> invalid_arg "head_symbol")
    | Const kn -> kn
    | _ -> invalid_arg "head_symbol"

(* get head symbol and its arguments *)
let head_symbol_and_args c =
  match kind_of_term (collapse c) with
    | App (f,va) ->
	(match kind_of_term f with
	   | Const kn -> (kn,va)
	   | _ -> invalid_arg "head_symbol_and_args")
    | Const kn -> (kn,[||])
    | _ -> invalid_arg "head_symbol_and_args"

(* say if a constr is algebraic *)
let check_if_algebraic env =
  let rec check_alg c =
    match kind_of_term (collapse c) with
      | App (f,va) ->
	  (match kind_of_term f with
	     | Const kn -> check_if_symbol env kn; Array.iter check_alg va
             | Construct _ -> Array.iter check_alg va
	     | _ -> rule_err (Not_a_symbol_or_a_constructor f))
      | Construct _ | Rel _ -> ()
      | Const kn -> check_if_symbol env kn
      | _ -> rule_err (Not_algebraic c)
  in check_alg

(* say if a constr is an admissible RHS *)
let check_rhs env =
  let rec chk_rhs c =
    match kind_of_term c with
      | App (f,va) -> chk_rhs f; Array.iter chk_rhs va
      | Construct _ | Ind _ | Const _ | Rel _ -> ()
      | Prod (_,t,b) | Lambda (_,t,b) -> chk_rhs t; chk_rhs b
      | _ -> rule_err (Term_not_admissible_in_RHS c)
  in chk_rhs

(* say if an algebraic constr is linear *)
let is_linear =
  let vars = ref [] in
  let rec is_lin c =
    match kind_of_term c with
      | Rel i -> if List.mem i !vars then false else (vars := i::!vars; true)
      | App (f,va) -> is_lin f; array_for_all is_lin va
      | _ -> true
  in fun c -> vars := []; is_lin c

(* check if an algebraic constr is linear *)
let check_linear =
  let vars = ref [] in
  let rec check_lin c =
    match kind_of_term c with
      | Rel i ->
	  if List.mem i !vars then rule_err Not_linear else vars := i::!vars
      | App (f,va) -> check_lin f; Array.iter check_lin va
      | _ -> ()
  in fun c -> vars := []; check_lin c

(* say if an algebraic rule if non-duplicating *)
let is_non_dupl =
  let vars = ref (Array.make 10 0) in
  let init() = Array.fill !vars 0 (Array.length !vars) 0
  and update func i =
    let n = Array.length !vars in
      if i >= n then vars := Array.append !vars (Array.make (i-n+10) 0);
      !vars.(i) <- func !vars.(i)
  in
  let occs func =
    let rec occs_rec c =
      match kind_of_term c with
	| Rel i -> update func i
	| App (f,va) -> occs_rec f; Array.iter occs_rec va
	| _ -> ()
    in occs_rec
  in fun (l,r) -> init(); occs succ l; occs pred r;
    array_for_all (fun v -> v >= 0) !vars

(* check subject reduction *)
let check_typing env envl envr (l,r) =
  let kn,args = head_symbol_and_args l in
  let cb = lookup_constant kn env in
  let t = hnf_prod_applist env cb.const_type (Array.to_list args) in
  let tl = j_type (typing envl l) and tr = j_type (typing envr r) in
  let _ = conv envl tl t and _ = conv envr tr t in ()

(* sets of integers *)
module IntOrd = struct
  type t = int
  let compare = Pervasives.compare
end
module IntSet = Set.Make(IntOrd)

(* compute the variables accessible in an array of algebraic terms *)
let acc_vars env =
  let rec accs c =
    match kind_of_term (collapse_appl c) with
      | App (f,va) ->
	  (match kind_of_term f with
	     | Const kn ->
		 (match (lookup_constant kn env).const_symb with
		    | Some si ->
			let f i s c =
			  if si.symb_acc.(i) then IntSet.union s (accs c)
			  else s
			and vb =
			  if Array.length va <= si.symb_arity then va
			  else Array.sub va 0 si.symb_arity
			in array_fold_left_i f IntSet.empty vb
		    | _ -> IntSet.empty)
	     | Construct _ -> Array.fold_left add_accs IntSet.empty va
	     | _ -> IntSet.empty)
      | Rel i -> IntSet.singleton i
      | _ -> IntSet.empty
  and add_accs s c = IntSet.union s (accs c)
  in Array.fold_left add_accs IntSet.empty

(* say if symbols in [c] are smaller or equivalent to [kn]
          symbols equivalent to [kn] are applied to arguments smaller than [vl]
          variables in [c] are accessible in [vl] *)
let check_rec_calls env prec kn status vl =
  let accs = acc_vars env vl in
  let rec check_rc c =
    match kind_of_term c with
      | App (f,va) ->
	  (match kind_of_term f with
	     | Const kn' ->
		 (match compare prec kn' kn with
		    | Smaller -> Array.iter check_rc va
		    | Equivalent ->
			if not (is_struct_smaller_vec status va vl) then
			  rule_err (Recursive_call_not_smaller (status,va,vl))
			else Array.iter check_rc va
		    | _ -> rule_err (Symbol_not_smaller (kn',kn)))
	     | _ -> check_rc f; Array.iter check_rc va)
      | Const kn' ->
	  if compare prec kn' kn <> Smaller then
	    rule_err (Symbol_not_smaller (kn',kn))
      | Construct _ | Ind _ -> ()
      | Rel i ->
	  if not (IntSet.mem i accs) then rule_err (Variable_not_accessible c)
      | Lambda (_,t,b) | Prod (_,t,b) -> check_rc t; check_rc b
      | _ -> rule_err (Term_not_admissible_in_RHS c)
  in check_rc

(* say if a rule satisfies the General Schema *)
let check_GS env (l,r) =
  let kn,vl = head_symbol_and_args l in
  let cb = lookup_constant kn env in
  check_rec_calls env (prec env) kn (status cb) vl r

(* check that the addition of some rules is correct *)
let check_rules env re =

  (* check context and substitution *)
  let ctx = List.map (fun (id,t) -> (id,LocalAssum t)) re.rules_entry_ctx
  and subs = List.map (fun (id,t) -> (id,LocalDef t)) re.rules_entry_subs in
  let envr,ctx',_ = infer_local_decls env ctx in
  let envl,subs',_ = infer_local_decls envr subs in
  let rules = re.rules_entry_list in

  (* check rule syntax and subject reduction *)
  let check_rule ((l,r) as rule) =
    try
      check_if_algebraic env l;
      check_if_symbol_headed env l;
      check_rhs envr r;
      check_typing env envl envr rule;
      check_linear l;
      check_GS env rule
    with Error_in_rule e -> rule_error rule envl envr e
  in List.iter check_rule rules;

    (* check local confluence *)
    if not (is_locally_confluent (cime env) rules)
    then condition_error Not_locally_confluent;

    (* end check_rules *)
    print_endline "Rules accepted.";
    { rules_ctx = ctx'; rules_subs = subs'; rules_list = rules }
