(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Names
open Declarations
open Decl_kinds
open Util
open Symbol
open Print

(* CiME *)
open Signatures
open Gen_terms
open Variables
open Rewrite_rules
open Naive_dnet
open Rewriting
open Innermost
(* open Hcons *)
open Abstract_rewriting
open Orderings_generalities

(* type for CiME symbols *)
type symb = Sapp | Slambda | Sprod | Sconstr of constr | Sname of name
	    | Sshift of int | Sevar of int | Sletin | Scase
	    | Sfix of (int array * int) | Scofix of int

(* arity of a symbol *)
let arity cmap imap f =
  match f with
    | Sshift _ -> 1
    | Sapp -> 2
    | Slambda | Sprod -> 3
    | Sconstr c ->
	begin
	  match kind_of_term c with
	    | Const kn ->
		begin
		  match (KNmap.find kn cmap).const_symb with
		    | Some si -> si.symb_arity
		    | _ -> 0
		end
	    | Construct ((kn,i),n) ->
		(KNmap.find kn imap).mind_packets.(i).mind_cons_arity.(n-1)
	    | _ -> 0
	end
    | _ -> 0

(* say if a symbol is AC *)
let is_ac cmap f = 
  match f with
    | Sconstr c ->
	begin
	  match kind_of_term c with
	    | Const kn ->
		begin
		  match (KNmap.find kn cmap).const_symb with
		    | Some si -> si.symb_eqth = AC
		    | _ -> false
		end
	    | _ -> false
	end
    | _ -> false

(* say if a symbol is C *)
let is_commutative cmap f =
  match f with
    | Sconstr c ->
	begin
	  match kind_of_term c with
	    | Const kn ->
		begin
		  match (KNmap.find kn cmap).const_symb with
		    | Some si -> si.symb_eqth = C
		    | _ -> false
		end
	    | _ -> false
	end
    | _ -> false

(* say if a symbol is neither AC nor C *)
let is_free cmap f =
  match f with
    | Sconstr c ->
	begin
	  match kind_of_term c with
	    | Const kn ->
		begin
		  match (KNmap.find kn cmap).const_symb with
		    | Some si -> si.symb_eqth = Free
		    | _ -> true
		end
	    | _ -> true
	end
    | _ -> true

(* string of a symbol *)
let string_of_symb imap f =
  match f with
    | Sapp -> "@"
    | Slambda -> "%"
    | Sprod -> "!"
    | Sname n -> string_of_name n
    | Sshift n -> "^" ^ (string_of_int n)
    | Sconstr c ->
	begin
	  match kind_of_term c with
	    | Const kn -> string_of_kn kn (* string_of_label (label kn) *)
	    | Construct ((kn,i),n) -> string_of_id
		(KNmap.find kn imap).mind_packets.(i).mind_consnames.(n-1)
	    | Rel i -> "x" ^ (string_of_int i)
	    | Fix ((_,i),(vn,_,_)) -> string_of_name vn.(i)
	    | CoFix (i,(vn,_,_)) -> string_of_name vn.(i)
	    | Ind (kn,i) -> string_of_id
		(KNmap.find kn imap).mind_packets.(i).mind_typename
	    | _ -> "?" (* TO DO ? *)
	end
    | _ -> "?" (* TO DO ? *)

(* CiME signature from maps for constants and inductives *)
class sigma cmap imap = object
  method arity = arity cmap imap
  method is_ac = is_ac cmap
  method is_commutative = is_commutative cmap
  method is_free = is_free cmap
  method contains_ac_symbols = true
  method contains_only_free_symbols = false
  method string_of_symbol = string_of_symb imap
  method symbol_fix (f:symb) = Prefix
  (* method hash_symbol (f:symb) = hash_symbol f
  method all_symbols = ([]:symb list) (* TO_DO ? *) *)
  method smallest_constant (ord:symb ordering) = Sapp
end

(* empty signature *)
let empty_sign = new sigma KNmap.empty KNmap.empty

(* hash tables for CiME *)
(* let hcime = HashTerm.create 1997
let phcime = HashTerm.create 1997 *)

(* module for CiME rewriting *)
module Cime = MakeACRewriting(
  struct
    type t (* symbol *) = symb
    (* type hct =  symbol Gen_terms.HashTerm.t 
    type phct =  symbol Signatures.protect_var_sig Gen_terms.HashTerm.t
    let my_hct = hcime
    let my_phct = phcime *)
  end)

open Cime

(* basic primitives for building terms and rules *)
(* let make_term = make_term hcime *) (* TO DO ? cannot use my_hct ! *)
let make_term f l = Term(f,l)
(* let make_head_flatten_term sign = make_head_flatten_term sign hcime *)
let make_head_flatten_term sign f l = head_flatten_term sign (Term(f,l))
(* let make_var_term = make_var_term hcime *)
let make_var_term v = Var v
let make_rule sign = make_rule sign (* None *)

(* create an array of variables *)
let mkvars n = Array.of_list (List.map make_var_term (fresh_variables n))

(* variables for CiME rules *)
let vars = ref (mkvars 10)

(* primitives for building terms *)
let constr c = make_term (Sconstr c)
let flat sign c = make_head_flatten_term sign (Sconstr c)
let var i = !vars.(i)
let name n = make_term (Sname n) []
let app x y = make_term Sapp [x;y]
let lambda n t b = make_term Slambda [name n;t;b]
let prod n t b = make_term Sprod [name n;t;b]
let shift n x = if n<=0 then x else make_term (Sshift n) [x]

(* for debugging *)
let prt sign =
  let rec prt_rec = function
    | Term (f,l) ->
	pr (sign#string_of_symbol f);
	if l <> [] then (prch '('; pr_list prt_rec "," l; prch ')')
    | Var v -> pr (string_of_var_id v)
  in prt_rec

let prc sign =
  let rec prc_rec c =
    match kind_of_term c with
      | App (f,va) ->
	  if Array.length va = 0 then prc_rec f
	  else prch '('; prc_rec f; Array.iter pr_sep va; prch ')'
      | Prod (n,t,b) -> prch '('; pr_name n; prch ':';
	  prc_rec t; prch ')'; prc_rec b
      | Lambda (n,t,b) -> prch '['; pr_name n; prch ':';
	  prc_rec t; prch ']'; prc_rec b
      | _ -> pr (sign#string_of_symbol (Sconstr c))
  and pr_sep c = prch ' '; prc_rec c
  in prc_rec

let prv sign va =
  let pr_sep i c = if i>0 then prch ','; prc sign c in
    if Array.length va = 0 then pr "<empty>"
    else Array.iteri pr_sep va

let prr sign r = prt sign r.lhs; pr " -> "; prt sign r.rhs

(* from LHS constr to cime *)
let cime_of_lhs_constr sign =
  let rec coc c =
    match kind_of_term c with
      | App (f,va) ->
	  begin
	    let g,l = decomp f (Array.fold_right coc_cons va []) in
	      match kind_of_term g with
		| Const kn -> flat sign g l
		| Construct _ -> constr g l
		| _ -> anomaly "cime_of_lhs_constr"
	  end
      | Rel i -> var i
      | Const _ | Construct _ -> constr c []
      | _ -> anomaly "cime_of_lhs_constr"
  and coc_cons c l = (coc c)::l
  and decomp c l =
    match kind_of_term c with
      | App (f,va) -> decomp f (Array.fold_right coc_cons va l)
      | _ -> c,l
  in coc

(* from RHS constr to cime *)
let cime_of_rhs_constr sign =
  let rec coc k c = (* k = number of lambda/prod's gone through *)
    match kind_of_term c with
      | App (f,va) ->
	  begin
	    let g,l = decomp k f (coc_array k va) in
	      match kind_of_term g with
		| Const _ -> flat sign g l
		| Construct _ -> constr g l
		| _ -> List.fold_right (fun c t -> app t c) l (coc k g)
	  end
      | Rel i ->
	  let j = i - k in if j >= 0 then shift k (var j) else constr c []
      | Lambda (n,t,b) -> lambda n (coc k t) (coc (k+1) b)
      | Prod (n,t,b) -> prod n (coc k t) (coc (k+1) b)
      | Const _ | Construct _ -> constr c []
      | _ -> anomaly "cime_of_rhs_constr"
  and coc_cons k c l = (coc k c)::l
  and coc_array k a = Array.fold_right (coc_cons k) a []
  and decomp k c l =
    match kind_of_term c with
      | App (f,va) -> decomp k f (Array.fold_right (coc_cons k) va l)
      | _ -> c,l
  in coc 0

(* from constr to cime *)
let cime_of_constr sign =
  let rec coc c =
    match kind_of_term c with
      | App (f,va) ->
	  begin
	    let g,l = decomp f (Array.fold_right coc_cons va []) in
	      match kind_of_term g with
		| Const kn -> flat sign g l
		| _ -> constr g l
	  end
      | Prod (n,t,b) -> prod n (coc t) (coc b)
      | Lambda (n,t,b) -> lambda n (coc t) (coc b)
      | _ -> constr c []
  and coc_cons c l = (coc c)::l
  and decomp c l =
    match kind_of_term c with
      | App (f,va) -> decomp f (Array.fold_right coc_cons va l)
      | _ -> c,l
  in coc

(* give the application form *)
let app_form l =
  let rec app_form_rec x acc =
    match x (* x.node *) with
      | Term (Sapp,[x';y']) -> app_form_rec x' (y'::acc)
      | _ -> (x,acc)
  in match l with
    | [x;y] -> app_form_rec x [y]
    | _ -> anomaly "Cime.app_form"

(* get name *)
let get_name g =
  match g (* g.node *) with
    | Term (Sname n,_) -> n
    | _ -> anomaly "Cime.get_name"

(* shift a constr *)
let shift_constr p =
  if p<=0 then fun c -> c
  else
    let rec shift k c = (* k = number of lambda/prod's gone through *)
      match kind_of_term c with
	| Rel i -> if i <= k then c else mkRel (i+p)
	| App (f,va) -> mkApp (shift k f,Array.map (shift k) va)
	| Lambda (n,t,b) -> mkLambda (n,shift k t,shift (k+1) b)
	| Prod (n,t,b) -> mkProd (n,shift k t,shift (k+1) b)
	| _ -> c
    in shift 0

(* unflatten the application of 'f' and apply 'w' to its arguments *)
let unflat w f =
  let rec unflat_rec l =
    match l with
      | [] -> anomaly "Cime.unflat"
      | x::l' ->
	  begin
	    match l' with
	      | [] -> w x
	      | _ -> mkApp (f, [|w x;unflat_rec l'|])
	  end
  in unflat_rec

(* from cime to constr *)
let constr_of_cime sign =
  let rec coc n t = (* n = number of shifts to do *)
    match t (* t.node *) with
      | Term (f,l) ->
	  begin
	    match f with
	      | Sapp ->
		  let (g,m) = app_form l in
		    mkApp (coc n g,array_init_by_list_map (coc n) mkProp m)
	      | Slambda ->
		  begin
		    match l with
		      | [g;t;b] -> mkLambda (get_name g,coc n t,coc n b)
		      | _ -> anomaly "constr_of_cime"
		  end
	      | Sprod ->
		  begin
		    match l with
		      | [g;t;b] -> mkProd (get_name g,coc n t,coc n b)
		      | _ -> anomaly "constr_of_cime"
		  end
	      | Sconstr c ->
		  begin
		    match l with
		      | [] -> shift_constr n c
		      | _ ->
			  if sign#is_ac f then
			    unflat (coc n) (shift_constr n c) l
			  else mkApp (shift_constr n c,
				      array_init_by_list_map (coc n) mkProp l)
		  end
	      | Sshift p ->
		  begin
		    match l with
		      | [u] -> coc (n+p) u
		      | _ -> anomaly "constr_of_cime"
		  end
	      | _ -> anomaly "constr_of_cime"
	  end
      | _ -> anomaly "constr_of_cime"
  in coc 0

(* from Coq rule to CiME rule *)
let cime_rule_of_coq_rule sign (l,r) =
  let l' = cime_of_lhs_constr sign l
  and r' = cime_of_rhs_constr sign r
  in make_rule sign l' r'

(* environment for CiME *)
type env = {
  (* sign : signature; *)
  cmap : constant_body KNmap.t;
  imap : mutual_inductive_body KNmap.t;
  rules : rule list;
  dnet : compiled_rules }

(* empty environment *)
let empty_env = {
  (* sign = empty_sign; *)
  cmap = KNmap.empty;
  imap = KNmap.empty;
  rules = [];
  dnet = compile empty_sign [] }

(* get the signature corresponding to an environment *)
let sign =
  let cmapref = ref empty_env.cmap
  and imapref = ref empty_env.imap and sigref = ref empty_sign in
    fun env ->
      if !cmapref != env.cmap or !imapref != env.imap then
	(cmapref := env.cmap; imapref := env.imap;
	 sigref := new sigma env.cmap env.imap);
      !sigref

(* add symbol and inductive *)
let add_symbol newcmap env = { env with cmap = newcmap }
let add_inductive newimap env = { env with imap = newimap }

(* add rules *)
let add_rules rb env =
  let n = List.length rb.rules_ctx in
  if n > Array.length !vars then vars := mkvars (n+10);
    let s = sign env in
    let new_rules = List.map (cime_rule_of_coq_rule s) rb.rules_list in
    let rules = new_rules @ env.rules in
    let dnet = compile s rules in
      { env with rules = rules; dnet = dnet }

(* module for confluence checking *)
module Confluence = Confluence.Make(Cime)

(* say if the addition of l preserves confluence *)
let is_confluent env l =
  let s = sign env in
  let l' = List.map (cime_rule_of_coq_rule s) l in
    Confluence.is_confluent s default (l' @ env.rules)

(* hash table for normal forms *)
(* let hcime_nf = Hashtbl.create 1997
let memo t u = Hashtbl.add hcime_nf t u
and find t = Hashtbl.find hcime_nf t *)
let force_norm = force_normalize (* find memo *)

(* return None if [t] is already in normal form
   return [Some t'] where [t'] is the normal form of [t] otherwise *)
let normalize env t =
  try
    let s = sign env in (* pr"rules: ";pr_list (prr s) "; " env.rules;pnl(); *)
    let t' = cime_of_constr s t in
    let nf = force_norm s default env.dnet t' in
    let nf' = constr_of_cime s nf in
      Some nf'
  with Irreducible -> None

(* give the normal form *)
let nf env t =
  match normalize env t with
    | Some nf -> nf
    | _ -> t

(* say if a term is in normal form *)
(* let is_nf env t =
  try
    let s = sign env in
    let t' = cime_of_constr s t in
    let red = compiled_ac_rewrite_at_top s hcime phcime env.dnet in
    let _ = safe_force_innermost_normalize
	      find memo s hcime_nf 1 red t' in
      true
  with
    | Irreducible -> false
    | Unnormalized _ -> true
*)

(* cap and aliens of a constr *)
let cap_and_aliens sign =
  let rec cap c =
    match kind_of_term c with
      | App (f,va) ->
	  begin
	    match kind_of_term f with
	      | Const _ ->
		  let (caps,aliens) = cap_array va in flat sign f caps, aliens
	      | _ ->
		  let (caps,aliens) = cap_array va in constr f caps, aliens
	  end
      | _ -> constr c [], [c]
  and cap_cons c (caps,aliens) =
    let (newcaps,newaliens) = cap c in newcaps::caps, newaliens @ aliens
  and cap_array va = Array.fold_right cap_cons va ([],[])
  in cap

(* translation of a constr for equivalence test
arities are not respected *)
let cime_of_eq_constr sign =
  let rec coc c =
    match kind_of_term c with
      | Evar (i,va) -> make_term (Sevar i) (Array.fold_right coc_cons va [])
      | Cast (c,_) -> coc c
      | Prod (_,t,c) -> make_term Sprod [coc t; coc c]
      | Lambda (_,t,c) -> make_term Slambda [coc t; coc c]
      | LetIn (_,b,t,c) -> make_term Sletin [coc b; coc t; coc c]
      | App (f,va) ->
	  let g,l = decomp f (Array.fold_right coc_cons va []) in
	  begin
	    match kind_of_term g with
	      | Const kn -> make_term (Sconstr g) l
	      | _ -> make_term Sapp ((coc g)::l)
	  end
      | Case (_,p,c,va) ->
	  make_term Scase (Array.fold_right coc_cons va [coc p; coc c])
      | Fix (i,(_,va1,va2)) ->
	  let l = Array.fold_right coc_cons va1 [] in
	    make_term (Sfix i) (Array.fold_right coc_cons va2 l)
      | CoFix (i,(_,va1,va2)) ->
	  let l = Array.fold_right coc_cons va1 [] in
	    make_term (Scofix i) (Array.fold_right coc_cons va2 l)
      | _ -> make_term (Sconstr c) []
  and coc_cons c l = (coc c)::l
  and decomp c l =
    match kind_of_term c with
      | App (f,va) -> decomp f (Array.fold_right coc_cons va l) 
      | _ -> c,l
  in coc

(* check whether two terms are equivalent modulo C/AC symbols *)
let are_equiv env t u =
  let s = sign env in
  let t' = cime_of_eq_constr s t and u' = cime_of_eq_constr s u in
    (* compare_t t' u' = 0 *)
    equals s t' u'
