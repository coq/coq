(* Author : Nicolas Ayache and Jean-Christophe Filliatre *)
(* Goal : Tactics to call decision procedures *)


open Util
open Pp
open Term
open Tacmach
open Fol
open Names
open Nameops
open Termops
open Coqlib
open Hipattern

let logic_dir = ["Coq";"Logic";"Decidable"]
let coq_modules =
  init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules
    @ [["Coq"; "omega"; "OmegaLemmas"]]

let constant = gen_constant_in_modules "Omega" coq_modules

let coq_Z = lazy (constant "Z")
let coq_Zplus = lazy (constant "Zplus")
let coq_Zmult = lazy (constant "Zmult")
let coq_Zopp = lazy (constant "Zopp")
let coq_Zminus = lazy (constant "Zminus")
let coq_Zdiv = lazy (constant "Zdiv")
let coq_Zs = lazy (constant "Zs")
let coq_Zgt = lazy (constant "Zgt")
let coq_Zle = lazy (constant "Zle")
let coq_Zge = lazy (constant "Zge")
let coq_Zlt = lazy (constant "Zlt")

(* not Prop typed expressions *)
exception NotProp

(* not first-order expressions *)
exception NotFO

(* assumption: t:Set *)
let rec tr_type env t =
  if t = Lazy.force coq_Z then Base "INT"
  else if is_Prop t then Base "BOOLEAN"
  else if is_Set t then Base "TYPE"
  else if is_imp_term t then 
    begin match match_with_imp_term t with
      | Some (t1, t2) -> Arrow (tr_type env t1, tr_type env t2)
      | _ -> assert false
    end
  (* else if then *)
  else raise NotFO

(* assumption: t:T:Set *)
let rec tr_term env t =
  match kind_of_term t with
    | Var id -> 
	Tvar (string_of_id id)
    | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zplus -> 
	Plus (tr_term env a, tr_term env b)
    | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zminus -> 
	Moins (tr_term env a, tr_term env b)
    | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zmult -> 
	Mult (tr_term env a, tr_term env b)
    | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zdiv -> 
	Div (tr_term env a, tr_term env b)
    | Term.App (f, cl) -> 
	begin try
	  let r = Libnames.reference_of_constr f in
	  let s = string_of_id (Nametab.id_of_global r) in
	  App (s, List.map (tr_term env) (Array.to_list cl))
	with Not_found ->
	  raise NotFO
	end
    | _ -> 
	raise NotFO

(* assumption: f is of type Prop *)
let rec tr_formula env f =
  let c, args = decompose_app f in
  match kind_of_term c, args with
    | Var id, [] -> 
	Fvar (string_of_id id)
    | _, [t;a;b] when c = build_coq_eq () -> 
	(* TODO: verifier type t *)
	Fatom (Eq (tr_term env a, tr_term env b))
    | _, [a;b] when c = Lazy.force coq_Zle ->
	Fatom (Le (tr_term env a, tr_term env b))
    | _, [] when c = build_coq_False () ->
	False
    | _, [] when c = build_coq_True () ->
	True
    | _, [a] when c = build_coq_not () ->
	Not (tr_formula env a)
    | _, [a;b] when c = build_coq_and () ->
	And (tr_formula env a, tr_formula env b)
    | _, [a;b] when c = build_coq_or () ->
	Or (tr_formula env a, tr_formula env b)
    | Prod (_, a, b), _ ->
	if is_imp_term f then
	  Imp (tr_formula env a, tr_formula env b)
	else
	  assert false (*TODO Forall *)
    | _, [a] when c = build_coq_ex () ->
	assert false (*TODO*) (*Exists (tr_formula env a)*)
    | _ ->
	raise NotFO


let tr_goal gl =
  let tr_one_hyp (id, ty) =
    let id = string_of_id id in
    if is_Prop ty then
      DeclProp id
    else if is_Set ty then
      DeclType id
    else 
      let s = pf_type_of gl ty in
      if is_Prop s then
	Assert (id, tr_formula (pf_env gl) ty)
      else if is_Set s then
	DeclVar (id, tr_type (pf_env gl) ty)
      else
	raise NotFO
  in
  let c = tr_formula (pf_env gl) (pf_concl gl) in
  let hyps =
    List.fold_left 
      (fun acc h -> try tr_one_hyp h :: acc with NotFO -> acc)
      [] (pf_hyps_types gl)
  in
  hyps, c


let rec isGoodType gl t = 
  (is_Prop t) || 
  (is_Set t) || 
  (is_Prop (pf_type_of gl (body_of_type t))) || 
  (is_Set (pf_type_of gl (body_of_type t)))


let rec allGoodTypeHyps gl hyps_types = match hyps_types with
  | [] -> 
      Tacticals.tclIDTAC gl
  | (id, t)::l' -> 
      if not (isGoodType gl t) then 
	errorlabstrm "allGoodTypeHyps"
	  (pr_id id ++ str " must be Prop, Set or " ++ pr_id id ++ 
	   str "'s type must be Prop or Set");
      allGoodTypeHyps gl l'

let allGoodType gl =
  let concl_type = pf_type_of gl (pf_concl gl) in
  if not (is_Prop concl_type) then error "Goal is not a Prop";
  let hyps_types = pf_hyps_types gl in 
  allGoodTypeHyps gl hyps_types


type prover = Simplify | CVCLite | Harvey

let call_prover prover q = match prover with
  | Simplify -> Dp_simplify.call q
  | CVCLite -> error "CVC Lite not yet interfaced"
  | Harvey -> error "haRVey not yet interfaced"
  
let dp prover gl =
  let concl_type = pf_type_of gl (pf_concl gl) in
  if not (is_Prop concl_type) then error "Goal is not a Prop";
  try 
    let q = tr_goal gl in
    begin match call_prover prover q with
      | Valid -> Tactics.admit_as_an_axiom gl
      | Invalid -> error "Invalid"
      | DontKnow -> error "Don't know"
      | Timeout -> error "Timeout"
    end
  with NotFO ->
    error "Not a first order goal"
  

let simplify = dp Simplify
let cvc_lite = dp CVCLite
let harvey = dp Harvey
