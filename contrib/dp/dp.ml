(* Author : Nicolas Ayache and Jean-Christophe Filliatre *)
(* Goal : Tactics to call decision procedures *)


open Util
open Pp
open Term
open Tacmach
open Fol
open Names
open Nameops
open Coqlib

let logic_dir = ["Coq";"Logic";"Decidable"]
let coq_modules =
  init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules
    @ [["Coq"; "omega"; "OmegaLemmas"]]

let constant = gen_constant_in_modules "Omega" coq_modules

let coq_Z = lazy (constant "Z")

(* not Prop typed expressions *)
exception NotProp

(* not first-order expressions *)
exception NotFO

(* assumption: t:Set *)
let tr_type env t =
  if t = Lazy.force coq_Z then Base "INT"
  else raise NotFO

(* assumption: t:T:Set *)
let tr_term env t =
  match kind_of_term t with
    | Var id -> Tvar (string_of_id id)
    | _ -> raise NotFO

(* assumption: f is of type Prop *)
let tr_formula env f =
  let c, args = decompose_app f in
  match kind_of_term c, args with
    | _, [t;a;b] when c = build_coq_eq () -> 
	(* TODO: verifier type t *)
	Fatom (Eq (tr_term env a, tr_term env b))
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


(* Checks if a Coq formula is first-ordered *) 
let rec is_FO c = match kind_of_term c with
    Prod(n, t1, t2) -> assert false (*TODO*)
  | Lambda(n, t, c) ->assert false (*TODO*)
  | _ -> false

(* Translates a first-order Coq formula into a specific first-order
 language formula *)
(* let rec to_FO f = *)

let rec isGoodType gl t = 
(is_Prop t) || (is_Set t) || (is_Prop (pf_type_of gl (body_of_type t))) || (is_Set (pf_type_of gl (body_of_type t)))


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

(*** UTILISER prterm
let rec type_to_string t = match kind_of_term t with
    Sort (Prop Null) -> "Prop "
  | Sort (Prop Pos) -> "Set "
  | Sort (Type _) -> "Type "
  | Cast (c,_) -> type_to_string c
  | _ -> "Other"

let rec hyps_types_to_string = function
    [] -> ""
  | e::l -> (type_to_string e) ^ (hyps_types_to_string l)
***)

type prover = Simplify | CVCLite | Harvey

let call_prover prover q = match prover with
  | Simplify -> Dp_simplify.call q
  | CVCLite -> error "CVC Lite not yet interfaced"
  | Harvey -> error "haRVey not yet interfaced"

let admit_as_an_axiom gl =
  msgnl (str "Valid!");
  Tacticals.tclIDTAC gl
  
let dp prover gl =
  let concl_type = pf_type_of gl (pf_concl gl) in
  if not (is_Prop concl_type) then error "Goal is not a Prop";
  try 
    let q = tr_goal gl in
    begin match call_prover prover q with
      | Valid -> admit_as_an_axiom gl
      | Invalid -> error "Invalid"
      | DontKnow -> error "Don't know"
      | Timeout -> error "Timeout"
    end
  with NotFO ->
    error "Not a first order goal"
  

let simplify = dp Simplify
let cvc_lite = dp CVCLite
let harvey = dp Harvey
