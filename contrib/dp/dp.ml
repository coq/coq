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
open Libnames
open Declarations

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
let coq_Z0 = lazy (constant "Z0")
let coq_Zpos = lazy (constant "Zpos")
let coq_Zneg = lazy (constant "Zneg")
let coq_xH = lazy (constant "xH")
let coq_xI = lazy (constant "xI")
let coq_xO = lazy (constant "xO")

(* not Prop typed expressions *)
exception NotProp

(* not first-order expressions *)
exception NotFO

(* Renaming of Coq globals *)

let global_names = Hashtbl.create 97
let used_names = Hashtbl.create 97

let rename_global r =
  try 
    Hashtbl.find global_names r
  with Not_found ->
    let rec loop id = 
      if Hashtbl.mem used_names id then 
	loop (lift_ident id)
      else begin 
	Hashtbl.add used_names id ();
	let s = string_of_id id in
	Hashtbl.add global_names r s; 
	s
      end
    in
    loop (Nametab.id_of_global r)

let foralls =
  List.fold_right (fun (x,t) p -> Forall (rename_global (VarRef x), t, p))

(* coq_rename_vars env [(x1,t1);...;(xn,tn)] renames the xi outside of 
   env names, and returns the new variables together with the new 
   environment *)
let coq_rename_vars env vars =
  let avoid = ref (ids_of_named_context (Environ.named_context env)) in
  List.fold_right
    (fun (na,t) (newvars, newenv) -> 
       let id = next_name_away na !avoid in
       avoid := id :: !avoid;
       id :: newvars, Environ.push_named (id, None, t) newenv)
    vars ([],env)

(* assumption: t:Set *)
let rec tr_type env ty =
  if ty = Lazy.force coq_Z then [], "INT"
  else if is_Prop ty then [], "BOOLEAN"
  else if is_Set ty then [], "TYPE"
  else if is_imp_term ty then 
    begin match match_with_imp_term ty with
      | Some (t1, t2) -> begin match tr_type env t1, tr_type env t2 with
	  | ([], t1'), (l2, t2') -> t1' :: l2, t2'
	  | _ -> raise NotFO
	end
      | _ -> assert false
    end
  else match kind_of_term ty with
    | Var id -> [], rename_global (VarRef id)
    | Ind i -> [], rename_global (IndRef i)
    | _ -> raise NotFO

(* assumption : p:Z *)
let rec fol_term_of_positive p =
  match kind_of_term p with
    | Term.Construct _ when p = Lazy.force coq_xH ->
	Cst 1
    | Term.App (f, [|a|]) when f = Lazy.force coq_xI ->
	Plus (Mult (Cst 2, (fol_term_of_positive a)), Cst 1)
    | Term.App (f, [|a|]) when f = Lazy.force coq_xO ->
	Mult (Cst 2, (fol_term_of_positive a))
    | Var id ->
	Tvar (rename_global (VarRef id))
    | _ -> 
	assert false

(* Coq global references *)

type global = Gnot_fo | Gfo of Fol.hyp

let globals = Hashtbl.create 97
let globals_stack = ref []
let locals = Hashtbl.create 97

let lookup t r =  match Hashtbl.find t r with
  | Gnot_fo -> raise NotFO
  | Gfo d -> d

let rec tr_global_type env id ty =
  if is_Prop ty then
    DeclPred (id, [])
  else if is_Set ty then
    DeclType id
  else 
    let s = Typing.type_of env Evd.empty ty in
    if is_Prop s then
      Assert (id, tr_formula env ty)
    else
      let l,t = tr_type env ty in 
      if is_Set s then DeclVar (id, l, t)
      else if t = "BOOLEAN" then
	DeclPred(id, l)
      else raise NotFO

and tr_global env r = match r with
  | Libnames.VarRef id ->
      lookup locals id
  | r ->
      try
	lookup globals r
      with Not_found ->
	try
	  let ty = Global.type_of_global r in
	  let id = rename_global r in
	  let d = tr_global_type env id ty in
	  Hashtbl.add globals r (Gfo d);
	  globals_stack := d :: !globals_stack;
	  begin try axiomatize_body env r id d with NotFO -> () end;
	  d
	with NotFO ->
	  Hashtbl.add globals r Gnot_fo;
	  raise NotFO

and axiomatize_body env r id d = match r with
  | Libnames.VarRef ident -> 
      assert false
  | Libnames.ConstRef c ->
      begin match (Global.lookup_constant c).const_body with
	| Some b -> 
	    let b = force b in
	    let id, ax = match d with
	      | DeclPred (id, []) ->
		  let value = tr_formula env b in
		  id, And (Imp (Fatom (Pred (id, [])), value),
			   Imp (value, Fatom (Pred (id, []))))
	      | DeclVar (id, [], _) ->
		  let value = tr_term env b in
		  id, Fatom (Eq (Tvar id, value)) 
	      | DeclVar (id, l, _) | DeclPred (id, l) ->
		  let vars,t = decompose_lam b in
		  let n = List.length l in
		  let k = List.length vars in
		  assert (k <= n);
		  if k < n then raise NotFO; (* TODO: eta-expanser *)
		  let vars,env = coq_rename_vars env vars in
		  let t = substl (List.map mkVar vars) t in
		  let vars = List.rev vars in
		  let fol_var x = Tvar (rename_global (VarRef x)) in
		  let fol_vars = List.map fol_var vars in
		  let vars = List.combine vars l in
		  let p = match d with
		    | DeclVar _ ->
			Fatom (Eq (App (id, fol_vars), tr_term env t))
		    | DeclPred _ ->
			let value = tr_formula env t in
			And (Imp (Fatom (Pred (id, fol_vars)), value),
			     Imp (value, Fatom (Pred (id, fol_vars))))
		    | _ ->
			assert false
		  in
		  id, foralls vars p
	      | _ ->
		  raise NotFO (* TODO *)
	    in
	    let ax = Assert (id, ax) in
	    globals_stack := ax :: !globals_stack
	| None -> 
	    () (* Coq axiom *)
      end
  | _ -> ()



(* assumption: t:T:Set *)
and tr_term env t =
  match kind_of_term t with
    | Var id -> 
	Tvar (rename_global (VarRef id))
    | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zplus -> 
	Plus (tr_term env a, tr_term env b)
    | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zminus -> 
	Moins (tr_term env a, tr_term env b)
    | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zmult -> 
	Mult (tr_term env a, tr_term env b)
    | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zdiv -> 
	Div (tr_term env a, tr_term env b)
    | Term.Construct _ when t = Lazy.force coq_Z0 ->
	Cst 0
    | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos ->
	fol_term_of_positive a
    | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg ->
	Moins (Cst 0, (fol_term_of_positive a))
    | _ ->
	let f, cl = decompose_app t in
	begin try
	  let r = Libnames.reference_of_constr f in
	  match tr_global env r with
	    | DeclVar (s, _, _) -> Fol.App (s, List.map (tr_term env) cl)
	    | _ -> raise NotFO
	with Not_found ->
	  raise NotFO
	end

(* assumption: f is of type Prop *)
and tr_formula env f =
  let c, args = decompose_app f in
  match kind_of_term c, args with
    | Var id, [] -> 
	Fatom (Pred (rename_global (VarRef id), []))
    | _, [t;a;b] when c = build_coq_eq () -> 
	(*let ty = pf_type_of gl t in
	if is_Set ty then*)
	  Fatom (Eq (tr_term env a, tr_term env b))
	(*else raise NotFO*)
    | _, [a;b] when c = Lazy.force coq_Zle ->
	Fatom (Le (tr_term env a, tr_term env b))
    | _, [a;b] when c = Lazy.force coq_Zlt ->
	Fatom (Lt (tr_term env a, tr_term env b))
    | _, [a;b] when c = Lazy.force coq_Zge ->
	Fatom (Ge (tr_term env a, tr_term env b))
    | _, [a;b] when c = Lazy.force coq_Zgt ->
	Fatom (Gt (tr_term env a, tr_term env b))
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
	  assert false (* TODO Forall *)	  
    | _, [a] when c = build_coq_ex () ->
	assert false (* TODO Exists (tr_formula env a) *)
    | _ ->
	begin try
	  let r = Libnames.reference_of_constr c in
	  match tr_global env r with
	    | DeclPred (s, _) -> Fatom (Pred (s, List.map (tr_term env) args))
	    | _ -> raise NotFO
	with Not_found ->
	  raise NotFO
	end


let tr_goal gl =
  Hashtbl.clear locals;
  let tr_one_hyp (id, ty) = 
    try
      let s = rename_global (VarRef id) in
      let d = tr_global_type (pf_env gl) s ty in
      Hashtbl.add locals id (Gfo d);
      d
    with NotFO ->
      Hashtbl.add locals id Gnot_fo;
      raise NotFO
  in
  let hyps =
    List.fold_right 
      (fun h acc -> try tr_one_hyp h :: acc with NotFO -> acc)
      (pf_hyps_types gl) []
  in
  let c = tr_formula (pf_env gl) (pf_concl gl) in
  let hyps = List.rev_append !globals_stack hyps in
  hyps, c


type prover = Simplify | CVCLite | Harvey

let call_prover prover q = match prover with
  | Simplify -> Dp_simplify.call q
  | CVCLite -> error "CVC Lite not yet interfaced"
  | Harvey -> error "haRVey not yet interfaced"
  
let dp prover gl =
  let concl_type = pf_type_of gl (pf_concl gl) in
  if not (is_Prop concl_type) then error "Conclusion is not a Prop";
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
