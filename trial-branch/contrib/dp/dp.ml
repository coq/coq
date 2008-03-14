(* Authors: Nicolas Ayache and Jean-Christophe Filliâtre *)
(* Tactics to call decision procedures *)

(* Works in two steps: 

   - first the Coq context and the current goal are translated in
     Polymorphic First-Order Logic (see fol.mli in this directory)

   - then the resulting query is passed to the Why tool that translates
     it to the syntax of the selected prover (Simplify, CVC Lite, haRVey,
     Zenon)
*)

open Util
open Pp
open Term
open Tacmach
open Tactics
open Tacticals
open Fol
open Names
open Nameops
open Termops
open Coqlib
open Hipattern
open Libnames
open Declarations
open Dp_why

let debug = ref false
let set_debug b = debug := b
let trace = ref false
let set_trace b = trace := b
let timeout = ref 10
let set_timeout n = timeout := n

let logic_dir = ["Coq";"Logic";"Decidable"]
let coq_modules =
  init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules
    @ [["Coq"; "omega"; "OmegaLemmas"]]

let constant = gen_constant_in_modules "dp" coq_modules

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
let coq_iff = lazy (constant "iff")

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
  List.fold_right 
    (fun (x,t) p -> Forall (x, t, p))

let fresh_var = function
  | Anonymous -> rename_global (VarRef (id_of_string "x"))
  | Name x -> rename_global (VarRef x)

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

(* extract the prenex type quantifications i.e.
   type_quantifiers env (A1:Set)...(Ak:Set)t = A1...An, (env+Ai), t *)
let decomp_type_quantifiers env t =
  let rec loop vars t = match kind_of_term t with
    | Prod (n, a, t) when is_Set a -> 
	loop ((n,a) :: vars) t
    | _ -> 
	let vars, env = coq_rename_vars env vars in
	let t = substl (List.map mkVar vars) t in
	List.rev vars, env, t
  in
  loop [] t

(* same thing with lambda binders (for axiomatize body) *)
let decomp_type_lambdas env t =
  let rec loop vars t = match kind_of_term t with
    | Lambda (n, a, t) when is_Set a -> 
	loop ((n,a) :: vars) t
    | _ -> 
	let vars, env = coq_rename_vars env vars in
	let t = substl (List.map mkVar vars) t in
	List.rev vars, env, t
  in
  loop [] t

let decompose_arrows = 
  let rec arrows_rec l c = match kind_of_term c with
    | Prod (_,t,c) when not (dependent (mkRel 1) c) -> arrows_rec (t :: l) c
    | Cast (c,_,_) -> arrows_rec l c
    | _ -> List.rev l, c
  in 
  arrows_rec []

let rec eta_expanse t vars env i =
  assert (i >= 0);
  if i = 0 then
    t, vars, env
  else
    match kind_of_term (Typing.type_of env Evd.empty t) with
      | Prod (n, a, b) when not (dependent (mkRel 1) b) ->
	  let avoid = ids_of_named_context (Environ.named_context env) in
	  let id = next_name_away n avoid in
	  let env' = Environ.push_named (id, None, a) env in
	  let t' = mkApp (t, [| mkVar id |]) in
	  eta_expanse t' (id :: vars) env' (pred i)
      | _ -> 
	  assert false

let rec skip_k_args k cl = match k, cl with
  | 0, _ -> cl
  | _, _ :: cl -> skip_k_args (k-1) cl
  | _, [] -> raise NotFO

(* Coq global references *)

type global = Gnot_fo | Gfo of Fol.decl

let globals = ref Refmap.empty
let globals_stack = ref []

(* synchronization *)
let () =
  Summary.declare_summary "Dp globals"
    { Summary.freeze_function = (fun () -> !globals, !globals_stack);
      Summary.unfreeze_function = 
	(fun (g,s) -> globals := g; globals_stack := s);
      Summary.init_function = (fun () -> ());
      Summary.survive_module = false;
      Summary.survive_section = false }

let add_global r d = globals := Refmap.add r d !globals
let mem_global r = Refmap.mem r !globals
let lookup_global r = match Refmap.find r !globals with
  | Gnot_fo -> raise NotFO
  | Gfo d -> d

let locals = Hashtbl.create 97

let lookup_local r =  match Hashtbl.find locals r with
  | Gnot_fo -> raise NotFO
  | Gfo d -> d

let iter_all_constructors i f =  
  let _, oib = Global.lookup_inductive i in
  Array.iteri
    (fun j tj -> f j (mkConstruct (i, j+1)))
    oib.mind_nf_lc


(* injection c [t1,...,tn] adds the injection axiom
     forall x1:t1,...,xn:tn,y1:t1,...,yn:tn. 
       c(x1,...,xn)=c(y1,...,yn) -> x1=y1 /\ ... /\ xn=yn *)

let injection c l =
  let i = ref 0 in
  let var s = incr i; id_of_string (s ^ string_of_int !i) in
  let xl = List.map (fun t -> rename_global (VarRef (var "x")), t) l in
  i := 0;
  let yl = List.map (fun t -> rename_global (VarRef (var "y")), t) l in
  let f = 
    List.fold_right2 
      (fun (x,_) (y,_) p -> And (Fatom (Eq (App (x,[]),App (y,[]))), p))
      xl yl True
  in
  let vars = List.map (fun (x,_) -> App(x,[])) in
  let f = Imp (Fatom (Eq (App (c, vars xl), App (c, vars yl))), f) in
  let foralls = List.fold_right (fun (x,t) p -> Forall (x, t, p)) in
  let f = foralls xl (foralls yl f) in
  let ax = Axiom ("injection_" ^ c, f) in
  globals_stack := ax :: !globals_stack

(* rec_names_for c [|n1;...;nk|] builds the list of constant names for 
   identifiers n1...nk with the same path as c, if they exist; otherwise
   raises Not_found *)
let rec_names_for c =
  let mp,dp,_ = Names.repr_con c in
  array_map_to_list
    (function 
       | Name id -> 
	   let c' = Names.make_con mp dp (label_of_id id) in
	   ignore (Global.lookup_constant c');
	   msgnl (Printer.pr_constr (mkConst c'));
	   c'
       | Anonymous ->
	   raise Not_found)

(* abstraction tables *)

let term_abstractions = Hashtbl.create 97

let new_abstraction = 
  let r = ref 0 in fun () -> incr r; "abstraction_" ^ string_of_int !r

(* Arithmetic constants *)

exception NotArithConstant

(* translates a closed Coq term p:positive into a FOL term of type int *)
let rec tr_positive p = match kind_of_term p with
  | Term.Construct _ when p = Lazy.force coq_xH ->
      Cst 1
  | Term.App (f, [|a|]) when f = Lazy.force coq_xI ->
      Plus (Mult (Cst 2, tr_positive a), Cst 1)
  | Term.App (f, [|a|]) when f = Lazy.force coq_xO ->
      Mult (Cst 2, tr_positive a)
  | Term.Cast (p, _, _) ->
      tr_positive p
  | _ ->
      raise NotArithConstant

(* translates a closed Coq term t:Z into a FOL term of type int *)
let rec tr_arith_constant t = match kind_of_term t with
  | Term.Construct _ when t = Lazy.force coq_Z0 ->
      Cst 0
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos ->
      tr_positive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg ->
      Moins (Cst 0, tr_positive a)
  | Term.Cast (t, _, _) ->
      tr_arith_constant t
  | _ -> 
      raise NotArithConstant

(* translate a Coq term t:Set into a FOL type expression;
   tv = list of type variables *)
and tr_type tv env t =
  let t = Reductionops.nf_betadeltaiota env Evd.empty t in
  if t = Lazy.force coq_Z then 
    Tid ("int", [])
  else match kind_of_term t with
    | Var x when List.mem x tv ->
	Tvar (string_of_id x)
    | _ ->
	let f, cl = decompose_app t in
	begin try
	  let r = global_of_constr f in
	  match tr_global env r with
	    | DeclType (id, k) -> 
		assert (k = List.length cl); (* since t:Set *)
		Tid (id, List.map (tr_type tv env) cl)
	    | _ -> 
		raise NotFO
	with 
	  | Not_found ->
	      raise NotFO
	  | NotFO -> 
	      (* we need to abstract some part of (f cl) *)
	      (*TODO*)
	      raise NotFO
	end

and make_term_abstraction tv env c =
  let ty = Typing.type_of env Evd.empty c in
  let id = new_abstraction () in
  match tr_decl env id ty with
    | DeclFun (id,_,_,_) as d ->
	begin try
	  Hashtbl.find term_abstractions c
	with Not_found ->
	  Hashtbl.add term_abstractions c id;
	  globals_stack := d :: !globals_stack;
	  id
	end
    | _ ->
	raise NotFO

(* translate a Coq declaration id:ty in a FOL declaration, that is either
   - a type declaration : DeclType (id, n) where n:int is the type arity
   - a function declaration : DeclFun (id, tl, t) ; that includes constants
   - a predicate declaration : DeclPred (id, tl)
   - an axiom : Axiom (id, p)
 *)
and tr_decl env id ty =
  let tv, env, t = decomp_type_quantifiers env ty in
  if is_Set t then
    DeclType (id, List.length tv)
  else if is_Prop t then
    DeclPred (id, List.length tv, [])
  else 
    let s = Typing.type_of env Evd.empty t in
    if is_Prop s then
      Axiom (id, tr_formula tv [] env t)
    else
      let l, t = decompose_arrows t in
      let l = List.map (tr_type tv env) l in
      if is_Prop t then
	DeclPred(id, List.length tv, l)
      else 
	let s = Typing.type_of env Evd.empty t in
	if is_Set s then 
	  DeclFun(id, List.length tv, l, tr_type tv env t)
	else 
	  raise NotFO

(* tr_global(r) = tr_decl(id(r),typeof(r)) + a cache mechanism *)
and tr_global env r = match r with
  | VarRef id ->
      lookup_local id
  | r ->
      try
	lookup_global r
      with Not_found ->
	try
	  let ty = Global.type_of_global r in
	  let id = rename_global r in
	  let d = tr_decl env id ty in
	  (* r can be already declared if it is a constructor *)
	  if not (mem_global r) then begin 
	    add_global r (Gfo d);
	    globals_stack := d :: !globals_stack
	  end;
	  begin try axiomatize_body env r id d with NotFO -> () end;
	  d
	with NotFO ->
	  add_global r Gnot_fo;
	  raise NotFO

and axiomatize_body env r id d = match r with
  | VarRef _ -> 
      assert false
  | ConstRef c ->
      begin match (Global.lookup_constant c).const_body with
	| Some b ->
	    let b = force b in
	    let tv, env, b = decomp_type_lambdas env b in
	    let axioms =
	      (match d with
		 | DeclPred (id, _, []) ->
		     let value = tr_formula tv [] env b in
		     [id, Iff (Fatom (Pred (id, [])), value)]
		 | DeclFun (id, _, [], _) ->
		     let value = tr_term tv [] env b in
		     [id, Fatom (Eq (Fol.App (id, []), value))]
		 | DeclFun (id, _, l, _) | DeclPred (id, _, l) ->
		     (*Format.eprintf "axiomatize_body %S@." id;*)
		     let b = match kind_of_term b with
		       (* a single recursive function *)
		       | Fix (_, (_,_,[|b|])) -> 
			   subst1 (mkConst c) b
                       (* mutually recursive functions *)
		       | Fix ((_,i), (names,_,bodies)) ->
                           (* we only deal with named functions *)
			   begin try
			     let l = rec_names_for c names in
			     substl (List.rev_map mkConst l) bodies.(i)
			   with Not_found ->
			     b
			   end
		       | _ -> 
			   b
		     in
		     let vars, t = decompose_lam b in
		     let n = List.length l in
		     let k = List.length vars in
		     assert (k <= n);
		     let vars, env = coq_rename_vars env vars in
		     let t = substl (List.map mkVar vars) t in
		     let t, vars, env = eta_expanse t vars env (n-k) in
		     let vars = List.rev vars in
		     let bv = vars in
		     let vars = List.map (fun x -> string_of_id x) vars in
		     let fol_var x = Fol.App (x, []) in
		     let fol_vars = List.map fol_var vars in
		     let vars = List.combine vars l in
		     begin match d with
		       | DeclFun (_, _, _, ty) ->
			   begin match kind_of_term t with
			     | Case (ci, _, e, br) ->
				 equations_for_case env id vars tv bv ci e br
			     | _ -> 
				 let t = tr_term tv bv env t in
				 let ax = 
				   add_proof (Fun_def (id, vars, ty, t))
				 in
				 let p = Fatom (Eq (App (id, fol_vars), t)) in
				 [ax, foralls vars p]
			   end
		       | DeclPred _ ->
			   let value = tr_formula tv bv env t in
			   let p = Iff (Fatom (Pred (id, fol_vars)), value) in
			   [id, foralls vars p]
		       | _ ->
			   assert false
		     end
		 | DeclType _ ->
		     raise NotFO
		 | Axiom _ -> assert false)
	    in
	    let axioms = List.map (fun (id,ax) -> Axiom (id, ax)) axioms in
	    globals_stack := axioms @ !globals_stack
	| None -> 
	    () (* Coq axiom *)
      end
  | IndRef i ->
      iter_all_constructors i
	(fun _ c ->
	   let rc = global_of_constr c in
	   try
	     begin match tr_global env rc with
	       | DeclFun (_, _, [], _) -> ()
	       | DeclFun (idc, _, al, _) -> injection idc al
	       | _ -> ()
	     end
	   with NotFO ->
	     ())
  | _ -> ()

and equations_for_case env id vars tv bv ci e br = match kind_of_term e with
  | Var x when List.exists (fun (y, _) -> string_of_id x = y) vars ->
      let eqs = ref [] in
      iter_all_constructors ci.ci_ind
	(fun j cj ->
	   try
	     let cjr = global_of_constr cj in
	     begin match tr_global env cjr with
	       | DeclFun (idc, _, l, _) ->
		   let b = br.(j) in
		   let rec_vars, b = decompose_lam b in
		   let rec_vars, env = coq_rename_vars env rec_vars in
		   let coq_rec_vars = List.map mkVar rec_vars in
		   let b = substl coq_rec_vars b in
		   let rec_vars = List.rev rec_vars in
		   let coq_rec_term = applist (cj, List.rev coq_rec_vars) in
		   let b = replace_vars [x, coq_rec_term] b in
		   let bv = bv @ rec_vars in
		   let rec_vars = List.map string_of_id rec_vars in
		   let fol_var x = Fol.App (x, []) in
		   let fol_rec_vars = List.map fol_var rec_vars in
		   let fol_rec_term = App (idc, fol_rec_vars) in
		   let rec_vars = List.combine rec_vars l in
		   let fol_vars = List.map fst vars in
		   let fol_vars = List.map fol_var fol_vars in
		   let fol_vars = List.map (fun y -> match y with
					      | App (id, _) ->
						  if id = string_of_id x
						  then fol_rec_term
						  else y
					      | _ -> y)
				    fol_vars in
		   let vars = vars @ rec_vars in
		   let rec remove l e = match l with
		     | [] -> []
		     | (y, t)::l' -> if y = string_of_id e then l'
		       else (y, t)::(remove l' e) in
		   let vars = remove vars x in
		   let p = 
		     Fatom (Eq (App (id, fol_vars), 
				tr_term tv bv env b))
		   in
		   eqs := (id ^ "_" ^ idc, foralls vars p) :: !eqs
	       | _ -> 
		   assert false end
	   with NotFO ->
	     ());
      !eqs
  | _ ->
      raise NotFO

(* assumption: t:T:Set *)
and tr_term tv bv env t = match kind_of_term t with
  | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zplus -> 
      Plus (tr_term tv bv env a, tr_term tv bv env b)
  | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zminus -> 
      Moins (tr_term tv bv env a, tr_term tv bv env b)
  | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zmult -> 
      Mult (tr_term tv bv env a, tr_term tv bv env b)
  | Term.App (f, [|a;b|]) when f = Lazy.force coq_Zdiv -> 
      Div (tr_term tv bv env a, tr_term tv bv env b)
  | Term.Var id when List.mem id bv ->
      App (string_of_id id, [])
  | _ ->
      try
	tr_arith_constant t
      with NotArithConstant ->
	let f, cl = decompose_app t in
	begin try
	  let r = global_of_constr f in
	  match tr_global env r with
	    | DeclFun (s, k, _, _) -> 
		let cl = skip_k_args k cl in
		Fol.App (s, List.map (tr_term tv bv env) cl)
	    | _ -> 
		raise NotFO
	with 
	  | Not_found ->
	      raise NotFO
	  | NotFO -> (* we need to abstract some part of (f cl) *)
	      let rec abstract app = function
		| [] ->
		    Fol.App (make_term_abstraction tv env app, [])
		| x :: l as args ->
		    begin try
		      let s = make_term_abstraction tv env app in
		      Fol.App (s, List.map (tr_term tv bv env) args)
		    with NotFO ->
		      abstract (applist (app, [x])) l
		    end
	      in
	      let app,l = match cl with 
		| x :: l -> applist (f, [x]), l | [] -> raise NotFO
	      in
	      abstract app l
	end

and quantifiers n a b tv bv env =
  let vars, env = coq_rename_vars env [n,a] in
  let id = match vars with [x] -> x | _ -> assert false in
  let b = subst1 (mkVar id) b in
  let t = tr_type tv env a in
  let bv = id :: bv in
  id, t, bv, env, b

(* assumption: f is of type Prop *)
and tr_formula tv bv env f =
  let c, args = decompose_app f in
  match kind_of_term c, args with
    | Var id, [] -> 
	Fatom (Pred (rename_global (VarRef id), []))
    | _, [t;a;b] when c = build_coq_eq () ->
	let ty = Typing.type_of env Evd.empty t in
	if is_Set ty then
	  let _ = tr_type tv env t in
	  Fatom (Eq (tr_term tv bv env a, tr_term tv bv env b))
	else 
	  raise NotFO
    | _, [a;b] when c = Lazy.force coq_Zle ->
	Fatom (Le (tr_term tv bv env a, tr_term tv bv env b))
    | _, [a;b] when c = Lazy.force coq_Zlt ->
	Fatom (Lt (tr_term tv bv env a, tr_term tv bv env b))
    | _, [a;b] when c = Lazy.force coq_Zge ->
	Fatom (Ge (tr_term tv bv env a, tr_term tv bv env b))
    | _, [a;b] when c = Lazy.force coq_Zgt ->
	Fatom (Gt (tr_term tv bv env a, tr_term tv bv env b))
    | _, [] when c = build_coq_False () ->
	False
    | _, [] when c = build_coq_True () ->
	True
    | _, [a] when c = build_coq_not () ->
	Not (tr_formula tv bv env a)
    | _, [a;b] when c = build_coq_and () ->
	And (tr_formula tv bv env a, tr_formula tv bv env b)
    | _, [a;b] when c = build_coq_or () ->
	Or (tr_formula tv bv env a, tr_formula tv bv env b)
    | _, [a;b] when c = Lazy.force coq_iff ->
	Iff (tr_formula tv bv env a, tr_formula tv bv env b)
    | Prod (n, a, b), _ ->
	if is_imp_term f then
	  Imp (tr_formula tv bv env a, tr_formula tv bv env b)
	else
	  let id, t, bv, env, b = quantifiers n a b tv bv env in
	  Forall (string_of_id id, t, tr_formula tv bv env b)
    | _, [_; a] when c = build_coq_ex () ->
	begin match kind_of_term a with
	  | Lambda(n, a, b) ->
	      let id, t, bv, env, b = quantifiers n a b tv bv env in
	      Exists (string_of_id id, t, tr_formula tv bv env b)
	  | _ -> 
	      (* unusual case of the shape (ex p) *)
	      raise NotFO (* TODO: we could eta-expanse *)
	end
    | _ ->
	begin try
	  let r = global_of_constr c in
	  match tr_global env r with
	    | DeclPred (s, k, _) -> 
		let args = skip_k_args k args in
		Fatom (Pred (s, List.map (tr_term tv bv env) args))
	    | _ -> 
		raise NotFO
	with Not_found ->
	  raise NotFO
	end


let tr_goal gl =
  Hashtbl.clear locals;
  let tr_one_hyp (id, ty) = 
    try
      let s = rename_global (VarRef id) in
      let d = tr_decl (pf_env gl) s ty in
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
  let c = tr_formula [] [] (pf_env gl) (pf_concl gl) in
  let hyps = List.rev_append !globals_stack (List.rev hyps) in
  hyps, c


type prover = Simplify | Ergo | Yices | CVCLite | Harvey | Zenon | Gwhy

let remove_files = List.iter (fun f -> try Sys.remove f with _ -> ())

let sprintf = Format.sprintf

let call_simplify fwhy =
  let cmd = sprintf "why --no-arrays --simplify --encoding sstrat %s" fwhy in
  if Sys.command cmd <> 0 then error ("call to " ^ cmd ^ " failed");
  let fsx = Filename.chop_suffix fwhy ".why" ^ "_why.sx" in
  let cmd = 
    sprintf "timeout %d Simplify %s > out 2>&1 && grep -q -w Valid out" 
      !timeout fsx
  in
  let out = Sys.command cmd in
  let r = 
    if out = 0 then Valid None else if out = 1 then Invalid else Timeout 
  in
  if not !debug then remove_files [fwhy; fsx];
  r

let call_ergo fwhy =
  let ftrace = Filename.temp_file "ergo_trace" "" in
  let cmd = 
    if !trace then
      sprintf 
	"timeout %d ergo -cctrace %s %s > out 2>&1 && grep -q -w Valid out"  
	!timeout ftrace fwhy
    else
      sprintf "timeout %d ergo %s > out 2>&1 && grep -q -w Valid out" 
	!timeout fwhy
  in
  let out = Sys.command cmd in
  let r = 
    if out = 0 then Valid (if !trace then Some ftrace else None)
    else if out = 1 then Invalid else Timeout 
  in
  if not !debug then remove_files [fwhy];
  r

let call_zenon fwhy =
  let cmd = sprintf "why --no-prelude --no-zenon-prelude --zenon %s" fwhy in
  if Sys.command cmd <> 0 then error ("call to " ^ cmd ^ " failed");
  let fznn = Filename.chop_suffix fwhy ".why" ^ "_why.znn" in
  let out = Filename.temp_file "dp_out" "" in
  let cmd = 
    sprintf "timeout %d zenon -ocoqterm %s > %s 2>&1" !timeout fznn out 
  in
  let c = Sys.command cmd in
  if not !debug then remove_files [fwhy; fznn];
  if c = 137 then 
    Timeout
  else begin
    if c <> 0 then anomaly ("command failed: " ^ cmd);
    if Sys.command (sprintf "grep -q -w Error %s" out) = 0 then
      error "Zenon failed";
    let c = Sys.command (sprintf "grep -q PROOF-FOUND %s" out) in
    if c = 0 then Valid (Some out) else Invalid
  end

let call_yices fwhy =
  let cmd = sprintf "why --no-arrays -smtlib --encoding sstrat %s" fwhy in
  if Sys.command cmd <> 0 then error ("call to " ^ cmd ^ " failed");
  let fsmt = Filename.chop_suffix fwhy ".why" ^ "_why.smt" in
  let cmd = 
    sprintf "timeout %d yices -pc 0 -smt < %s > out 2>&1 && grep -q -w unsat out" 
      !timeout fsmt
  in
  let out = Sys.command cmd in
  let r = 
    if out = 0 then Valid None else if out = 1 then Invalid else Timeout 
  in
  if not !debug then remove_files [fwhy; fsmt];
  r

let call_cvcl fwhy =
  let cmd = sprintf "why --no-arrays --cvcl --encoding sstrat %s" fwhy in
  if Sys.command cmd <> 0 then error ("call to " ^ cmd ^ " failed");
  let fcvc = Filename.chop_suffix fwhy ".why" ^ "_why.cvc" in
  let cmd = 
    sprintf "timeout %d cvcl < %s > out 2>&1 && grep -q -w Valid out" 
      !timeout fcvc
  in
  let out = Sys.command cmd in
  let r = 
    if out = 0 then Valid None else if out = 1 then Invalid else Timeout 
  in
  if not !debug then remove_files [fwhy; fcvc];
  r

let call_harvey fwhy =
  let cmd = sprintf "why --no-arrays --harvey --encoding strat %s" fwhy in
  if Sys.command cmd <> 0 then error ("call to " ^ cmd ^ " failed");
  let frv = Filename.chop_suffix fwhy ".why" ^ "_why.rv" in
  let out = Sys.command (sprintf "rvc -e -t %s > /dev/null 2>&1" frv) in
  if out <> 0 then anomaly ("call to rvc -e -t " ^ frv ^ " failed");
  let f = Filename.chop_suffix frv ".rv" ^ "-0.baf" in
  let outf = Filename.temp_file "rv" ".out" in
  let out = 
    Sys.command (sprintf "timeout %d rv -e\"-T 2000\" %s > %s 2>&1" 
		   !timeout f outf) 
  in
  let r =
    if out <> 0 then 
      Timeout
    else
      let cmd = 
	sprintf "grep \"Proof obligation in\" %s | grep -q \"is valid\"" outf
      in
      if Sys.command cmd = 0 then Valid None else Invalid
  in
  if not !debug then remove_files [fwhy; frv; outf];
  r

let call_gwhy fwhy =
  let cmd = sprintf "gwhy --no-arrays  %s" fwhy in
  if Sys.command cmd <> 0 then ignore (Sys.command (sprintf "emacs %s" fwhy));
  NoAnswer

let ergo_proof_from_file f gl =
  let s =
    let buf = Buffer.create 1024 in
    let c = open_in f in
    try
      while true do Buffer.add_string buf (input_line c) done; assert false
    with End_of_file ->
      close_in c;
      Buffer.contents buf
  in
  let parsed_constr = Pcoq.parse_string Pcoq.Constr.constr s in
  let t = Constrintern.interp_constr (project gl) (pf_env gl) parsed_constr in
  exact_check t gl

let call_prover prover q =
  let fwhy = Filename.temp_file "coq_dp" ".why" in
  Dp_why.output_file fwhy q;
  if !debug then Format.eprintf "Why file: %s@." fwhy;
  match prover with
    | Simplify -> call_simplify fwhy
    | Ergo -> call_ergo fwhy
    | Yices -> call_yices fwhy
    | Zenon -> call_zenon fwhy
    | CVCLite -> call_cvcl fwhy
    | Harvey -> call_harvey fwhy
    | Gwhy -> call_gwhy fwhy
  
let dp prover gl =
  let concl_type = pf_type_of gl (pf_concl gl) in
  if not (is_Prop concl_type) then error "Conclusion is not a Prop";
  try 
    let q = tr_goal gl in
    begin match call_prover prover q with
      | Valid (Some f) when prover = Zenon -> Dp_zenon.proof_from_file f gl
      | Valid (Some f) when prover = Ergo -> ergo_proof_from_file f gl
      | Valid _ -> Tactics.admit_as_an_axiom gl
      | Invalid -> error "Invalid"
      | DontKnow -> error "Don't know"
      | Timeout -> error "Timeout"
      | NoAnswer -> Tacticals.tclIDTAC gl
    end
  with NotFO ->
    error "Not a first order goal"
  

let simplify = tclTHEN intros (dp Simplify)
let ergo = tclTHEN intros (dp Ergo)
let yices = tclTHEN intros (dp Yices)
let cvc_lite = tclTHEN intros (dp CVCLite)
let harvey = dp Harvey
let zenon = tclTHEN intros (dp Zenon)
let gwhy = tclTHEN intros (dp Gwhy)

let dp_hint l =
  let env = Global.env () in
  let one_hint (qid,r) = 
    if not (mem_global r) then begin
      let ty = Global.type_of_global r in
      let s = Typing.type_of env Evd.empty ty in
      if is_Prop s then
	try
	  let id = rename_global r in
	  let tv, env, ty = decomp_type_quantifiers env ty in
	  let d = Axiom (id, tr_formula tv [] env ty) in
	  add_global r (Gfo d);
	  globals_stack := d :: !globals_stack
	with NotFO ->
	  add_global r Gnot_fo;
	  msg_warning
	    (pr_reference qid ++ 
	     str " ignored (not a first order proposition)")
	else begin
	  add_global r Gnot_fo;
	  msg_warning
	    (pr_reference qid ++ str " ignored (not a proposition)")
	end
    end
  in
  List.iter one_hint (List.map (fun qid -> qid, Nametab.global qid) l)
