(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Tacmach
open Proof_type
open Libobject
open Reductionops
open Term
open Termops
open Names
open Nameops
open Util
open Pp
open Printer
open Vernacinterp
open Environ
open Termast
open Command
open Tactics 
open Safe_typing
open Nametab

type setoid =
    { set_a : constr;
      set_aeq : constr;
      set_th : constr
    }

type morphism =
    { lem : constr;
      profil : bool list;
      arg_types : constr list;
      lem2 : constr option
    }

let constr_of c = Astterm.interp_constr Evd.empty (Global.env()) c

let constant dir s =
  let dir = make_dirpath
              (List.map id_of_string (List.rev ("Coq"::"Setoids"::dir))) in
  let id = id_of_string s in
    try 
      Declare.global_reference_in_absolute_module dir id
  with Not_found ->
    anomaly ("Setoid: cannot find "^(Nametab.string_of_qualid (Nametab.make_qualid dir id)))

let global_constant dir s =
  let dir = make_dirpath
              (List.map id_of_string (List.rev ("Coq"::"Init"::dir))) in
  let id = id_of_string s in
    try 
      Declare.global_reference_in_absolute_module dir id
  with Not_found ->
    anomaly ("Setoid: cannot find "^(Nametab.string_of_qualid (Nametab.make_qualid dir id)))

let current_constant id =
  try
    Declare.global_reference id
  with Not_found ->
    anomaly ("Setoid: cannot find "^(string_of_id id))

(* Setoid_theory *)

let coq_Setoid_Theory = lazy(constant ["Setoid"] "Setoid_Theory")

let coq_seq_refl = lazy(constant ["Setoid"] "Seq_refl")
let coq_seq_sym = lazy(constant ["Setoid"] "Seq_sym")
let coq_seq_trans = lazy(constant ["Setoid"] "Seq_trans")

let coq_fleche = lazy(constant ["Setoid"] "fleche")

(* Coq constants *)

let coqeq = lazy(global_constant ["Logic"] "eq")

let coqconj = lazy(global_constant ["Logic"] "conj")

(************************* Table of declared setoids **********************)


(* Setoids are stored in a table which is synchronised with the Reset mechanism. *)

module Cmap = Map.Make(struct type t = constr let compare = compare end)

let setoid_table = ref Gmap.empty

let setoid_table_add (s,th) = setoid_table := Gmap.add s th !setoid_table
let setoid_table_find s = Gmap.find s !setoid_table
let setoid_table_mem s = Gmap.mem s !setoid_table

let equiv_list () = List.map (fun x -> x.set_aeq) (Gmap.rng !setoid_table)

let _ = 
  Summary.declare_summary "setoid-table"
    { Summary.freeze_function = (fun () -> !setoid_table);
      Summary.unfreeze_function = (fun t -> setoid_table := t);
      Summary.init_function = (fun () -> setoid_table := Gmap .empty);
      Summary.survive_section = false }

(* Declare a new type of object in the environment : "setoid-theory". *)

let (setoid_to_obj, obj_to_setoid)=
  let cache_set (_,(s, th)) = setoid_table_add (s,th)
  and export_set x = Some x 
  in 
    declare_object ("setoid-theory",
		    { cache_function = cache_set;
		      load_function = (fun _ -> ());
		      open_function = cache_set;
		      export_function = export_set})

(******************************* Table of declared morphisms ********************)

(* Setoids are stored in a table which is synchronised with the Reset mechanism. *)

let morphism_table = ref Gmap.empty

let morphism_table_add (m,c) = morphism_table := Gmap.add m c !morphism_table
let morphism_table_find m = Gmap.find m !morphism_table
let morphism_table_mem m = Gmap.mem m !morphism_table

let _ = 
  Summary.declare_summary "morphism-table"
    { Summary.freeze_function = (fun () -> !morphism_table);
      Summary.unfreeze_function = (fun t -> morphism_table := t);
      Summary.init_function = (fun () -> morphism_table := Gmap .empty);
      Summary.survive_section = false }

(* Declare a new type of object in the environment : "morphism-definition". *)

let (morphism_to_obj, obj_to_morphism)=
  let cache_set (_,(m, c)) = morphism_table_add (m, c)
  and export_set x = Some x 
  in 
    declare_object ("morphism-definition",
		    { cache_function = cache_set;
		      load_function = (fun _ -> ());
		      open_function = cache_set;
		      export_function = export_set})

(************************** Adding a setoid to the database *********************)

(* Find the setoid theory associated with a given type A.
This implies that only one setoid theory can be declared for
a given type A. *)

let find_theory a =
  try 
    setoid_table_find a 
  with Not_found ->
    errorlabstrm "Setoid" 
      [< 'sTR "No Declared Setoid Theory for ";
	 prterm a; 'fNL;
	 'sTR "Use Add Setoid to declare it">]
    
(* Add a Setoid to the database after a type verification. *)

let eq_lem_proof env a eq sym trans = 
  lambda_create env
    (a, lambda_create env
       (a, lambda_create env
	  (a, lambda_create env 
	     (a, lambda_create env 
		((mkApp (eq, [|(mkRel 4);(mkRel 3)|])), lambda_create env
		   ((mkApp (eq, [|(mkRel 3);(mkRel 2)|])), lambda_create env
		      ((mkApp (eq, [|(mkRel 6);(mkRel 4)|])),
		       (mkApp (trans,
			       [|(mkRel 6);(mkRel 7);(mkRel 4);
				 (mkApp (sym, [|(mkRel 7);(mkRel 6);(mkRel 3)|]));
				 (mkApp (trans,
					 [|(mkRel 7);(mkRel 5);(mkRel 4);(mkRel 1);(mkRel 2)|]))|]
			      )))))))))

let eq_lem2_proof env a eq sym trans = 
  lambda_create env
    (a, lambda_create env
       (a, lambda_create env
	  (a, lambda_create env 
	     (a, lambda_create env 
		((mkApp (eq, [|(mkRel 4);(mkRel 3)|])), lambda_create env
		   ((mkApp (eq, [|(mkRel 3);(mkRel 2)|])),
		    (mkApp ((Lazy.force coqconj),
			    [|(mkArrow 
				 (mkApp (eq, [|(mkRel 6);(mkRel 4)|]))
				 (mkApp (eq, [|(mkRel 6);(mkRel 4)|])));
			      (mkArrow
				 (mkApp (eq, [|(mkRel 5);(mkRel 3)|]))
				 (mkApp (eq, [|(mkRel 7);(mkRel 5)|])));
			      (lambda_create env
				 ((mkApp (eq, [|(mkRel 6);(mkRel 4)|])),
				  (mkApp (trans,
					  [|(mkRel 6);(mkRel 7);(mkRel 4);
					    (mkApp (sym, [|(mkRel 7);(mkRel 6);(mkRel 3)|]));
					    (mkApp (trans,
						    [|(mkRel 7);(mkRel 5);(mkRel 4);(mkRel 1);(mkRel 2)|]))|]))));
			      (lambda_create env
				 ((mkApp (eq, [|(mkRel 5);(mkRel 3)|])),
				  (mkApp (trans,
					  [|(mkRel 7);(mkRel 6);(mkRel 5);(mkRel 3);
					    (mkApp (trans,
						    [|(mkRel 6);(mkRel 4);(mkRel 5);(mkRel 1);
						      (mkApp (sym, [|(mkRel 5);(mkRel 4);(mkRel 2)|]))|]))|]))))|]))))))))

let gen_eq_lem_name =
  let i = ref 0 in
    function () -> 
      incr i;
      make_ident "setoid_eq_ext" (Some !i)

let add_setoid a aeq th =
  if setoid_table_mem a 
  then errorlabstrm "Add Setoid"
    [< 'sTR "A Setoid Theory is already declared for "; prterm a >]
  else let env = Global.env () in
    if (is_conv env Evd.empty (Typing.type_of env Evd.empty th)
	  (mkApp ((Lazy.force coq_Setoid_Theory), [| a; aeq |])))
    then (Lib.add_anonymous_leaf 
	    (setoid_to_obj 
	       (a, { set_a = a;
		     set_aeq = aeq;
		     set_th = th}));
	  let sym = mkApp ((Lazy.force coq_seq_sym), [|a; aeq; th|]) in
	  let trans = mkApp ((Lazy.force coq_seq_trans), [|a; aeq; th|]) in
	  let eq_morph = eq_lem_proof env a aeq sym trans in
	  let eq_morph2 = eq_lem2_proof env a aeq sym trans in
	    Options.if_verbose pPNL [< prterm a;'sTR " is registered as a setoid">];
	    let eq_ext_name = gen_eq_lem_name () in 
	    let eq_ext_name2 = gen_eq_lem_name () in 
	    let _ = Declare.declare_constant eq_ext_name
		      ((ConstantEntry {const_entry_body = eq_morph; 
				       const_entry_type = None;
                                       const_entry_opaque = true}),
		       Declare.NeverDischarge) in
	    let _ = Declare.declare_constant eq_ext_name2
		      ((ConstantEntry {const_entry_body = eq_morph2; 
				       const_entry_type = None;
                                       const_entry_opaque = true}),
		       Declare.NeverDischarge) in
	    let eqmorph = (current_constant eq_ext_name) in
	    let eqmorph2 = (current_constant eq_ext_name2) in
	      (Lib.add_anonymous_leaf
		 (morphism_to_obj (aeq, 
				   { lem = eqmorph;
				     profil = [true; true];
				     arg_types = [a;a];
				     lem2 = (Some eqmorph2)})));
	      Options.if_verbose pPNL [< prterm aeq;'sTR " is registered as a morphism">])
    else errorlabstrm "Add Setoid" [< 'sTR "Not a valid setoid theory" >]

(* The vernac command "Add Setoid" *)

let constr_of_comarg = function 
  | VARG_CONSTR c -> constr_of c
  | _ -> anomaly "Add Setoid"

let _ = 
  vinterp_add "AddSetoid"
    (function 
       | [(VARG_CONSTR a); (VARG_CONSTR aeq); (VARG_CONSTR th)] -> 
	   (fun () -> (add_setoid 
			 (constr_of a)
			 (constr_of aeq)
			 (constr_of th)))
       | _ -> anomaly "AddSetoid")
 
(***************** Adding a morphism to the database ****************************)

(* We maintain a table of the currently edited proofs of morphism lemma
   in order to add them in the morphism_table when the user does Save *)

let edited = ref Gmap.empty

let new_edited id m profil = 
  edited := Gmap.add id (m,profil)  !edited

let is_edited id =
  Gmap.mem id !edited

let no_more_edited id =
  edited := Gmap.remove id !edited

let what_edited id =
  Gmap.find id !edited

let check_is_dependent t n =
  let rec aux t i n =
    if (i<n)
    then (dependent (mkRel i) t) || (aux t (i+1) n)
    else false
  in aux t 0 n

let gen_lem_name m = match kind_of_term m with 
  | Var id -> add_suffix id "_ext"
  | Const sp -> add_suffix (basename sp) "_ext"
  | Ind (sp, i) -> add_suffix (basename sp) ((string_of_int i)^"_ext")
  | Construct ((sp,i),j) -> add_suffix
      (basename sp) ((string_of_int i)^(string_of_int i)^"_ext")
  | _ -> errorlabstrm "New Morphism" [< 'sTR "The term "; prterm m; 'sTR "is not a known name">]

let gen_lemma_tail m lisset body n =
  let l = (List.length lisset) in
  let a1 = Array.create l (mkRel 0) in
  let a2 = Array.create l (mkRel 0) in
  let rec aux i n = function
    | true::q -> 
	a1.(i) <- (mkRel n);
	a2.(i) <- (mkRel (n-1));
	aux (i+1) (n-2) q
    | false::q ->
	a1.(i) <- (mkRel n);
	a2.(i) <- (mkRel n);
	aux (i+1) (n-1) q
    | [] -> () in 
    aux 0 n lisset;
    if (eq_constr body mkProp)
    then mkArrow (mkApp (m,a1)) (lift 1 (mkApp (m, a2)))
    else if (setoid_table_mem body)
    then mkApp ((setoid_table_find body).set_aeq, [|(mkApp (m, a1)); (mkApp (m, a2))|])
    else mkApp ((Lazy.force coqeq), [|body; (mkApp (m, a1)); (mkApp (m, a2))|])

let gen_lemma_middle m larg lisset body n =
  let rec aux la li i n = match (la, li) with
    | ([], []) -> gen_lemma_tail m lisset body n
    | (t::q, true::lq) -> 
	mkArrow (mkApp ((setoid_table_find t).set_aeq, 
			[|(mkRel i); (mkRel (i-1))|])) (aux q lq (i-1) (n+1))
    | (t::q, false::lq) -> aux q lq (i-1) n
    | _ -> assert false
  in aux larg lisset n n

let gen_compat_lemma env m body larg lisset = 
  let rec aux la li n = match (la, li) with
    | (t::q, true::lq) -> 
	prod_create env (t,(prod_create env (t, (aux q lq (n+2)))))
    | (t::q, false::lq) -> 
	prod_create env (t, (aux q lq (n+1)))
    | ([],[]) -> gen_lemma_middle m larg lisset body n
    | _ -> assert false
  in aux larg lisset 0

let new_morphism m id =
  if morphism_table_mem m
  then errorlabstrm "New Morphism"
    [< 'sTR "The term "; prterm m; 'sTR " is already declared as a morphism">]
  else 
    let env = Global.env() in
    let typeofm = (Typing.type_of env Evd.empty m) in
    let typ = (nf_betaiota typeofm) in  (* nf_bdi avant, mais bug *)
    let (argsrev, body) = (decompose_prod typ) in
    let args = (List.rev argsrev) in
      if (args=[])
      then errorlabstrm "New Morphism"
	[< 'sTR "The term "; prterm m; 'sTR " is not a product">]
      else if (check_is_dependent typ (List.length args))
      then  errorlabstrm "New Morphism"
	[< 'sTR "The term "; prterm m; 'sTR " should not be a dependent product">]
      else (
	let args_t = (List.map snd args) in
	let poss = (List.map setoid_table_mem args_t) in
	let lem = (gen_compat_lemma env m body args_t poss) in
	let lemast = (ast_of_constr true env lem) in
	  new_edited id m poss;
	  start_proof_com (Some id) Declare.NeverDischarge lemast;
	  (Options.if_verbose Vernacentries.show_open_subgoals ()))

let rec sub_bool l1 n = function
  | [] -> []
  | true::q -> ((List.hd l1), n)::(sub_bool (List.tl l1) (n-2) q)
  | false::q -> (sub_bool (List.tl l1) (n-1) q)

let gen_lemma_iff_tail m mext larg lisset n k =
  let a1 = Array.create k (mkRel 0) in
  let a2 = Array.create k (mkRel 0) in
  let nb = List.length lisset in
  let b1 = Array.create nb (mkRel 0) in
  let b2 = Array.create nb (mkRel 0) in
  let rec aux i j = function
    |[] -> ()
    |true::q ->
       (a1.(i) <- (mkRel j);
	a1.(i+1) <- (mkRel (j-1));
	a2.(i) <- (mkRel (j-1));
	a2.(i+1) <- (mkRel j);
	aux (i+2) (j-2) q)
    |false::q ->
       (a1.(i) <- (mkRel j);
	a2.(i) <- (mkRel j);
	aux (i+1) (j-1) q) in
  let rec aux2 i j = function
    | (t,p)::q -> 
	let th = (setoid_table_find t).set_th
	and equiv = (setoid_table_find t).set_aeq in
	  a1.(i) <- (mkRel j);
	  a2.(i) <- mkApp ((Lazy.force coq_seq_sym),
			   [|t; equiv; th; (mkRel p); (mkRel (p-1)); (mkRel j)|]);
	  aux2 (i+1) (j-1) q
    | [] -> () in
  let rec aux3 i j = function
    | true::q -> 
	b1.(i) <- (mkRel j);
	b2.(i) <- (mkRel (j-1));
	aux3 (i+1) (j-2) q
    | false::q ->
	b1.(i) <- (mkRel j);
	b2.(i) <- (mkRel j);
	aux3 (i+1) (j-1) q
    | [] -> () in 
    aux 0 k lisset;
    aux2 n (k-n) (sub_bool larg k lisset);
    aux3 0 k lisset;
    mkApp ((Lazy.force coqconj),
	   [|(mkArrow (mkApp (m,b1)) (lift 1 (mkApp (m, b2))));
	     (mkArrow (mkApp (m,b2)) (lift 1 (mkApp (m, b1))));
	     (mkApp (mext, a1));(mkApp (mext, a2))|])

let gen_lemma_iff_middle env m mext larg lisset n =
  let rec aux la li i k = match (la, li) with
    | ([], []) -> gen_lemma_iff_tail m mext larg lisset n k
    | (t::q, true::lq) -> 
	lambda_create env ((mkApp ((setoid_table_find t).set_aeq, [|(mkRel i); (mkRel (i-1))|])),
			   (aux q lq (i-1) (k+1)))
    | (t::q, false::lq) -> aux q lq (i-1) k
    | _ -> assert false
  in aux larg lisset n n

let gen_lem_iff env m mext larg lisset =
  let rec aux la li n = match (la, li) with
    | (t::q, true::lq) -> 
	lambda_create env (t,(lambda_create env (t, (aux q lq (n+2)))))
    | (t::q, false::lq) -> 
	lambda_create env (t, (aux q lq (n+1)))
    | ([],[]) -> gen_lemma_iff_middle env m mext larg lisset n
    | _ -> assert false
  in aux larg lisset 0

let add_morphism lem_name (m,profil) =
  if morphism_table_mem m
  then errorlabstrm "New Morphism"
    [< 'sTR "The term "; prterm m; 'sTR " is already declared as a morpism">]
  else 
    let env = Global.env() in
    let mext = (current_constant lem_name) in
    let typeofm = (Typing.type_of env Evd.empty m) in
    let typ = (nf_betaiota typeofm) in
    let (argsrev, body) = (decompose_prod typ) in
    let args = List.rev argsrev in
    let args_t = (List.map snd args) in
    let poss = (List.map setoid_table_mem args_t) in
    let _ = assert (poss=profil) in
      (if (eq_constr body mkProp)
       then
	 (let lem_2 = gen_lem_iff env m mext args_t poss in
	  let lem2_name = add_suffix lem_name "2" in
	  let _ = Declare.declare_constant lem2_name
		    ((ConstantEntry {const_entry_body = lem_2; 
				     const_entry_type = None;
                                     const_entry_opaque = true}),
		     Declare.NeverDischarge) in
	  let lem2 = (current_constant lem2_name) in
	    (Lib.add_anonymous_leaf
	       (morphism_to_obj (m, 
				 { lem = mext;
				   profil = poss;
				   arg_types = args_t;
				   lem2 = (Some lem2)})));
	    Options.if_verbose message ((string_of_id lem2_name) ^ " is defined"))
       else
	 (Lib.add_anonymous_leaf
	    (morphism_to_obj (m, 
			      { lem = mext;
				profil = poss;
				arg_types = args_t;
				lem2 = None}))));
      Options.if_verbose pPNL [< prterm m;'sTR " is registered as a morphism">]   
    
let _ = 
  let current_save = vinterp_map "SaveNamed" in
    overwriting_vinterp_add "SaveNamed"
      (function 
	 |[] -> (fun () -> 
		   let pf_id = Pfedit.get_current_proof_name () in
		     current_save [] ();
		     if (is_edited pf_id)
		     then 
		       (add_morphism pf_id (what_edited pf_id);
			no_more_edited pf_id))
	 | _ -> assert false)

let _ = 
  let current_defined = vinterp_map "DefinedNamed" in
    overwriting_vinterp_add "DefinedNamed"
      (function 
	 |[] -> (fun () -> let pf_id = Pfedit.get_current_proof_name () in
			 current_defined [] ();
			 if (is_edited pf_id)
			 then 
			   (add_morphism pf_id (what_edited pf_id);
			   no_more_edited pf_id))
	 | _ -> assert false)

(*
let _ = 
  vinterp_add "NewMorphism"
    (function 
       | [(VARG_IDENTIFIER s)] ->
	   (fun () -> 
	      try 
		(let m = Declare.global_reference CCI s in
		   new_morphism m (gen_lem_name m))
	      with 
		  Not_found -> 
		    errorlabstrm "New Morphism" 
		      [< 'sTR "The term "; 'sTR(string_of_id s); 'sTR" is not a known name">])
       | _ -> anomaly "NewMorphism")
*)
  
let _ = 
  vinterp_add "NamedNewMorphism"
    (function 
       | [(VARG_IDENTIFIER s);(VARG_CONSTR m)] ->
	   (fun () -> new_morphism (constr_of m) s)
       | _ -> anomaly "NewMorphism")

(****************************** The tactic itself *******************************)

type constr_with_marks =
  | MApp of constr_with_marks array 
  | Toreplace
  | Tokeep
  | Mimp of constr_with_marks * constr_with_marks

let is_to_replace = function
  | Tokeep -> false
  | Toreplace -> true
  | MApp _ -> true
  | Mimp _ -> true

let get_mark a = 
  Array.fold_left (||) false (Array.map is_to_replace a)

let rec mark_occur t in_c =
  if (eq_constr t in_c) then Toreplace else
    match kind_of_term in_c with
      | App (c,al) -> 
	  let a = Array.map (mark_occur t) al
	  in if (get_mark a) then (MApp a) else Tokeep
      | Prod (_, c1, c2) -> 
	  if (dependent (mkRel 1) c2)
	  then Tokeep
	  else 
	    let c1m = mark_occur t c1 in
	    let c2m = mark_occur t c2 in
	      if ((is_to_replace c1m)||(is_to_replace c2m))
	      then (Mimp (c1m, c2m))
	      else Tokeep
      | _ -> Tokeep

let create_args ca ma bl c1 c2 = 
  let rec aux i = function
    | [] -> []
    | true::q -> 
	if (is_to_replace ma.(i)) 
	then (replace_term c1 c2 ca.(i))::ca.(i)::(aux (i+1) q)
	else ca.(i)::ca.(i)::(aux (i+1) q)
    | false::q -> ca.(i)::(aux (i+1) q)
  in
    aux 0 bl


let res_tac c a hyp =
  let sa = setoid_table_find a in
  let fin = match hyp with
    | None -> Auto.full_trivial
    | Some h -> 
	tclORELSE (tclTHEN (tclTRY (apply h)) (tclFAIL 0)) 
	  (tclORELSE (tclTHEN (tclTRY (tclTHEN (apply (mkApp ((Lazy.force coq_seq_sym), [|sa.set_a; sa.set_aeq; sa.set_th|]))) (apply h))) (tclFAIL 0))
	     Auto.full_trivial) in
    tclORELSE (tclTHEN (tclTRY (apply (mkApp ((Lazy.force coq_seq_refl), [|sa.set_a; sa.set_aeq; sa.set_th;c|])))) (tclFAIL 0))
      (tclORELSE assumption
	 (tclORELSE (tclTHEN (tclTRY (apply (mkApp ((Lazy.force coq_seq_sym), [|sa.set_a; sa.set_aeq; sa.set_th|])))) assumption)
	    fin))

let id_res_tac c a = 
  let sa = setoid_table_find a in
    (tclTRY (apply (mkApp ((Lazy.force coq_seq_refl), [|sa.set_a; sa.set_aeq; sa.set_th; c|]))))

(* An exception to catchs errors *)

exception Nothing_found of constr;;

let rec create_tac_list i a al c1 c2 hyp args_t = function
  | [] -> []
  | false::q -> create_tac_list (i+1) a al c1 c2 hyp args_t q
  | true::q -> 
      if (is_to_replace a.(i))
      then (zapply false al.(i) a.(i) c1 c2 hyp)::(create_tac_list (i+1) a al c1 c2 hyp args_t q)
      else (id_res_tac al.(i) (List.nth args_t i))::(create_tac_list (i+1) a al c1 c2 hyp args_t q)
(*      else tclIDTAC::(create_tac_list (i+1) a al c1 c2 hyp q) *)

and zapply is_r gl gl_m c1 c2 hyp glll = (match ((kind_of_term gl), gl_m) with
  | ((App (c,al)),(MApp a)) -> (
      try 
	let m = morphism_table_find c in
	let args = Array.of_list (create_args al a m.profil c1 c2) in
	  if is_r
	  then tclTHENS (apply (mkApp (m.lem, args)))
	    ((create_tac_list 0 a al c1 c2 hyp m.arg_types m.profil)@[tclIDTAC])
 	  else (match m.lem2 with
		  | None -> 
		      tclTHENS (apply (mkApp (m.lem, args))) (create_tac_list 0 a al c1 c2 hyp m.arg_types m.profil)
		  | Some xom -> 
		      tclTHENS (apply (mkApp (xom, args))) (create_tac_list 0 a al c1 c2 hyp m.arg_types m.profil))
      with Not_found -> errorlabstrm "Setoid_replace" 
	  [< 'sTR "The term "; prterm c; 'sTR " has not been declared as a morphism">])
  | ((Prod (_,hh, cc)),(Mimp (hhm, ccm))) ->
      let al = [|hh; cc|] in
      let a = [|hhm; ccm|] in
      let fleche_constr = (Lazy.force coq_fleche) in
      let fleche_cp = destConst fleche_constr in
      let new_concl = (mkApp (fleche_constr, al)) in
	if is_r 
	then
	  let m = morphism_table_find fleche_constr in
	  let args = Array.of_list (create_args al a m.profil c1 c2) in  
	    tclTHEN (change_in_concl new_concl)
	      (tclTHENS (apply (mkApp (m.lem, args)))
		 ((create_tac_list 0 a al c1 c2 hyp m.arg_types m.profil)@[unfold_constr (ConstRef fleche_cp)]))
(*		 ((create_tac_list 0 a al c1 c2 hyp m.arg_types m.profil)@[tclIDTAC])) *)
	else (zapply is_r new_concl (MApp a) c1 c2 hyp)
(*      let args = Array.of_list (create_args [|hh; cc|] [|hhm; ccm|] [true;true] c1 c2) in
	if is_r
	then tclTHENS (apply (mkApp ((Lazy.force coq_fleche_ext), args)))
	  ((create_tac_list 0 [|hhm; ccm|] [|hh; cc|] c1 c2 hyp [mkProp; mkProp] [true;true])@[tclIDTAC])
	else tclTHENS (apply (mkApp ((Lazy.force coq_fleche_ext2), args)))
	  ((create_tac_list 0 [|hhm; ccm|] [|hh; cc|] c1 c2 hyp [mkProp; mkProp] [true;true])@[tclIDTAC])
*)
  | (_, Toreplace) -> (res_tac gl (pf_type_of glll gl) hyp) (* tclORELSE Auto.full_trivial tclIDTAC *)
  | (_, Tokeep) -> (match hyp with 
		      | None -> errorlabstrm "Setoid_replace"
			  [< 'sTR "No replacable occurence of "; prterm c1; 'sTR " found">]
		      | Some _ ->errorlabstrm "Setoid_replace"
			  [< 'sTR "No rewritable occurence of "; prterm c1; 'sTR " found">])
  | _ -> anomaly ("Bug in Setoid_replace")) glll

let setoid_replace c1 c2 hyp gl =
  let but = (pf_concl gl) in
    (zapply true but (mark_occur c1 but) c1 c2 hyp) gl

let general_s_rewrite lft2rgt c gl =
  let ctype = pf_type_of gl c in
  let (equiv, args) = decompose_app ctype in
  let rec get_last_two = function
    | [c1;c2] -> (c1, c2)
    | x::y::z -> get_last_two (y::z)
    | _ -> error "The term provided is not an equivalence" in 
  let (c1,c2) = get_last_two args in
    if lft2rgt
    then setoid_replace c1 c2 (Some c) gl
    else setoid_replace c2 c1 (Some c) gl

let setoid_rewriteLR = general_s_rewrite true

let setoid_rewriteRL = general_s_rewrite false

let dyn_setoid_replace = function
  | [(Constr c1);(Constr c2)] -> (fun gl -> setoid_replace c1 c2 None gl)
  | _ -> invalid_arg "Setoid_replace : Bad arguments"
      
let h_setoid_replace = hide_tactic "Setoid_replace" dyn_setoid_replace

let dyn_setoid_rewriteLR = function
  | [(Constr c)] -> setoid_rewriteLR c
  | _ -> invalid_arg "Setoid_rewrite : Bad arguments"

let h_setoid_rewriteLR = hide_tactic "Setoid_rewriteLR" dyn_setoid_rewriteLR

let dyn_setoid_rewriteRL = function
  | [(Constr c)] -> setoid_rewriteRL c
  | _ -> invalid_arg "Setoid_rewrite : Bad arguments"

let h_setoid_rewriteRL = hide_tactic "Setoid_rewriteRL" dyn_setoid_rewriteRL
