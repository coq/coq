(* A proof by pointing algorithm. *)
open Util;;
open Names;;
open Term;;
open Tactics;;
open Tacticals;;
open Hipattern;;
open Pattern;;
open Reduction;;
open Ctast;;
open Rawterm;;
open Environ;;

open Proof_trees;;
open Proof_type;;
open Tacmach;;
open Tacexpr;;
open Typing;;
open Pp;;

(* get_hyp_by_name : goal sigma -> string -> constr,
   looks up for an hypothesis (or a global constant), from its name *)
let get_hyp_by_name g name =
  let evd = project g in
  let env = pf_env g in
  try (let judgment = 
         Pretyping.understand_judgment 
          evd env (RVar(dummy_loc, name)) in
       ("hyp",judgment.uj_type))
(* je sais, c'est pas beau, mais je ne sais pas trop me servir de look_up...
   Lo�c *)
  with _ -> (let ast = Termast.ast_of_qualid (Libnames.make_short_qualid name)in
             let c = Astterm.interp_constr evd env ast in
             ("cste",type_of (Global.env()) Evd.empty c))
;;

type pbp_atom =
  | PbpTryAssumption of identifier option
  | PbpTryClear of identifier list
  | PbpGeneralize of identifier * identifier list
  | PbpLApply of identifier (* = CutAndApply *)
  | PbpIntros of identifier list
  | PbpSplit
  (* Existential *)
  | PbpExists of identifier
  (* Or *)
  | PbpLeft
  | PbpRight
  (* Not *)
  | PbpReduce
  (* Head *)
  | PbpApply of identifier
  | PbpElim of identifier * identifier list;;

(* Invariant: In PbpThens ([a1;...;an],[t1;...;tp]), all tactics
   [a1]..[an-1] are atomic (or try of an atomic) tactic and produce
   exactly one goal, and [an] produces exactly p subgoals

   In [PbpThen [a1;..an]], all tactics are (try of) atomic tactics and
   produces exactly one subgoal, except the last one which may complete the
   goal

   Convention: [PbpThen []] is Idtac and [PbpThen t] is a coercion
   from atomic to composed tactic
*)

type pbp_sequence =
  | PbpThens of pbp_atom list * pbp_sequence list
  | PbpThen of pbp_atom list

(* This flattens sequences of tactics producing just one subgoal *)
let chain_tactics tl1 = function
  | PbpThens (tl2, tl3) -> PbpThens (tl1@tl2, tl3)
  | PbpThen tl2 -> PbpThen (tl1@tl2)

type pbp_rule = (identifier list *
                    identifier list *
                    bool *
                    identifier option *
                    (types, constr) kind_of_term *
                    int list *
                    (identifier list ->
                     identifier list ->
                     bool ->
                       identifier option -> (types, constr) kind_of_term -> int list -> pbp_sequence)) ->
                    pbp_sequence option;;

let zz = (0,0);;

(*
let make_named_intro s =
    Node(zz, "Intros",
          [Node(zz,"INTROPATTERN",
            [Node(zz,"LISTPATTERN",
              [Node(zz, "IDENTIFIER", 
                [Nvar(zz, s)])])])]);;
*)
let make_named_intro id = PbpIntros [id]

(*
let get_name_from_intro = function
    Node(a, "Intros",
          [Node(b,"INTROPATTERN",
            [Node(c,"LISTPATTERN",
              [Node(d, "IDENTIFIER", 
                [Nvar(e, s)])])])]) ->
		  Some s
  | _ -> None;;
*)
(*
let make_clears =  function
    [] -> Node(zz, "Idtac",[])
  | str_list ->
      Node(zz, "TRY", [Node(zz,"Clear",
	   [Node(zz, "CLAUSE", List.map (function s -> Nvar(zz,s)) str_list)])
	       ]);;
*)
let make_clears str_list = PbpThen [PbpTryClear str_list]

let add_clear_names_if_necessary tactic clear_names =
    match clear_names with
      [] -> tactic
    | l -> chain_tactics [PbpTryClear l] tactic;;

let make_final_cmd f optname clear_names constr path =
(*    let tactic = f optname constr path in*)
    add_clear_names_if_necessary (f optname constr path) clear_names;;

let (rem_cast:pbp_rule) = function
    (a,c,cf,o, Cast(f,_), p, func) ->
      Some(func a c cf o (kind_of_term f) p)
  | _ -> None;;

let (forall_intro: pbp_rule) = function
  (avoid,
   clear_names,
   clear_flag,
   None,
   Prod(Name x, _, body),
   (2::path),
   f) ->
     let x' = next_global_ident_away x avoid in
      Some(chain_tactics [make_named_intro x']
	      (f (x'::avoid)
		clear_names clear_flag None (kind_of_term body) path))
| _ -> None;;

let (imply_intro2: pbp_rule) = function
  avoid, clear_names,
  clear_flag, None, Prod(Anonymous, _, body), 2::path, f ->
   let h' = next_global_ident_away (id_of_string "H") avoid in
     Some(chain_tactics [make_named_intro h']
          (f (h'::avoid) clear_names clear_flag None (kind_of_term body) path))
  | _ -> None;;


let (imply_intro1: pbp_rule) = function
  avoid, clear_names,
  clear_flag, None, Prod(Anonymous, prem, body), 1::path, f ->
   let h' = next_global_ident_away (id_of_string "H") avoid in
   let str_h' = h' in
     Some(chain_tactics [make_named_intro str_h']
            (f (h'::avoid) clear_names clear_flag (Some str_h') 
		(kind_of_term prem) path))
  | _ -> None;;

let make_pbp_pattern x =
  Coqast.Node(zz,"APPLIST",
    [Coqast.Nvar (zz, id_of_string "PBP_META");
     Coqast.Nvar (zz, id_of_string ("Value_for_" ^ (string_of_id x)))])

let rec make_then = function
  | [] -> TacId
  | [t] -> t
  | t1::t2::l -> make_then (TacThen (t1,t2)::l)

let make_pbp_atomic_tactic = function
  | PbpTryAssumption None -> TacTry (TacAtom (zz, TacAssumption))
  | PbpTryAssumption (Some a) ->
      TacTry (TacAtom (zz, TacExact (Coqast.Nvar (zz,a))))
  | PbpExists x -> 
      TacAtom (zz, TacSplit (ImplicitBindings [make_pbp_pattern x]))
  | PbpGeneralize (h,args) ->
      let l = Coqast.Nvar (zz, h)::List.map make_pbp_pattern args in
      TacAtom (zz, TacGeneralize [Coqast.Node (zz, "APPLIST", l)])
  | PbpLeft -> TacAtom (zz, TacLeft NoBindings)
  | PbpRight -> TacAtom (zz, TacRight NoBindings)
  | PbpReduce -> TacAtom (zz, TacReduce (Red false, []))
  | PbpIntros l -> 
      let l = List.map (fun id -> IntroIdentifier id) l in
      TacAtom (zz, TacIntroPattern l)
  | PbpLApply h -> TacAtom (zz, TacLApply (Coqast.Nvar (zz, h)))
  | PbpApply h -> TacAtom (zz, TacApply (Coqast.Nvar(zz, h),NoBindings))
  | PbpElim (hyp_name, names) ->
      let bind = List.map (fun s -> (NamedHyp s,make_pbp_pattern s)) names in
      TacAtom
	(zz, TacElim ((Coqast.Nvar(zz,hyp_name),ExplicitBindings bind),None))
  | PbpTryClear l -> 
      TacTry (TacAtom (zz, TacClear (List.map (fun s -> AN (zz,s)) l)))
  | PbpSplit -> TacAtom (zz, TacSplit NoBindings);;

let rec make_pbp_tactic = function
  | PbpThen tl -> make_then (List.map make_pbp_atomic_tactic tl)
  | PbpThens (l,tl) ->
      TacThens
        (make_then (List.map make_pbp_atomic_tactic l),
	 List.map make_pbp_tactic tl)

let (forall_elim: pbp_rule) = function
  avoid, clear_names, clear_flag, 
  Some h, Prod(Name x, _, body), 2::path, f ->
  let h' = next_global_ident_away (id_of_string "H") avoid in
  let clear_names' = if clear_flag then h::clear_names else clear_names in
    Some
     (chain_tactics [PbpGeneralize (h,[x]); make_named_intro h']
        (f (h'::avoid) clear_names' true (Some h') (kind_of_term body) path))
  | _ -> None;;


let (imply_elim1: pbp_rule) = function
  avoid, clear_names, clear_flag,
  Some h, Prod(Anonymous, prem, body), 1::path, f ->
  let clear_names' = if clear_flag then h::clear_names else clear_names in
  let h' = next_global_ident_away (id_of_string "H") avoid in
  let str_h' = (string_of_id h') in
  Some(PbpThens
	  ([PbpLApply h],
	   [PbpThen [PbpIntros [h']];
            make_clears (h::clear_names);
	    f avoid clear_names' false None (kind_of_term prem) path]))
  | _ -> None;;


let (imply_elim2: pbp_rule) = function
  avoid, clear_names, clear_flag,
  Some h, Prod(Anonymous, prem, body), 2::path, f ->
  let clear_names' = if clear_flag then h::clear_names else clear_names in
  let h' = next_global_ident_away (id_of_string "H") avoid in
  Some(PbpThens
	 ([PbpLApply h],
          [chain_tactics [PbpIntros [h']]
              (f (h'::avoid) clear_names' false (Some h') 
		      (kind_of_term body) path);
           make_clears clear_names]))
  | _ -> None;;

let reference dir s =
  let dir = make_dirpath
              (List.map id_of_string (List.rev ("Coq"::"Init"::[dir]))) in
  let id = id_of_string s in
  try 
    Nametab.locate_in_absolute_module dir id
  with Not_found ->
    anomaly ("Coqlib: cannot find "^
	     (Libnames.string_of_qualid (Libnames.make_qualid dir id)))

let constant dir s =  Declare.constr_of_reference (reference dir s);;

let andconstr: unit -> constr = Coqlib.build_coq_and;;
let prodconstr () = constant "Datatypes" "prod";;
let exconstr () = constant "Logic" "ex";;
let exTconstr () = constant "Logic_Type" "exT";;
let sigconstr () = constant "Specif" "sig";;
let sigTconstr () = constant "Logic_Type" "sigT";;
let orconstr = Coqlib.build_coq_or;;
let sumboolconstr = Coqlib.build_coq_sumbool;;
let sumconstr() = constant "Datatypes" "sum";;
let notconstr = Coqlib.build_coq_not;;
let notTconstr () = constant "Logic_Type" "notT";;

let is_matching_local a b = is_matching (pattern_of_constr a) b;;

let (and_intro: pbp_rule) = function
    avoid, clear_names, clear_flag,
    None, App(and_oper, [|c1; c2|]), 2::a::path, f 
      ->
      if ((is_matching_local (andconstr()) and_oper) or
          (is_matching_local (prodconstr ()) and_oper)) & (a = 1 or a = 2) then
      	let cont_term = if a = 1 then c1 else c2 in
      	let cont_cmd = f avoid clear_names false None 
			 (kind_of_term cont_term) path in
      	let clear_cmd = make_clears clear_names in
      	let cmds =
            (if a = 1 
	    then [cont_cmd;clear_cmd] 
	    else [clear_cmd;cont_cmd]) in
      	Some (PbpThens ([PbpSplit],cmds))
      else None
  | _ -> None;;

let (ex_intro: pbp_rule) = function
    avoid, clear_names, clear_flag, None,
    App(oper, [| c1; c2|]), 2::2::2::path, f
      when (is_matching_local (exconstr ()) oper) or (is_matching_local (exTconstr ()) oper)
 	or (is_matching_local (sigconstr ()) oper)
	      or (is_matching_local (sigTconstr ()) oper) ->
		(match kind_of_term c2 with
		  Lambda(Name x, _, body) -> Some (PbpThen [PbpExists x])
		| _ -> None)
  | _ -> None;;

let (or_intro: pbp_rule) = function
    avoid, clear_names, clear_flag, None,
    App(or_oper, [|c1; c2 |]), 2::a::path, f ->
      if ((is_matching_local (orconstr ()) or_oper) or
        (is_matching_local (sumboolconstr ()) or_oper) or 
	(is_matching_local (sumconstr ()) or_oper))
	  & (a = 1 or a = 2) then
	let cont_term = if a = 1 then c1 else c2 in
	let fst_cmd = if a = 1 then PbpLeft else PbpRight in
	let cont_cmd = f avoid clear_names false None 
			 (kind_of_term cont_term) path in
	Some(chain_tactics [fst_cmd] cont_cmd)
      else
	None
  | _ -> None;;
	
let dummy_id = id_of_string "Dummy";;

let (not_intro: pbp_rule) = function
    avoid, clear_names, clear_flag, None,
    App(not_oper, [|c1|]), 2::1::path, f ->
      if(is_matching_local (notconstr ()) not_oper) or 
	(is_matching_local (notTconstr ()) not_oper) then
	let h' = next_global_ident_away (id_of_string "H") avoid in
	Some(chain_tactics [PbpReduce;make_named_intro h']
	       (f (h'::avoid) clear_names false (Some h') 
		  (kind_of_term c1) path))
      else
 	None
  | _ -> None;;



(*
let elim_with_bindings hyp_name names =
  Node(zz,"Elim", 
       [Node(zz, "COMMAND", [Nvar(zz,hyp_name)]);
	 Node(zz,"BINDINGS", 
	      List.map 
		(function s -> 
		  Node(zz,"BINDING",
		       [Nvar(zz,s);
			 Node
			   (zz,"COMMAND",
			    [Node
				(zz,"APPLIST",
				 [Nvar(zz,"PBP_META");
				   Nvar(zz,
					"value_for_" ^ s)])])])) names)]);;
*)
let elim_with_bindings hyp_name names =
  PbpElim (hyp_name, names);;

let auxiliary_goals clear_names clear_flag this_name n_aux =
  let clear_cmd = 
    make_clears (if clear_flag then (this_name ::clear_names) else clear_names) in
  let rec clear_list = function
      0 -> []
    | n -> clear_cmd::(clear_list (n - 1)) in
  clear_list n_aux;;

(* This function is used to follow down a path, while staying on the spine of
   successive products (universal quantifications or implications).
   Arguments are the current observed constr object and the path that remains
   to be followed, and an integer indicating how many products have already been
   crossed.
   Result is:
     - a list of string indicating the names of universally quantified variables.
     - a list of integers indicating the positions of the successive 
       universally quantified variables.
     - an integer indicating the number of non-dependent products.
     - the last constr object encountered during the walk down, and
     - the remaining path.

   For instance the following session should happen:
  let tt = raw_constr_of_com (Evd.mt_evd())(gLOB(initial_sign()))
     (parse_com "(P:nat->Prop)(x:nat)(P x)->(P x)") in
     down_prods (tt, [2;2;2], 0)
  ---> ["P","x"],[0;1], 1, <<(P x)>>, []
*)


let rec down_prods: (types, constr) kind_of_term * (int list) * int -> 
           identifier list * (int list) * int * (types, constr) kind_of_term *
  (int list) = 
   function
     Prod(Name x, _, body), 2::path, k ->
	let res_sl, res_il, res_i, res_cstr, res_p 
	    = down_prods (kind_of_term body, path, k+1) in
	x::res_sl, (k::res_il), res_i, res_cstr, res_p
   | Prod(Anonymous, _, body), 2::path, k ->
        let res_sl, res_il, res_i, res_cstr, res_p 
	    = down_prods (kind_of_term body, path, k+1) in
	res_sl, res_il, res_i+1, res_cstr, res_p
   | cstr, path, _ -> [], [], 0, cstr, path;;

exception Pbp_internal of int list;;

(* This function should be usable to check that a type can be used by the
   Apply command.  Basically, c is supposed to be the head of some
   type, where l gives the ranks of all universally quantified variables.
   It check that these universally quantified variables occur in the head.

   The knowledge I have on constr structures is incomplete.
*)
let (check_apply: (types, constr) kind_of_term -> (int list) -> bool) = 
   function c -> function l ->
   let rec delete n = function
     | [] -> []
     | p::tl -> if n = p then tl else p::(delete n tl) in
   let rec check_rec l = function
   | App(f, array) ->
       Array.fold_left (fun l c -> check_rec l (kind_of_term c))
	 (check_rec l (kind_of_term f)) array
   | Const _ -> l
   | Ind _ -> l
   | Construct _ -> l
   | Var _ -> l
   | Rel p ->
       let result = delete p l in
       if result = [] then
	 raise (Pbp_internal [])
       else
	 result
   | _ -> raise (Pbp_internal l) in
   try 
     (check_rec l c) = []
   with Pbp_internal l -> l = [];;

let (mk_db_indices: int list -> int -> int list) =
  function int_list -> function nprems ->
   let total = (List.length int_list) + nprems  in
   let rec mk_db_aux = function
     [] -> []
   | a::l -> (total - a)::(mk_db_aux l) in
   mk_db_aux int_list;;
     

(* This proof-by-pointing rule is quite complicated, as it attempts to foresee
   usages of head tactics.  A first operation is to follow the path as far
   as possible while staying on the spine of products (function down_prods)
   and then to check whether the next step will be an elim step.  If the 
   answer is true, then the built command takes advantage of the power of
   head tactics.  *)

(*
let (head_tactic_patt: pbp_rule) = function
    avoid, clear_names, clear_flag, Some h, cstr, path, f ->
    (match down_prods (cstr, path, 0) with
    | (str_list, _, nprems, 
       App(oper,[|c1|]), 2::1::path) 
      	when
 	  (is_matching_local (notconstr ()) oper) or
 	  (is_matching_local (notTconstr ()) oper) ->
	 Some(Node(zz, "TACTICLIST",
		   [elim_with_bindings h str_list;
		     f avoid clear_names false None (kind_of_term c1) path]))
    | (str_list, _, nprems, 
       App(oper, [|c1; c2|]), 2::a::path) 
      when ((is_matching_local (andconstr()) oper) or
	    (is_matching_local (prodconstr()) oper)) & (a = 1 or a = 2) ->
	let h1 = next_global_ident_away (id_of_string "H") avoid in
	let str_h1 = (string_of_id h1) in
	let h2 = next_global_ident_away (id_of_string "H") (h1::avoid) in
	let str_h2 = (string_of_id h2) in
	Some(Node(zz,"TACTICLIST",
                  [elim_with_bindings h str_list;
		    make_named_intro str_h1;
		    make_named_intro str_h2;
		    let cont_body = 
		      if a = 1 then c1 else c2 in
		    let cont_tac = 
		      f (h2::h1::avoid) (h::clear_names) 
                        false (Some (if 1 = a then str_h1 else str_h2))
                        (kind_of_term cont_body) path in
		    if nprems = 0 then
		      cont_tac
		    else
		      Node(zz,"TACLIST",
			   cont_tac::(auxiliary_goals
					clear_names clear_flag
					h nprems))]))
    | (str_list, _, nprems, App(oper,[|c1; c2|]), 2::a::path)
      when ((is_matching_local (exconstr ()) oper) or
	    (is_matching_local (exTconstr ()) oper) or
	    (is_matching_local (sigconstr ()) oper) or
	    (is_matching_local (sigTconstr()) oper)) & a = 2 ->
		   (match (kind_of_term c2),path with
		     Lambda(Name x, _,body), (2::path) ->
		       Some(Node(zz,"TACTICLIST",
		    		 [elim_with_bindings h str_list;
				   let x' = next_global_ident_away x avoid in
				   let cont_body =
				     Prod(Name x', c1,
					    mkProd(Anonymous, body, 
						   mkVar(dummy_id))) in
				   let cont_tac 
				       = f avoid (h::clear_names) false None
				       cont_body (2::1::path) in
				   if nprems = 0 then
				     cont_tac
				   else
				     Node(zz,"TACLIST",
					  cont_tac::(auxiliary_goals
						       clear_names clear_flag
						       h nprems))]))
		   | _ -> None)
    | (str_list, _, nprems, App(oper,[|c1; c2|]), 2::a::path)
	when ((is_matching_local (orconstr ()) oper) or
              (is_matching_local (sumboolconstr ()) oper) or
	      (is_matching_local (sumconstr ()) oper)) &
                (a = 1 or a = 2) ->
	  Some(Node(zz, "TACTICLIST",
		    [elim_with_bindings h str_list;
		      let cont_body =
			if a = 1 then c1 else c2 in
                      (* h' is the name for the new intro *)
		      let h' = next_global_ident_away (id_of_string "H") avoid in
		      let str_h' = (string_of_id h') in
		      let cont_tac =
                        Node(zz,"TACTICLIST",
			     [make_named_intro str_h';
			       f 
				 (* h' should not be used again *)
				 (h'::avoid)
				 (* the disjunct itself can be discarded *)
				 (h::clear_names) false (Some str_h')
                          (kind_of_term cont_body) path]) in
		      let snd_tac = 
			Node(zz, "TACTICLIST", 
			     [make_named_intro str_h';
			       make_clears (h::clear_names)]) in
		      let tacs1 = 
			if a = 1 then
			  [cont_tac; snd_tac]
		      	else
			  [snd_tac; cont_tac] in
		      Node(zz,"TACLIST",
			   tacs1@(auxiliary_goals (h::clear_names)
				   false "dummy" nprems))]))
    | (str_list, int_list, nprems, c, []) 
        when  (check_apply c (mk_db_indices int_list nprems)) &
              (match c with Prod(_,_,_) -> false
              |  _ -> true) &
              (List.length int_list) + nprems > 0 ->
          Some(add_clear_names_if_necessary
	     (Node(zz,"Apply", [Node(zz,"COMMAND",[Nvar(zz, h)]);
			     Node(zz,"BINDINGS", [])]))
             clear_names)
    | _ -> None)
  | _ -> None;;
*)

let (head_tactic_patt: pbp_rule) = function
    avoid, clear_names, clear_flag, Some h, cstr, path, f ->
    (match down_prods (cstr, path, 0) with
    | (str_list, _, nprems, 
       App(oper,[|c1|]), 2::1::path) 
      	when
 	  (is_matching_local (notconstr ()) oper) or
 	  (is_matching_local (notTconstr ()) oper) ->
	 Some(chain_tactics [elim_with_bindings h str_list]
		 (f avoid clear_names false None (kind_of_term c1) path))
    | (str_list, _, nprems, 
       App(oper, [|c1; c2|]), 2::a::path) 
      when ((is_matching_local (andconstr()) oper) or
	    (is_matching_local (prodconstr()) oper)) & (a = 1 or a = 2) ->
	let h1 = next_global_ident_away (id_of_string "H") avoid in
	let h2 = next_global_ident_away (id_of_string "H") (h1::avoid) in
	Some(PbpThens
                  ([elim_with_bindings h str_list;
		    make_named_intro h1;
		    make_named_intro h2],
		    let cont_body = 
		      if a = 1 then c1 else c2 in
		    let cont_tac = 
		      f (h2::h1::avoid) (h::clear_names) 
                        false (Some (if 1 = a then h1 else h2))
                        (kind_of_term cont_body) path in
		    cont_tac::(auxiliary_goals
					clear_names clear_flag
					h nprems)))
    | (str_list, _, nprems, App(oper,[|c1; c2|]), 2::a::path)
      when ((is_matching_local (exconstr ()) oper) or
	    (is_matching_local (exTconstr ()) oper) or
	    (is_matching_local (sigconstr ()) oper) or
	    (is_matching_local (sigTconstr()) oper)) & a = 2 ->
		   (match (kind_of_term c2),path with
		     Lambda(Name x, _,body), (2::path) ->
		       Some(PbpThens
		    		 ([elim_with_bindings h str_list],
				   let x' = next_global_ident_away x avoid in
				   let cont_body =
				     Prod(Name x', c1,
					    mkProd(Anonymous, body, 
						   mkVar(dummy_id))) in
				   let cont_tac 
				       = f avoid (h::clear_names) false None
				       cont_body (2::1::path) in
				   cont_tac::(auxiliary_goals
						       clear_names clear_flag
						       h nprems)))
		     | _ -> None)
    | (str_list, _, nprems, App(oper,[|c1; c2|]), 2::a::path)
	when ((is_matching_local (orconstr ()) oper) or
              (is_matching_local (sumboolconstr ()) oper) or
	      (is_matching_local (sumconstr ()) oper)) &
                (a = 1 or a = 2) ->
	  Some(PbpThens
		    ([elim_with_bindings h str_list],
		      let cont_body =
			if a = 1 then c1 else c2 in
                      (* h' is the name for the new intro *)
		      let h' = next_global_ident_away (id_of_string "H") avoid in
		      let cont_tac =
                        chain_tactics 
			  [make_named_intro h']
			  (f 
			     (* h' should not be used again *)
			     (h'::avoid)
			     (* the disjunct itself can be discarded *)
			     (h::clear_names) false (Some h')
                             (kind_of_term cont_body) path) in
		      let snd_tac = 
			chain_tactics
			   [make_named_intro h']
			   (make_clears (h::clear_names)) in
		      let tacs1 = 
			if a = 1 then
			  [cont_tac; snd_tac]
		      	else
			  [snd_tac; cont_tac] in
		      tacs1@(auxiliary_goals (h::clear_names)
				   false dummy_id nprems)))
    | (str_list, int_list, nprems, c, []) 
        when  (check_apply c (mk_db_indices int_list nprems)) &
              (match c with Prod(_,_,_) -> false
              |  _ -> true) &
              (List.length int_list) + nprems > 0 ->
          Some(add_clear_names_if_necessary (PbpThen [PbpApply h]) clear_names)
    | _ -> None)
  | _ -> None;;
      

let pbp_rules = ref [rem_cast;head_tactic_patt;forall_intro;imply_intro2;
                      forall_elim; imply_intro1; imply_elim1; imply_elim2;
		      and_intro; or_intro; not_intro; ex_intro];;


(* The tactic traced_try was intended to be used in tactics instead of
   Try, with an argument  Node(zz, "TACTIC", [b]) where b is the tactic to
   try.  However, the current design is not very robust to the fact that
   Traced_Try may occur several times in the executed command! *)

let try_trace = ref true;;

let traced_try (f1:tactic) g =
    try (try_trace := true; tclPROGRESS f1 g)
    with e when Logic.catchable_exception e ->
      (try_trace := false; tclIDTAC g);;

let traced_try_entry = function
     [Tacexp t] ->
           traced_try (Tacinterp.interp t)
  |  _ -> failwith "traced_try_entry received wrong arguments";;


let rec clean_trace flag =
      function
          Node(a,"Traced_Try", [Node(_,_,[b])]) ->
             if flag then b else Node(zz,"Idtac",[])
      	| Node(a,b,c) -> Node(a,b,List.map (clean_trace flag) c)
        | t -> t;;

(* When the recursive descent along the path is over, one includes the
   command requested by the point-and-shoot strategy.  Default is
   Try Assumption--Try Exact.  *)

(*
let default_ast optname constr path =
      match optname with
        None ->  Node(zz, "TRY", [Node(zz, "Assumption",[])])
      | Some(a) -> Node(zz, "TRY", 
                   [Node(zz, "Exact",[Node(zz,"COMMAND",[Nvar(zz,a)])])]);;
*)

let default_ast optname constr path = PbpThen [PbpTryAssumption optname]

(* This is the main proof by pointing function. *)
(* avoid: les noms a ne pas utiliser *)
(* final_cmd: la fonction appelee par defaut *)
(* opt_name: eventuellement le nom de l'hypothese sur laquelle on agit *)

let rec pbpt final_cmd avoid clear_names clear_flag opt_name constr path =
  let rec try_all_rules rl =
      match rl with 
         f::tl ->
           (match f (avoid, clear_names, clear_flag,
                     opt_name, constr, path, pbpt final_cmd) with
              Some(ast) -> ast
            | None -> try_all_rules tl)
      |	 [] -> make_final_cmd final_cmd opt_name clear_names constr path
  in try_all_rules (!pbp_rules);;

(* these are the optimisation functions. *)
(* This function takes care of flattening successive then commands. *)

(*
let rec optim1 =
    function
        Node(a,"TACTICLIST",b) ->
          let tacs = List.map optim1 b in
          let rec flatten = function
            | [Node(a, "TACTICLIST", b')] ->
                let rec last = function
                    [] -> failwith "function last is called on an empty list"
		  | [b] -> b
		  | a::b -> last b in
		(match last b' with
		  Node(a, "TACLIST",_) -> [Node(a,"TACTICLIST", b')]
		| _ -> flatten b')
            | Node(a, "TACTICLIST", b')::others -> List.append (flatten b')
                                                       (flatten others)
            | Node(a, "Idtac",[])::others -> (flatten others)
            | [Node(a, "TACLIST",tacs)] ->
                 [Node(a, "TACLIST", List.map optim1 tacs)]
            | t1::others -> t1::(flatten others)
            | [] -> [] in
          (match (flatten tacs) with
            [] -> Node(zz,"Idtac", [])
          | [t] -> t
          | args -> Node(zz,"TACTICLIST", args))
      |	t -> t;;
*)

(* Invariant: in [flatten_sequence t], occurrences of [PbpThenCont(l,t)] enjoy
    that t is some [PbpAtom t] *)
(*
let rec flatten_sequence =
  function
      PbpThens (tl1,tl2) -> PbpThens (tl1,List.map flatten_sequence tl2)
    | PbpThen (tl1,t1) as x ->
	(match flatten_sequence t1 with
	  | PbpThenCont (tl2,t2) -> PbpThenCont (tl1@tl2,t2)
	  | PbpThens (tl2,tl3) -> PbpThens (tl1@tl2,tl3)
	  | PbpAtom _ -> x)
    | PbpAtom t as x -> x;;
*)

(* This optimization function takes care of compacting successive Intro commands
   together. *)
(*
let rec optim2 =
    function
	Node(a,"TACTICLIST",b) ->
         let get_ids = 
           List.map (function Node(_,"IDENTIFIER", [Nvar(_,s)])->s
             | Node(_,s,_) -> (failwith "unexpected node " ^ s)
             |  _ -> failwith "get_ids expected an identifier") in
         let put_ids ids =
           Node(zz,"Intros",
               	[Node(zz,"INTROPATTERN",
		      [Node(zz,"LISTPATTERN", 
			    List.map 
			      (function s -> Node(zz,"IDENTIFIER",[Nvar(zz,s)]))
			      ids)])]) in
         let rec group_intros names = function
             [] -> (match names with
               [] -> []
	     | l -> [put_ids l])
           | Node(_,"Intros", 
		  [Node(_,"INTROPATTERN",[Node(_,"LISTPATTERN", ids)])])::others ->
		    group_intros (names@(get_ids ids)) others
           | [Node(a,"TACLIST",b')] ->
	       [Node(a,"TACLIST", List.map optim2 b')]
           | t1::others -> 
	       (match names with
		 [] -> t1::(group_intros [] others)
	       | l -> (put_ids l)::t1::(group_intros [] others)) in
	 Node(a,"TACTICLIST",group_intros [] b)
   | t -> t;;
*)
(*
let rec optim2 = function
  | TacThens (t,tl) -> TacThens (optim2 t, List.map optim2 tl)
  | t ->
      let get_ids = 
	List.map (function IntroIdentifier _ as x -> x
	  |  _ -> failwith "get_ids expected an identifier") in
      let rec group_intros names = function
	  [] -> (match names with
              [] -> []
	    | l -> [TacIntroPattern l])
	| (TacIntroPattern ids)::others ->
	    group_intros (names@(get_ids ids)) others
	| t1::others -> 
	    (match names with
		[] -> t1::(group_intros [] others)
	      | l -> (TacIntroPattern l)::t1::(group_intros [] others)) in
      make_then (group_intros [] (flatten_sequence t))
*)

let rec group_intros names = function
    [] -> (match names with
        [] -> []
      | l -> [PbpIntros l])
  | (PbpIntros ids)::others -> group_intros (names@ids) others
  | t1::others ->
      (match names with
	  [] -> t1::(group_intros [] others)
	| l -> (PbpIntros l)::t1::(group_intros [] others))

let rec optim2 = function
  | PbpThens (tl1,tl2) -> PbpThens (group_intros [] tl1, List.map optim2 tl2)
  | PbpThen tl -> PbpThen (group_intros [] tl)

(*
let rec merge_ast_in_command com1 com2 =
    let args1 =
     (match com1 with
	Node(_, "APPLIST", args) -> args
     | _ -> failwith "unexpected com1 in merge_ast_in_command") in
    let args2 =
     (match com2 with
        Node(_, "APPLIST", hyp::args) -> args
     | _ -> failwith "unexpected com2 in merge_ast_in_command") in
      Node(zz, "COMMAND", [Node(zz, "APPLIST", args1@args2)]);;
*)
(*
let cleanup_clears empty_allowed names str_list other =
  let rec clean_aux = function
      [] -> []
    | (Nvar(_,x) as fst_one)::tail ->
      if List.mem x str_list then
         clean_aux tail
      else
         fst_one::(clean_aux tail)
    | _ -> failwith "unexpected argument in clean_aux" in
  match clean_aux names with
    [] -> (match other with 
            [] -> 
	      if empty_allowed then
		[]
	      else [Node(zz,"Idtac",[])]
          | _ -> other)
  | l -> Node(zz, "TRY", [Node(zz, "Clear", [Node(zz,"CLAUSE", l)])])::other;;
*)
let rec cleanup_clears str_list = function
    [] -> []
  | x::tail ->
      if List.mem x str_list then cleanup_clears str_list tail
      else x::(cleanup_clears str_list tail);;

(* This function takes care of compacting instanciations of universal
   quantifications. *)

let rec optim3_aux str_list = function
    (PbpGeneralize (h,l1))::(PbpIntros [s])::(PbpGeneralize (h',l2))::others
      when s=h' ->
      optim3_aux (s::str_list) (PbpGeneralize (h,l1@l2)::others)
  | (PbpTryClear names)::other ->
      (match cleanup_clears str_list names with
	  [] -> other
	| l -> (PbpTryClear l)::other)
  | a::l -> a::(optim3_aux str_list l) 
  | [] -> [];;

let rec optim3 str_list = function
    PbpThens (tl1, tl2) ->
      PbpThens (optim3_aux str_list tl1, List.map (optim3 str_list) tl2)
  | PbpThen tl -> PbpThen (optim3_aux str_list tl)

let optim x = make_pbp_tactic (optim3 [] (optim2 x));;

(* TODO
add_tactic "Traced_Try" traced_try_entry;;
*)

let rec tactic_args_to_ints = function
    [] -> []
  | (Integer n)::l -> n::(tactic_args_to_ints l)
  | _ -> failwith "expecting only numbers";;

(*
let pbp_tac display_function = function 
            (Identifier a)::l -> 
                 (function g ->
                    let str = (string_of_id a) in
		    let (ou,tstr) = (get_hyp_by_name g str) in
		    let exp_ast =
		      pbpt default_ast
		        (match ou with
			       "hyp" ->(pf_ids_of_hyps g)
			       |_ -> (a::(pf_ids_of_hyps g)))
                        []
			false
			(Some str)
			(kind_of_term tstr)
                        (tactic_args_to_ints l) in
                    (display_function (optim exp_ast);
                        tclIDTAC g))
          | ((Integer n)::_) as l -> 
                 (function g ->
                    let exp_ast =
                       (pbpt default_ast (pf_ids_of_hyps g) [] false
                          None (kind_of_term (pf_concl g))
			  (tactic_args_to_ints l)) in
                     (display_function (optim exp_ast);
                       tclIDTAC g))
          | [] -> (function g ->
                     (display_function (default_ast None (pf_concl g) []);
                      tclIDTAC g))
          |  _ -> failwith "expecting other arguments";;


*)
let pbp_tac display_function idopt nl =
  match idopt with
    | Some str ->
        (function g ->
	  let (ou,tstr) = (get_hyp_by_name g str) in
	  let exp_ast =
	    pbpt default_ast
	      (match ou with
		  "hyp" ->(pf_ids_of_hyps g)
		|_ -> (str::(pf_ids_of_hyps g)))
              []
	      false
	      (Some str)
	      (kind_of_term tstr)
              nl in
              (display_function (optim exp_ast); tclIDTAC g))
    | None ->
	if nl <> [] then
          (function g ->
            let exp_ast =
              (pbpt default_ast (pf_ids_of_hyps g) [] false
		None (kind_of_term (pf_concl g)) nl) in
            (display_function (optim exp_ast); tclIDTAC g))
	else
          (function g ->
            (display_function
	       (make_pbp_tactic (default_ast None (pf_concl g) []));
            tclIDTAC g));;


