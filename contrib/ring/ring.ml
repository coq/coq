
(* $Id$ *)

(* ML part of the Ring tactic *)

open Pp
open Util
open Term
open Names
open Reduction
open Tacmach
open Proof_type
open Proof_trees
open Printer
open Equality
open Vernacinterp
open Libobject
open Closure
open Tacred
open Tactics
open Pattern 
open Hiddentac
open Quote

let mt_evd = Evd.empty
let constr_of com = Astterm.interp_constr mt_evd (Global.env()) com

let constant sp id = 
  Declare.global_sp_reference (path_of_string sp) (id_of_string id)

(* Ring_theory *)

let coq_Ring_Theory = 
  lazy (constant "#Ring_theory#Ring_Theory.cci" "Ring_Theory")
let coq_Semi_Ring_Theory = 
  lazy (constant "#Ring_theory#Semi_Ring_Theory.cci" "Semi_Ring_Theory")

(* Ring_normalize *)
let coq_SPplus = lazy (constant "#Ring_normalize#spolynomial.cci" "SPplus")
let coq_SPmult = lazy (constant "#Ring_normalize#spolynomial.cci" "SPmult")
let coq_SPvar = lazy (constant "#Ring_normalize#spolynomial.cci" "SPvar")
let coq_SPconst = lazy (constant "#Ring_normalize#spolynomial.cci" "SPconst")
let coq_Pplus = lazy (constant "#Ring_normalize#polynomial.cci" "Pplus")
let coq_Pmult = lazy (constant "#Ring_normalize#polynomial.cci" "Pmult")
let coq_Pvar = lazy (constant "#Ring_normalize#polynomial.cci" "Pvar")
let coq_Pconst = lazy (constant "#Ring_normalize#polynomial.cci" "Pconst")
let coq_Popp = lazy (constant "#Ring_normalize#polynomial.cci" "Popp")
let coq_interp_sp = lazy (constant "#Ring_normalize#interp_sp.cci" "interp_sp")
let coq_interp_p = lazy (constant "#Ring_normalize#interp_p.cci" "interp_p")
let coq_interp_cs = lazy (constant "#Ring_normalize#interp_cs.cci" "interp_cs")
let coq_spolynomial_simplify = 
  lazy (constant "#Ring_normalize#spolynomial_simplify.cci" 
	  "spolynomial_simplify")
let coq_polynomial_simplify = 
  lazy (constant "#Ring_normalize#polynomial_simplify.cci"
	  "polynomial_simplify")
let coq_spolynomial_simplify_ok = 
  lazy (constant "#Ring_normalize#spolynomial_simplify_ok.cci"
	  "spolynomial_simplify_ok")
let coq_polynomial_simplify_ok = 
  lazy (constant "#Ring_normalize#polynomial_simplify_ok.cci"
	  "polynomial_simplify_ok")

(* Ring_abstract *)
let coq_ASPplus = lazy (constant "#Ring_abstract#aspolynomial.cci" "ASPplus")
let coq_ASPmult = lazy (constant "#Ring_abstract#aspolynomial.cci" "ASPmult")
let coq_ASPvar = lazy (constant "#Ring_abstract#aspolynomial.cci" "ASPvar")
let coq_ASP0 = lazy (constant "#Ring_abstract#aspolynomial.cci" "ASP0")
let coq_ASP1 = lazy (constant "#Ring_abstract#aspolynomial.cci" "ASP1")
let coq_APplus = lazy (constant "#Ring_abstract#apolynomial.cci" "APplus")
let coq_APmult = lazy (constant "#Ring_abstract#apolynomial.cci" "APmult")
let coq_APvar = lazy (constant "#Ring_abstract#apolynomial.cci" "APvar")
let coq_AP0 = lazy (constant "#Ring_abstract#apolynomial.cci" "AP0")
let coq_AP1 = lazy (constant "#Ring_abstract#apolynomial.cci" "AP1")
let coq_APopp = lazy (constant "#Ring_abstract#apolynomial.cci" "APopp")
let coq_interp_asp = 
  lazy (constant "#Ring_abstract#interp_asp.cci" "interp_asp")
let coq_interp_ap = 
  lazy (constant "#Ring_abstract#interp_ap.cci" "interp_ap")
 let coq_interp_acs = 
  lazy (constant "#Ring_abstract#interp_acs.cci" "interp_acs")
let coq_interp_sacs = 
  lazy (constant "#Ring_abstract#interp_sacs.cci" "interp_sacs")
let coq_aspolynomial_normalize = 
  lazy (constant "#Ring_abstract#aspolynomial_normalize.cci"
	  "aspolynomial_normalize")
let coq_apolynomial_normalize = 
  lazy (constant "#Ring_abstract#apolynomial_normalize.cci"
	  "apolynomial_normalize")
let coq_aspolynomial_normalize_ok = 
  lazy (constant "#Ring_abstract#aspolynomial_normalize_ok.cci" 
	  "aspolynomial_normalize_ok")
let coq_apolynomial_normalize_ok = 
  lazy (constant "#Ring_abstract#apolynomial_normalize_ok.cci"
	  "apolynomial_simplify_ok")

(* Logic *)
let coq_f_equal2 = lazy (constant "#Logic#f_equal2.cci" "f_equal2")
let coq_eq = lazy (constant "#Logic#eq.cci" "eq")
let coq_eqT = lazy (constant "#Logic_Type#eqT.cci" "eqT")

(*********** Useful types and functions ************)

module OperSet = 
  Set.Make (struct 
	      type t = global_reference
	      let compare = (Pervasives.compare : t->t->int)
	    end)	

type theory =
    { th_ring : bool;                  (* false for a semi-ring *)
      th_abstract : bool;
      th_a : constr;                   (* e.g. nat *)
      th_plus : constr;
      th_mult : constr;
      th_one : constr;
      th_zero : constr;
      th_opp : constr;                 (* Not used if semi-ring *)
      th_eq : constr;
      th_t : constr;                   (* e.g. NatTheory *)
      th_closed : ConstrSet.t;         (* e.g. [S; O] *)
                                       (* Must be empty for an abstract ring *)
    }

(* Theories are stored in a table which is synchronised with the Reset 
   mechanism. *)

module Cmap = Map.Make(struct type t = constr let compare = compare end)

let theories_map = ref Cmap.empty

let theories_map_add (c,t) = theories_map := Cmap.add c t !theories_map
let theories_map_find c = Cmap.find c !theories_map
let theories_map_mem c = Cmap.mem c !theories_map

let _ = 
  Summary.declare_summary "tactic-ring-table"
    { Summary.freeze_function = (fun () -> !theories_map);
      Summary.unfreeze_function = (fun t -> theories_map := t);
      Summary.init_function = (fun () -> theories_map := Cmap.empty) }

(* declare a new type of object in the environment, "tactic-ring-theory"
   The functions theory_to_obj and obj_to_theory do the conversions
   between theories and environement objects. *)

let (theory_to_obj, obj_to_theory) = 
  let cache_th (_,(c, th)) = theories_map_add (c,th)
  and spec_th x = x in
  declare_object ("tactic-ring-theory",
		  { load_function = cache_th;
		    open_function = (fun _ -> ());
                    cache_function = cache_th;
		    specification_function = spec_th })

(* from the set A, guess the associated theory *)
(* With this simple solution, the theory to use is automatically guessed *)
(* But only one theory can be declared for a given Set *)

let guess_theory a =
  try 
    theories_map_find a
  with Not_found -> 
    errorlabstrm "Ring" 
      [< 'sTR "No Declared Ring Theory for ";
	 prterm a; 'fNL;
	 'sTR "Use Add [Semi] Ring to declare it">]

(* Add a Ring or a Semi-Ring to the database after a type verification *)

let add_theory want_ring want_abstract a aplus amult aone azero aopp aeq t cset = 
  if theories_map_mem a then errorlabstrm "Add Semi Ring" 
    [< 'sTR "A (Semi-)Ring Structure is already declared for "; prterm a >];
  let env = Global.env () in
  if (want_ring & 
      not (is_conv env Evd.empty (Typing.type_of env Evd.empty t)
	     (mkApp (Lazy.force coq_Ring_Theory, [| a; aplus; amult;
			aone; azero; aopp; aeq |])))) then
    errorlabstrm "addring" [< 'sTR "Not a valid Ring theory" >];
  if (not want_ring &
      not (is_conv  env Evd.empty (Typing.type_of env Evd.empty t) 
	     (mkApp (Lazy.force coq_Semi_Ring_Theory, [| a; 
			aplus; amult; aone; azero; aeq |])))) then 
    errorlabstrm "addring" [< 'sTR "Not a valid Semi-Ring theory" >];
  Lib.add_anonymous_leaf
    (theory_to_obj 
       (a, { th_ring = want_ring;
	     th_abstract = want_abstract;
	     th_a = a;
	     th_plus = aplus;
	     th_mult = amult;
	     th_one = aone;
	     th_zero = azero;
	     th_opp = aopp;
	     th_eq = aeq;
	     th_t = t;
	     th_closed = cset }))

(* The vernac commands "Add Ring" and "Add Semi Ring" *)
(* see file Ring.v for examples of this command *)

let constr_of_comarg = function 
  | VARG_CONSTR c -> constr_of c
  | _ -> anomaly "Add (Semi) Ring"
  
let cset_of_comarg_list l = 
  List.fold_right ConstrSet.add (List.map constr_of_comarg l) ConstrSet.empty

let _ = 
  vinterp_add "AddSemiRing"
    (function
       | (VARG_CONSTR a)::(VARG_CONSTR aplus)::(VARG_CONSTR amult)
	 ::(VARG_CONSTR aone)::(VARG_CONSTR azero)::(VARG_CONSTR aeq)
	 ::(VARG_CONSTR t)::l -> 
	   (fun () -> (add_theory false false
			 (constr_of a)
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (mkXtra "not a term")
			 (constr_of aeq)
			 (constr_of t)
			 (cset_of_comarg_list l)))
       | _ -> anomaly "AddSemiRing")

let _ = 
  vinterp_add "AddRing"
    (function 
       | (VARG_CONSTR a)::(VARG_CONSTR aplus)::(VARG_CONSTR amult)
	 ::(VARG_CONSTR aone)::(VARG_CONSTR azero)::(VARG_CONSTR aopp)
	 ::(VARG_CONSTR aeq)::(VARG_CONSTR t)::l -> 
	   (fun () -> (add_theory true false
			 (constr_of a)
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (constr_of aopp)
			 (constr_of aeq)
			 (constr_of t)
			 (cset_of_comarg_list l)))
       | _ -> anomaly "AddRing")
    
let _ = 
  vinterp_add "AddAbstractSemiRing"
    (function 
       | [VARG_CONSTR a; VARG_CONSTR aplus; 
	  VARG_CONSTR amult; VARG_CONSTR aone;
	  VARG_CONSTR azero; VARG_CONSTR aeq; VARG_CONSTR t] -> 
	   (fun () -> (add_theory false false
			 (constr_of a)
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (mkXtra "not a term")
			 (constr_of aeq)
			 (constr_of t)
			 ConstrSet.empty))
       | _ -> anomaly "AddAbstractSemiRing")
    
let _ = 
  vinterp_add "AddAbstractRing"
    (function 
       | [ VARG_CONSTR a; VARG_CONSTR aplus; 
	   VARG_CONSTR amult; VARG_CONSTR aone;
	   VARG_CONSTR azero; VARG_CONSTR aopp; 
	   VARG_CONSTR aeq; VARG_CONSTR t ] -> 
	   (fun () -> (add_theory true true
			 (constr_of a)
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (constr_of aopp)
			 (constr_of aeq)
			 (constr_of t)
			 ConstrSet.empty))
       | _ -> anomaly "AddAbstractRing")
    
(******** The tactic itself *********)

(*
   gl : goal sigma
   th : semi-ring theory (concrete)
   cl : constr list [c1; c2; ...]
 
Builds 
   - a list of tuples [(c1, c'1, c''1, c'1_eq_c''1); ... ] 
  where c'i is convertible with ci and
  c'i_eq_c''i is a proof of equality of c'i and c''i

*)

let build_spolynom gl th lc =
  let varhash  = (Hashtbl.create 17 : (constr, constr) Hashtbl.t) in
  let varlist = ref ([] : constr list) in (* list of variables *)
  let counter = ref 1 in (* number of variables created + 1 *)
  (* aux creates the spolynom p by a recursive destructuration of c 
     and builds the varmap with side-effects *)
  let rec aux c = 
    match (kind_of_term (strip_outer_cast c)) with 
      | IsApp (binop,[|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkAppA [| Lazy.force coq_SPplus; th.th_a; aux c1; aux c2 |]
      | IsApp (binop,[|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkAppA [| Lazy.force coq_SPmult; th.th_a; aux c1; aux c2 |]
      | _ when closed_under th.th_closed c ->
	  mkAppA [| Lazy.force coq_SPconst; th.th_a; c |]
      | _ -> 
	  try Hashtbl.find varhash c 
	  with Not_found -> 
	    let newvar = mkAppA [| Lazy.force coq_SPvar; th.th_a; 
				   (path_of_int !counter) |] in
	    begin 
	      incr counter;
	      varlist := c :: !varlist;
	      Hashtbl.add varhash c newvar;
	      newvar
	    end
  in 
  let lp = List.map aux lc in
  let v = btree_of_array (Array.of_list (List.rev !varlist)) th.th_a in
  List.map 
    (fun p -> 
       (mkAppA [| Lazy.force coq_interp_sp; th.th_a; th.th_plus; th.th_mult; 
		  th.th_zero; v; p |],
	mkAppA [| Lazy.force coq_interp_cs; th.th_a; th.th_plus; th.th_mult; 
		  th.th_one; th.th_zero; v;
		  pf_reduce cbv_betadeltaiota gl 
		    (mkAppA [| Lazy.force coq_spolynomial_simplify; 
			       th.th_a; th.th_plus; th.th_mult; 
			       th.th_one; th.th_zero; 
			       th.th_eq; p|]) |],
	mkAppA [| Lazy.force coq_spolynomial_simplify_ok;
		  th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; 
		  th.th_eq; v; th.th_t; p |]))
    lp

(*
   gl : goal sigma
   th : ring theory (concrete)
   cl : constr list [c1; c2; ...]
 
Builds 
   - a list of tuples [(c1, c'1, c''1, c'1_eq_c''1); ... ] 
  where c'i is convertible with ci and
  c'i_eq_c''i is a proof of equality of c'i and c''i

*)

let build_polynom gl th lc =
  let varhash  = (Hashtbl.create 17 : (constr, constr) Hashtbl.t) in
  let varlist = ref ([] : constr list) in (* list of variables *)
  let counter = ref 1 in (* number of variables created + 1 *)
  let rec aux c = 
    match (kind_of_term (strip_outer_cast c)) with 
      | IsApp (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkAppA [| Lazy.force coq_Pplus; th.th_a; aux c1; aux c2 |]
      | IsApp (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkAppA [| Lazy.force coq_Pmult; th.th_a; aux c1; aux c2 |]
      (* The special case of Zminus *)
      | IsApp (binop, [|c1; c2|])
	  when pf_conv_x gl c (mkAppA [| th.th_plus; c1; 
	                                 mkAppA [| th.th_opp; c2 |] |]) ->
	    mkAppA [| Lazy.force coq_Pplus; th.th_a; aux c1;
	              mkAppA [| Lazy.force coq_Popp; th.th_a; aux c2 |] |]
      | IsApp (unop, [|c1|]) when pf_conv_x gl unop th.th_opp ->
	  mkAppA [| Lazy.force coq_Popp; th.th_a; aux c1 |]
      | _ when closed_under th.th_closed c ->
	  mkAppA [| Lazy.force coq_Pconst; th.th_a; c |]
      | _ -> 
	  try Hashtbl.find varhash c 
	  with Not_found -> 
	    let newvar = mkAppA [| Lazy.force coq_Pvar; th.th_a; 
				   (path_of_int !counter) |] in
	    begin 
	      incr counter;
	      varlist := c :: !varlist;
	      Hashtbl.add varhash c newvar;
	      newvar
	    end
  in
  let lp = List.map aux lc in
  let v = (btree_of_array (Array.of_list (List.rev !varlist)) th.th_a) in
  List.map 
    (fun p -> 
       (mkAppA [| Lazy.force coq_interp_p;
		  th.th_a; th.th_plus; th.th_mult; th.th_zero; th.th_opp;
		  v; p |],
	mkAppA [| Lazy.force coq_interp_cs;
		  th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; v;
		  pf_reduce cbv_betadeltaiota gl 
		    (mkAppA [| Lazy.force coq_polynomial_simplify; 
			       th.th_a; th.th_plus; th.th_mult; 
			       th.th_one; th.th_zero; 
			       th.th_opp; th.th_eq; p |]) |],
	mkAppA [| Lazy.force coq_polynomial_simplify_ok;
		  th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; 
		  th.th_opp; th.th_eq; v; th.th_t; p |]))
    lp

(*
   gl : goal sigma
   th : semi-ring theory (abstract)
   cl : constr list [c1; c2; ...]
 
Builds 
   - a list of tuples [(c1, c'1, c''1, c'1_eq_c''1); ... ] 
  where c'i is convertible with ci and
  c'i_eq_c''i is a proof of equality of c'i and c''i

*)

let build_aspolynom gl th lc =
  let varhash  = (Hashtbl.create 17 : (constr, constr) Hashtbl.t) in
  let varlist = ref ([] : constr list) in (* list of variables *)
  let counter = ref 1 in (* number of variables created + 1 *)
  (* aux creates the aspolynom p by a recursive destructuration of c 
     and builds the varmap with side-effects *)
  let rec aux c = 
    match (kind_of_term (strip_outer_cast c)) with 
      | IsApp (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkAppA [| Lazy.force coq_ASPplus; aux c1; aux c2 |]
      | IsApp (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkAppA [| Lazy.force coq_ASPmult; aux c1; aux c2 |]
      | _ when pf_conv_x gl c th.th_zero -> Lazy.force coq_ASP0
      | _ when pf_conv_x gl c th.th_one -> Lazy.force coq_ASP1
      | _ -> 
	  try Hashtbl.find varhash c 
	  with Not_found -> 
	    let newvar = mkAppA [| Lazy.force coq_ASPvar; 
				   (path_of_int !counter) |] in
	    begin 
	      incr counter;
	      varlist := c :: !varlist;
	      Hashtbl.add varhash c newvar;
	      newvar
	    end
  in 
  let lp = List.map aux lc in
  let v = btree_of_array (Array.of_list (List.rev !varlist)) th.th_a in
  List.map 
    (fun p -> 
       (mkAppA [| Lazy.force coq_interp_asp; th.th_a; th.th_plus; th.th_mult; 
		  th.th_one; th.th_zero; v; p |],
	mkAppA [| Lazy.force coq_interp_acs; th.th_a; th.th_plus; th.th_mult; 
		  th.th_one; th.th_zero; v;
		  pf_reduce cbv_betadeltaiota gl 
		    (mkAppA [| Lazy.force coq_aspolynomial_normalize; p|]) |],
	mkAppA [| Lazy.force coq_spolynomial_simplify_ok;
		  th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; 
		  th.th_eq; v; th.th_t; p |]))
    lp

(*
   gl : goal sigma
   th : ring theory (abstract)
   cl : constr list [c1; c2; ...]
 
Builds 
   - a list of tuples [(c1, c'1, c''1, c'1_eq_c''1); ... ] 
  where c'i is convertible with ci and
  c'i_eq_c''i is a proof of equality of c'i and c''i

*)

let build_apolynom gl th lc =
  let varhash  = (Hashtbl.create 17 : (constr, constr) Hashtbl.t) in
  let varlist = ref ([] : constr list) in (* list of variables *)
  let counter = ref 1 in (* number of variables created + 1 *)
  let rec aux c = 
    match (kind_of_term (strip_outer_cast c)) with 
      | IsApp (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkAppA [| Lazy.force coq_APplus; aux c1; aux c2 |]
      | IsApp (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkAppA [| Lazy.force coq_APmult; aux c1; aux c2 |]
      (* The special case of Zminus *)
      | IsApp (binop, [|c1; c2|]) 
	  when pf_conv_x gl c (mkAppA [| th.th_plus; c1; 
	                                 mkAppA [| th.th_opp; c2 |] |]) ->
	    mkAppA [| Lazy.force coq_APplus; aux c1;
	              mkAppA [| Lazy.force coq_APopp; aux c2 |] |]
      | IsApp (unop, [|c1|]) when pf_conv_x gl unop th.th_opp ->
	  mkAppA [| Lazy.force coq_APopp; aux c1 |]
      | _ when pf_conv_x gl c th.th_zero -> Lazy.force coq_AP0
      | _ when pf_conv_x gl c th.th_one -> Lazy.force coq_AP1
      | _ -> 
	  try Hashtbl.find varhash c 
	  with Not_found -> 
	    let newvar = mkAppA [| Lazy.force coq_APvar; 
				   (path_of_int !counter) |] in
	    begin 
	      incr counter;
	      varlist := c :: !varlist;
	      Hashtbl.add varhash c newvar;
	      newvar
	    end
  in
  let lp = List.map aux lc in
  let v = (btree_of_array (Array.of_list (List.rev !varlist)) th.th_a) in
  List.map 
    (fun p -> 
       (mkAppA [| Lazy.force coq_interp_ap;
		  th.th_a; th.th_plus; th.th_mult; th.th_one; 
		  th.th_zero; th.th_opp; v; p |],
	mkAppA [| Lazy.force coq_interp_sacs;
		  th.th_a; th.th_plus; th.th_mult; 
		  th.th_one; th.th_zero; th.th_opp; v; 
		  pf_reduce cbv_betadeltaiota gl 
		    (mkAppA [| Lazy.force coq_apolynomial_normalize; p |]) |],
	mkAppA [| Lazy.force coq_apolynomial_normalize_ok;
		  th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; 
		  th.th_opp; th.th_eq; v; th.th_t; p |]))
    lp
    
module SectionPathSet = 
  Set.Make(struct
	     type t = section_path
	     let compare = Pervasives.compare
	   end)

(* Avec l'uniformisation des red_kind, on perd ici sur la structure
   SectionPathSet; peut-être faudra-t-il la déplacer dans Closure *)
let constants_to_unfold = 
(*  List.fold_right SectionPathSet.add *)
    [ path_of_string "#Ring_normalize#interp_cs.cci";
      path_of_string "#Ring_normalize#interp_var.cci";
      path_of_string "#Ring_normalize#interp_vl.cci";
      path_of_string "#Ring_abstract#interp_acs.cci";
      path_of_string "#Ring_abstract#interp_sacs.cci";
      path_of_string "#Quote#varmap_find.cci" ]
(*    SectionPathSet.empty *)

(* Unfolds the functions interp and find_btree in the term c of goal gl *)
let polynom_unfold_tac =
  let flags = (UNIFORM, red_add betaiota_red (CONST constants_to_unfold)) in
  reduct_in_concl (cbv_norm_flags flags)
      
(* lc : constr list *)
(* th : theory associated to t *)
(* op : clause (None for conclusion or Some id for hypothesis id) *)
(* gl : goal  *)
(* Does the rewriting c_i -> (interp R RC v (polynomial_simplify p_i)) 
   where the ring R, the Ring theory RC, the varmap v and the polynomials p_i
   are guessed and such that c_i = (interp R RC v p_i) *)
let raw_polynom th op lc gl =
  (* first we sort the terms : if t' is a subterm of t it must appear
     after t in the list. This is to avoid that the normalization of t'
     modifies t in a non-desired way *)
  let lc = sort_subterm gl lc in
  let ltriplets = 
    if th.th_abstract then 
      if th.th_ring
      then build_apolynom gl th lc
      else build_aspolynom gl th lc
    else
      if th.th_ring 
      then build_polynom gl th lc
      else build_spolynom gl th lc in 
  let polynom_tac = 
    List.fold_right2 
      (fun ci (c'i, c''i, c'i_eq_c''i) tac ->
	 tclTHENS 
	   (elim_type (mkAppA [| Lazy.force coq_eqT; th.th_a; c'i; ci |]))
	   [ tclTHENS 
	       (elim_type 
		  (mkAppA [| Lazy.force coq_eqT; th.th_a; c''i; c'i |]))
	       [ tac;
		 h_exact c'i_eq_c''i ];
	     h_reflexivity])
      lc ltriplets polynom_unfold_tac 
  in
  polynom_tac gl

let guess_eq_tac th = 
  (tclORELSE reflexivity
     (tclTHEN 
	polynom_unfold_tac
	(tclREPEAT 
	   (tclORELSE 
	      (apply (mkAppA [| Lazy.force coq_f_equal2;
				th.th_a; th.th_a; th.th_a;
				th.th_plus |])) 
	      (apply (mkAppA [| Lazy.force coq_f_equal2;
				th.th_a; th.th_a; th.th_a; 
				th.th_mult |]))))))

let polynom lc gl =
  match lc with 
   (* If no argument is given, try to recognize either an equality or
      a declared relation with arguments c1 ... cn, 
      do "Ring c1 c2 ... cn" and then try to apply the simplification
      theorems declared for the relation *)
    | [] ->
	(match Hipattern.match_with_equation (pf_concl gl) with
	   | Some (eq,t::args) ->
	       let th = guess_theory t in
	       if List.exists 
		 (fun c1 -> not (pf_conv_x gl t (pf_type_of gl c1))) args
	       then 
		 errorlabstrm "Ring :"
		   [< 'sTR" All terms must have the same type" >];
	       (tclTHEN (raw_polynom th None args) (guess_eq_tac th)) gl
	   | _ -> 
	       errorlabstrm "polynom :" 
		 [< 'sTR" This goal is not an equality" >])
    (* Elsewhere, guess the theory, check that all terms have the same type
       and apply raw_polynom *)
    | c :: lc' -> 
	let t = pf_type_of gl c in 
	let th = guess_theory t in 
	if List.exists 
	  (fun c1 -> not (pf_conv_x gl t (pf_type_of gl c1))) lc'
	then 
	  errorlabstrm "Ring :"
	    [< 'sTR" All terms must have the same type" >];
	(tclTHEN (raw_polynom th None lc) polynom_unfold_tac) gl

let dyn_polynom ltacargs gl =  
  polynom (List.map 
	     (function 
		| Command c -> pf_interp_constr gl c 
		| Constr c -> c 
		| _ -> anomaly "dyn_polynom")
	     ltacargs) gl

let v_polynom = add_tactic "Ring" dyn_polynom

