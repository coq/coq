(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* ML part of the Ring tactic *)

open Pp
open Util
open Options
open Term
open Names
open Nameops
open Reductionops
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
open Nametab
open Quote

let mt_evd = Evd.empty
let constr_of com = Astterm.interp_constr mt_evd (Global.env()) com

let constant dir s =
  let dir = make_dirpath (List.map id_of_string (List.rev ("Coq"::dir))) in
  let id = id_of_string s in
  try 
    Declare.global_reference_in_absolute_module dir id
  with Not_found ->
    anomaly ("Ring: cannot find "^
	     (Nametab.string_of_qualid (Nametab.make_qualid dir id)))

(* Ring theory *)
let coq_Ring_Theory = lazy (constant ["ring";"Ring_theory"] "Ring_Theory")
let coq_Semi_Ring_Theory = lazy (constant ["ring";"Ring_theory"] "Semi_Ring_Theory")

(* Setoid ring theory *)
let coq_Setoid_Ring_Theory = lazy (constant ["ring";"Setoid_ring_theory"] "Setoid_Ring_Theory")
let coq_Semi_Setoid_Ring_Theory = lazy (constant ["ring";"Setoid_ring_theory"] "Semi_Setoid_Ring_Theory")

(* Ring normalize *)
let coq_SPplus = lazy (constant ["ring";"Ring_normalize"] "SPplus")
let coq_SPmult = lazy (constant ["ring";"Ring_normalize"] "SPmult")
let coq_SPvar = lazy (constant ["ring";"Ring_normalize"] "SPvar")
let coq_SPconst = lazy (constant ["ring";"Ring_normalize"] "SPconst")
let coq_Pplus = lazy (constant ["ring";"Ring_normalize"] "Pplus")
let coq_Pmult = lazy (constant ["ring";"Ring_normalize"] "Pmult")
let coq_Pvar = lazy (constant ["ring";"Ring_normalize"] "Pvar")
let coq_Pconst = lazy (constant ["ring";"Ring_normalize"] "Pconst")
let coq_Popp = lazy (constant ["ring";"Ring_normalize"] "Popp")
let coq_interp_sp = lazy (constant ["ring";"Ring_normalize"] "interp_sp")
let coq_interp_p = lazy (constant ["ring";"Ring_normalize"] "interp_p")
let coq_interp_cs = lazy (constant ["ring";"Ring_normalize"] "interp_cs")
let coq_spolynomial_simplify = 
  lazy (constant ["ring";"Ring_normalize"] "spolynomial_simplify")
let coq_polynomial_simplify = 
  lazy (constant ["ring";"Ring_normalize"] "polynomial_simplify")
let coq_spolynomial_simplify_ok = 
  lazy (constant ["ring";"Ring_normalize"] "spolynomial_simplify_ok")
let coq_polynomial_simplify_ok = 
  lazy (constant ["ring";"Ring_normalize"] "polynomial_simplify_ok")

(* Setoid theory *)
let coq_Setoid_Theory = lazy(constant ["setoid";"Setoid_replace"] "Setoid_Theory")

let coq_seq_refl = lazy(constant ["setoid";"Setoid_replace"] "Seq_refl")
let coq_seq_sym = lazy(constant ["setoid";"Setoid_replace"] "Seq_sym")
let coq_seq_trans = lazy(constant ["setoid";"Setoid_replace"] "Seq_trans")

(* Setoid Ring normalize *)
let coq_SetSPplus = lazy (constant ["ring";"Ring_normalize"] "SetSPplus")
let coq_SetSPmult = lazy (constant ["ring";"Ring_normalize"] "SetSPmult")
let coq_SetSPvar = lazy (constant ["ring";"Ring_normalize"] "SetSPvar")
let coq_SetSPconst = lazy (constant ["ring";"Ring_normalize"] "SetSPconst")
let coq_SetPplus = lazy (constant ["ring";"Ring_normalize"] "SetPplus")
let coq_SetPmult = lazy (constant ["ring";"Ring_normalize"] "SetPmult")
let coq_SetPvar = lazy (constant ["ring";"Ring_normalize"] "SetPvar")
let coq_SetPconst = lazy (constant ["ring";"Ring_normalize"] "SetPconst")
let coq_SetPopp = lazy (constant ["ring";"Ring_normalize"] "SetPopp")
let coq_interp_setsp = lazy (constant ["ring";"Ring_normalize"] "interp_setsp")
let coq_interp_setp = lazy (constant ["ring";"Ring_normalize"] "interp_setp")
let coq_interp_setcs = lazy (constant ["ring";"Ring_normalize"] "interp_cs")
let coq_setspolynomial_simplify = 
  lazy (constant ["ring";"Ring_normalize"] "setspolynomial_simplify")
let coq_setpolynomial_simplify = 
  lazy (constant ["ring";"Ring_normalize"] "setpolynomial_simplify")
let coq_setspolynomial_simplify_ok = 
  lazy (constant ["ring";"Ring_normalize"] "setspolynomial_simplify_ok")
let coq_setpolynomial_simplify_ok = 
  lazy (constant ["ring";"Ring_normalize"] "setpolynomial_simplify_ok")

(* Ring abstract *)
let coq_ASPplus = lazy (constant ["ring";"Ring_abstract"] "ASPplus")
let coq_ASPmult = lazy (constant ["ring";"Ring_abstract"] "ASPmult")
let coq_ASPvar = lazy (constant ["ring";"Ring_abstract"] "ASPvar")
let coq_ASP0 = lazy (constant ["ring";"Ring_abstract"] "ASP0")
let coq_ASP1 = lazy (constant ["ring";"Ring_abstract"] "ASP1")
let coq_APplus = lazy (constant ["ring";"Ring_abstract"] "APplus")
let coq_APmult = lazy (constant ["ring";"Ring_abstract"] "APmult")
let coq_APvar = lazy (constant ["ring";"Ring_abstract"] "APvar")
let coq_AP0 = lazy (constant ["ring";"Ring_abstract"] "AP0")
let coq_AP1 = lazy (constant ["ring";"Ring_abstract"] "AP1")
let coq_APopp = lazy (constant ["ring";"Ring_abstract"] "APopp")
let coq_interp_asp = 
  lazy (constant ["ring";"Ring_abstract"] "interp_asp")
let coq_interp_ap = 
  lazy (constant ["ring";"Ring_abstract"] "interp_ap")
 let coq_interp_acs = 
  lazy (constant ["ring";"Ring_abstract"] "interp_acs")
let coq_interp_sacs = 
  lazy (constant ["ring";"Ring_abstract"] "interp_sacs")
let coq_aspolynomial_normalize = 
  lazy (constant ["ring";"Ring_abstract"] "aspolynomial_normalize")
let coq_apolynomial_normalize = 
  lazy (constant ["ring";"Ring_abstract"] "apolynomial_normalize")
let coq_aspolynomial_normalize_ok = 
  lazy (constant ["ring";"Ring_abstract"] "aspolynomial_normalize_ok")
let coq_apolynomial_normalize_ok = 
  lazy (constant ["ring";"Ring_abstract"] "apolynomial_normalize_ok")

(* Logic --> to be found in Coqlib *)
open Coqlib
(*
val build_coq_f_equal2 : constr delayed
val build_coq_eqT : constr delayed
val build_coq_sym_eqT : constr delayed
*)

let mkLApp(fc,v) = mkApp(Lazy.force fc, v)

(*********** Useful types and functions ************)

module OperSet = 
  Set.Make (struct 
	      type t = global_reference
	      let compare = (Pervasives.compare : t->t->int)
	    end)

type morph =
    { plusm : constr;
      multm : constr;
      oppm : constr;
    }

type theory =
    { th_ring : bool;                  (* false for a semi-ring *)
      th_abstract : bool;
      th_setoid : bool;                (* true for a setoid ring *)
      th_equiv : constr option;
      th_setoid_th : constr option;
      th_morph : morph option;
      th_a : constr;                   (* e.g. nat *)
      th_plus : constr;
      th_mult : constr;
      th_one : constr;
      th_zero : constr;
      th_opp : constr option;          (* None if semi-ring *)
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
      Summary.init_function = (fun () -> theories_map := Cmap.empty);
      Summary.survive_section = false }

(* declare a new type of object in the environment, "tactic-ring-theory"
   The functions theory_to_obj and obj_to_theory do the conversions
   between theories and environement objects. *)

let (theory_to_obj, obj_to_theory) = 
  let cache_th (_,(c, th)) = theories_map_add (c,th)
  and export_th x = Some x in
  declare_object ("tactic-ring-theory",
		  { load_function = (fun _ -> ());
		    open_function = cache_th;
                    cache_function = cache_th;
		    export_function = export_th })

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

(* Looks up an option *)

let unbox = function 
  | Some w -> w
  | None -> anomaly "Ring : Not in case of a setoid ring."

(* Add a Ring or a Semi-Ring to the database after a type verification *)

let add_theory want_ring want_abstract want_setoid a aequiv asetth amorph aplus amult aone azero aopp aeq t cset = 
  if theories_map_mem a then errorlabstrm "Add Semi Ring" 
    [< 'sTR "A (Semi-)(Setoid-)Ring Structure is already declared for ";
       prterm a >];
  let env = Global.env () in
    if (want_ring & want_setoid &
	(not (is_conv env Evd.empty (Typing.type_of env Evd.empty t)
		(mkLApp (coq_Setoid_Ring_Theory, 
			[| a; (unbox aequiv); aplus; amult; aone; azero; (unbox aopp); aeq|])))) &
	(not (is_conv env Evd.empty (Typing.type_of env Evd.empty (unbox asetth))
		(mkLApp (coq_Setoid_Theory, [| a; (unbox aequiv) |]))))) then 
      errorlabstrm "addring" [< 'sTR "Not a valid Setoid-Ring theory" >];
    if (not want_ring & want_setoid &
	(not (is_conv env Evd.empty (Typing.type_of env Evd.empty t)
		(mkLApp (coq_Semi_Setoid_Ring_Theory, 
			[| a; (unbox aequiv); aplus; amult; aone; azero; aeq|])))) &
	(not (is_conv env Evd.empty (Typing.type_of env Evd.empty (unbox asetth))
		(mkLApp (coq_Setoid_Theory, [| a; (unbox aequiv) |]))))) then 
      errorlabstrm "addring" [< 'sTR "Not a valid Semi-Setoid-Ring theory" >];
    if (want_ring & not want_setoid &
	not (is_conv env Evd.empty (Typing.type_of env Evd.empty t)
	       (mkLApp (coq_Ring_Theory, 
		       [| a; aplus; amult; aone; azero; (unbox aopp); aeq |])))) then
      errorlabstrm "addring" [< 'sTR "Not a valid Ring theory" >];
    if (not want_ring & not want_setoid &
	not (is_conv  env Evd.empty (Typing.type_of env Evd.empty t) 
	       (mkLApp (coq_Semi_Ring_Theory, 
		       [| a; aplus; amult; aone; azero; aeq |])))) then 
      errorlabstrm "addring" [< 'sTR "Not a valid Semi-Ring theory" >];
    Lib.add_anonymous_leaf
      (theory_to_obj 
	 (a, { th_ring = want_ring;
	       th_abstract = want_abstract;
	       th_setoid = want_setoid;
	       th_equiv = aequiv;
	       th_setoid_th = asetth;
	       th_morph = amorph;
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
  | _ -> anomaly "Add (Semi) (Setoid) Ring"
  
let cset_of_comarg_list l = 
  List.fold_right ConstrSet.add (List.map constr_of_comarg l) ConstrSet.empty

let _ = 
  vinterp_add "AddSemiRing"
    (function
       | (VARG_CONSTR a)::(VARG_CONSTR aplus)::(VARG_CONSTR amult)
	 ::(VARG_CONSTR aone)::(VARG_CONSTR azero)::(VARG_CONSTR aeq)
	 ::(VARG_CONSTR t)::l -> 
	   (fun () -> (add_theory false false false
			 (constr_of a)
			 None
			 None
			 None
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 None
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
	   (fun () -> (add_theory true false false
			 (constr_of a)
			 None
			 None
			 None
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (Some (constr_of aopp))
			 (constr_of aeq)
			 (constr_of t)
			 (cset_of_comarg_list l)))
       | _ -> anomaly "AddRing")
    
let _ = 
  vinterp_add "AddSetoidRing"
    (function 
       | (VARG_CONSTR a)::(VARG_CONSTR aequiv)::(VARG_CONSTR asetth)::(VARG_CONSTR aplus)
	 ::(VARG_CONSTR amult)::(VARG_CONSTR aone)::(VARG_CONSTR azero)::(VARG_CONSTR aopp)
	 ::(VARG_CONSTR aeq)::(VARG_CONSTR pm)::(VARG_CONSTR mm)::(VARG_CONSTR om)
	 ::(VARG_CONSTR t)::l -> 
	   (fun () -> (add_theory true false true
			 (constr_of a)
			 (Some (constr_of aequiv))
			 (Some (constr_of asetth))
			 (Some {
			    plusm = (constr_of pm);
			    multm = (constr_of mm);
			    oppm = (constr_of om)})
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (Some (constr_of aopp))
			 (constr_of aeq)
			 (constr_of t)
			 (cset_of_comarg_list l)))
       | _ -> anomaly "AddSetoidRing")
    
let _ = 
  vinterp_add "AddSemiSetoidRing"
    (function 
       | (VARG_CONSTR a)::(VARG_CONSTR aequiv)::(VARG_CONSTR asetth)::(VARG_CONSTR aplus)
	 ::(VARG_CONSTR amult)::(VARG_CONSTR aone)::(VARG_CONSTR azero)
	 ::(VARG_CONSTR aeq)::(VARG_CONSTR pm)::(VARG_CONSTR mm)::(VARG_CONSTR om)
	 ::(VARG_CONSTR t)::l -> 
	   (fun () -> (add_theory false false true
			 (constr_of a)
			 (Some (constr_of aequiv))
			 (Some (constr_of asetth))
			 (Some {
			    plusm = (constr_of pm);
			    multm = (constr_of mm);
			    oppm = (constr_of om)})
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 None
			 (constr_of aeq)
			 (constr_of t)
			 (cset_of_comarg_list l)))
       | _ -> anomaly "AddSemiSetoidRing")
    
let _ = 
  vinterp_add "AddAbstractSemiRing"
    (function 
       | [VARG_CONSTR a; VARG_CONSTR aplus; 
	  VARG_CONSTR amult; VARG_CONSTR aone;
	  VARG_CONSTR azero; VARG_CONSTR aeq; VARG_CONSTR t] -> 
	   (fun () -> (add_theory false true false
			 (constr_of a)
			 None
			 None
			 None
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 None
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
	   (fun () -> (add_theory true true false
			 (constr_of a)
			 None
			 None
			 None
			 (constr_of aplus)
			 (constr_of amult)
			 (constr_of aone)
			 (constr_of azero)
			 (Some (constr_of aopp))
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
      | App (binop,[|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_SPplus, [|th.th_a; aux c1; aux c2 |])
      | App (binop,[|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_SPmult, [|th.th_a; aux c1; aux c2 |])
      | _ when closed_under th.th_closed c ->
	  mkLApp(coq_SPconst, [|th.th_a; c |])
      | _ -> 
	  try Hashtbl.find varhash c 
	  with Not_found -> 
	    let newvar =
              mkLApp(coq_SPvar, [|th.th_a; (path_of_int !counter) |]) in
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
       (mkLApp (coq_interp_sp,
               [|th.th_a; th.th_plus; th.th_mult; th.th_zero; v; p |]),
	mkLApp (coq_interp_cs,
               [|th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; v;
		  pf_reduce cbv_betadeltaiota gl 
		    (mkLApp (coq_spolynomial_simplify, 
			    [| th.th_a; th.th_plus; th.th_mult; 
			       th.th_one; th.th_zero; 
			       th.th_eq; p|])) |]),
	mkLApp (coq_spolynomial_simplify_ok,
	        [| th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; 
		  th.th_eq; v; th.th_t; p |])))
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
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_Pplus, [|th.th_a; aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_Pmult, [|th.th_a; aux c1; aux c2 |])
      (* The special case of Zminus *)
      | App (binop, [|c1; c2|])
	  when pf_conv_x gl c
            (mkApp (th.th_plus, [|c1; mkApp(unbox th.th_opp, [|c2|])|])) ->
	    mkLApp(coq_Pplus,
                  [|th.th_a; aux c1;
	            mkLApp(coq_Popp, [|th.th_a; aux c2|]) |])
      | App (unop, [|c1|]) when pf_conv_x gl unop (unbox th.th_opp) ->
	  mkLApp(coq_Popp, [|th.th_a; aux c1|])
      | _ when closed_under th.th_closed c ->
	  mkLApp(coq_Pconst, [|th.th_a; c |])
      | _ -> 
	  try Hashtbl.find varhash c 
	  with Not_found -> 
	    let newvar =
              mkLApp(coq_Pvar, [|th.th_a; (path_of_int !counter) |]) in
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
       (mkLApp(coq_interp_p,
	       [| th.th_a; th.th_plus; th.th_mult; th.th_zero;
                 (unbox th.th_opp); v; p |])),
	mkLApp(coq_interp_cs,
	       [| th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; v;
		  pf_reduce cbv_betadeltaiota gl 
		    (mkLApp(coq_polynomial_simplify,
			    [| th.th_a; th.th_plus; th.th_mult; 
			       th.th_one; th.th_zero; 
			       (unbox th.th_opp); th.th_eq; p |])) |]),
	mkLApp(coq_polynomial_simplify_ok,
	       [| th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; 
		  (unbox th.th_opp); th.th_eq; v; th.th_t; p |]))
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
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_ASPplus, [| aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_ASPmult, [| aux c1; aux c2 |])
      | _ when pf_conv_x gl c th.th_zero -> Lazy.force coq_ASP0
      | _ when pf_conv_x gl c th.th_one -> Lazy.force coq_ASP1
      | _ -> 
	  try Hashtbl.find varhash c 
	  with Not_found -> 
	    let newvar = mkLApp(coq_ASPvar, [|(path_of_int !counter) |]) in
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
       (mkLApp(coq_interp_asp,
               [| th.th_a; th.th_plus; th.th_mult; 
		  th.th_one; th.th_zero; v; p |]),
	mkLApp(coq_interp_acs,
               [| th.th_a; th.th_plus; th.th_mult; 
		  th.th_one; th.th_zero; v;
		  pf_reduce cbv_betadeltaiota gl 
		    (mkLApp(coq_aspolynomial_normalize,[|p|])) |]),
	mkLApp(coq_spolynomial_simplify_ok,
	       [| th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; 
		  th.th_eq; v; th.th_t; p |])))
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
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_APplus, [| aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_APmult, [| aux c1; aux c2 |])
      (* The special case of Zminus *)
      | App (binop, [|c1; c2|]) 
	  when pf_conv_x gl c
            (mkApp(th.th_plus, [|c1; mkApp(unbox th.th_opp,[|c2|]) |])) ->
	    mkLApp(coq_APplus,
                   [|aux c1; mkLApp(coq_APopp,[|aux c2|]) |])
      | App (unop, [|c1|]) when pf_conv_x gl unop (unbox th.th_opp) ->
	  mkLApp(coq_APopp, [| aux c1 |])
      | _ when pf_conv_x gl c th.th_zero -> Lazy.force coq_AP0
      | _ when pf_conv_x gl c th.th_one -> Lazy.force coq_AP1
      | _ -> 
	  try Hashtbl.find varhash c 
	  with Not_found -> 
	    let newvar =
              mkLApp(coq_APvar, [| path_of_int !counter |]) in
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
       (mkLApp(coq_interp_ap,
	       [| th.th_a; th.th_plus; th.th_mult; th.th_one; 
		  th.th_zero; (unbox th.th_opp); v; p |]),
	mkLApp(coq_interp_sacs,
	       [| th.th_a; th.th_plus; th.th_mult; 
		  th.th_one; th.th_zero; (unbox th.th_opp); v; 
		  pf_reduce cbv_betadeltaiota gl 
		    (mkLApp(coq_apolynomial_normalize, [|p|])) |]),
	mkLApp(coq_apolynomial_normalize_ok,
	       [| th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; 
		  (unbox th.th_opp); th.th_eq; v; th.th_t; p |])))
    lp
    
(*
   gl : goal sigma
   th : setoid ring theory (concrete)
   cl : constr list [c1; c2; ...]
 
Builds 
   - a list of tuples [(c1, c'1, c''1, c'1_eq_c''1); ... ] 
  where c'i is convertible with ci and
  c'i_eq_c''i is a proof of equality of c'i and c''i

*)

let build_setpolynom gl th lc =
  let varhash  = (Hashtbl.create 17 : (constr, constr) Hashtbl.t) in
  let varlist = ref ([] : constr list) in (* list of variables *)
  let counter = ref 1 in (* number of variables created + 1 *)
  let rec aux c = 
    match (kind_of_term (strip_outer_cast c)) with 
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_SetPplus, [|th.th_a; aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_SetPmult, [|th.th_a; aux c1; aux c2 |])
      (* The special case of Zminus *)
      | App (binop, [|c1; c2|])
	  when pf_conv_x gl c
            (mkApp(th.th_plus, [|c1; mkApp(unbox th.th_opp,[|c2|])|])) ->
	    mkLApp(coq_SetPplus,
                   [| th.th_a; aux c1;
	              mkLApp(coq_SetPopp, [|th.th_a; aux c2|]) |])
      | App (unop, [|c1|]) when pf_conv_x gl unop (unbox th.th_opp) ->
	  mkLApp(coq_SetPopp, [| th.th_a; aux c1 |])
      | _ when closed_under th.th_closed c ->
	  mkLApp(coq_SetPconst, [| th.th_a; c |])
      | _ -> 
	  try Hashtbl.find varhash c 
	  with Not_found -> 
	    let newvar =
              mkLApp(coq_SetPvar, [| th.th_a; path_of_int !counter |]) in
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
       (mkLApp(coq_interp_setp,
	       [| th.th_a; th.th_plus; th.th_mult; th.th_zero;
                  (unbox th.th_opp); v; p |]),
	mkLApp(coq_interp_setcs,
	       [| th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; v;
		  pf_reduce cbv_betadeltaiota gl 
		    (mkLApp(coq_setpolynomial_simplify,
			    [| th.th_a; th.th_plus; th.th_mult; 
			       th.th_one; th.th_zero; 
			       (unbox th.th_opp); th.th_eq; p |])) |]),
	mkLApp(coq_setpolynomial_simplify_ok,
	       [| th.th_a; (unbox th.th_equiv); th.th_plus;
                  th.th_mult; th.th_one; th.th_zero;(unbox th.th_opp);
                  th.th_eq; v; th.th_t; (unbox th.th_setoid_th);
		  (unbox th.th_morph).plusm; (unbox th.th_morph).multm;
		  (unbox th.th_morph).oppm; p |])))
    lp

(*
   gl : goal sigma
   th : semi setoid ring theory (concrete)
   cl : constr list [c1; c2; ...]
 
Builds 
   - a list of tuples [(c1, c'1, c''1, c'1_eq_c''1); ... ] 
  where c'i is convertible with ci and
  c'i_eq_c''i is a proof of equality of c'i and c''i

*)

let build_setspolynom gl th lc =
  let varhash  = (Hashtbl.create 17 : (constr, constr) Hashtbl.t) in
  let varlist = ref ([] : constr list) in (* list of variables *)
  let counter = ref 1 in (* number of variables created + 1 *)
  let rec aux c = 
    match (kind_of_term (strip_outer_cast c)) with 
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_SetSPplus, [|th.th_a; aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_SetSPmult, [| th.th_a; aux c1; aux c2 |])
      | _ when closed_under th.th_closed c ->
	  mkLApp(coq_SetSPconst, [| th.th_a; c |])
      | _ -> 
	  try Hashtbl.find varhash c
	  with Not_found ->
	    let newvar =
              mkLApp(coq_SetSPvar, [|th.th_a; path_of_int !counter |]) in
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
       (mkLApp(coq_interp_setsp,
	       [| th.th_a; th.th_plus; th.th_mult; th.th_zero; v; p |]),
	mkLApp(coq_interp_setcs,
               [| th.th_a; th.th_plus; th.th_mult; th.th_one; th.th_zero; v;
		  pf_reduce cbv_betadeltaiota gl 
		    (mkLApp(coq_setspolynomial_simplify,
			    [| th.th_a; th.th_plus; th.th_mult; 
			       th.th_one; th.th_zero; 
			       th.th_eq; p |])) |]),
	mkLApp(coq_setspolynomial_simplify_ok,
	       [| th.th_a; (unbox th.th_equiv); th.th_plus;
                  th.th_mult; th.th_one; th.th_zero; th.th_eq; v;
                  th.th_t; (unbox th.th_setoid_th);
		  (unbox th.th_morph).plusm;
                  (unbox th.th_morph).multm; p |])))
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
    [ path_of_string "Coq.ring.Ring_normalize.interp_cs";
      path_of_string "Coq.ring.Ring_normalize.interp_var";
      path_of_string "Coq.ring.Ring_normalize.interp_vl";
      path_of_string "Coq.ring.Ring_abstract.interp_acs";
      path_of_string "Coq.ring.Ring_abstract.interp_sacs";
      path_of_string "Coq.ring.Quote.varmap_find";
      (* anciennement des Local devenus Definition *)
      path_of_string "Coq.ring.Ring_normalize.ics_aux";
      path_of_string "Coq.ring.Ring_normalize.ivl_aux";
      path_of_string "Coq.ring.Ring_normalize.interp_m";
      path_of_string "Coq.ring.Ring_abstract.iacs_aux";
      path_of_string "Coq.ring.Ring_abstract.isacs_aux";
      path_of_string "Coq.ring.Setoid_ring_normalize.interp_cs";
      path_of_string "Coq.ring.Setoid_ring_normalize.interp_var";
      path_of_string "Coq.ring.Setoid_ring_normalize.interp_vl";
      path_of_string "Coq.ring.Setoid_ring_normalize.ics_aux";
      path_of_string "Coq.ring.Setoid_ring_normalize.ivl_aux";
      path_of_string "Coq.ring.Setoid_ring_normalize.interp_m";
    ]
(*    SectionPathSet.empty *)

(* Unfolds the functions interp and find_btree in the term c of goal gl *)
open RedFlags
let polynom_unfold_tac =
  let flags =
    (UNIFORM, mkflags(fBETA::fIOTA::(List.map fCONST constants_to_unfold))) in
  reduct_in_concl (cbv_norm_flags flags)
      
let polynom_unfold_tac_in_term gl =
  let flags = 
    (UNIFORM,mkflags(fBETA::fIOTA::fZETA::(List.map fCONST constants_to_unfold)))
  in
  cbv_norm_flags flags (pf_env gl) (project gl)

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
    if th.th_setoid then
      if th.th_ring
      then build_setpolynom gl th lc
      else build_setspolynom gl th lc
    else
      if th.th_ring then
	if th.th_abstract
	then build_apolynom gl th lc
	else build_polynom gl th lc
      else
	if th.th_abstract 
	then build_aspolynom gl th lc
	else build_spolynom gl th lc in 
  let polynom_tac = 
    List.fold_right2
      (fun ci (c'i, c''i, c'i_eq_c''i) tac ->
         let c'''i = 
	   if !term_quality then polynom_unfold_tac_in_term gl c''i else c''i 
	 in
         if !term_quality && pf_conv_x gl c'''i ci then 
	   tac (* convertible terms *)
         else if th.th_setoid
	 then
           (tclORELSE 
              (tclORELSE
		 (h_exact c'i_eq_c''i)
		 (h_exact (mkLApp(coq_seq_sym, 
				  [| th.th_a; (unbox th.th_equiv);
                                     (unbox th.th_setoid_th);
				     c'''i; ci; c'i_eq_c''i |]))))
	      (tclTHENS 
		 (Setoid_replace.setoid_replace ci c'''i None)
		 [ tac;
                   h_exact c'i_eq_c''i ])) 
	 else
           (tclORELSE
              (tclORELSE
		 (h_exact c'i_eq_c''i)
		 (h_exact (mkApp(build_coq_sym_eqT (),
				 [|th.th_a; c'''i; ci; c'i_eq_c''i |]))))
	      (tclTHENS 
		 (elim_type 
		    (mkApp(build_coq_eqT (), [|th.th_a; c'''i; ci |])))
		 [ tac;
                   h_exact c'i_eq_c''i ]))
)
      lc ltriplets polynom_unfold_tac 
  in
  polynom_tac gl

let guess_eq_tac th = 
  (tclORELSE reflexivity
     (tclTHEN 
	polynom_unfold_tac
	(tclREPEAT 
	   (tclORELSE 
	      (apply (mkApp(build_coq_f_equal2 (),
		            [| th.th_a; th.th_a; th.th_a;
			       th.th_plus |])))
	      (apply (mkApp(build_coq_f_equal2 (),
		            [| th.th_a; th.th_a; th.th_a; 
			       th.th_mult |])))))))
let guess_equiv_tac th = 
  (tclORELSE (apply (mkLApp(coq_seq_refl,
			    [| th.th_a; (unbox th.th_equiv);
			       (unbox th.th_setoid_th)|])))
     (tclTHEN 
	polynom_unfold_tac
	(tclREPEAT 
	   (tclORELSE 
	      (apply (unbox th.th_morph).plusm)
	      (apply (unbox th.th_morph).multm)))))

let match_with_equiv c = match (kind_of_term c) with
  | App (e,a) -> 
      if (List.mem e (Setoid_replace.equiv_list ()))
      then Some (decompose_app c)
      else None
  | _ -> None

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
	   | _ -> (match match_with_equiv (pf_concl gl) with
		     | Some (equiv, c1::args) ->
			 let t = (pf_type_of gl c1) in
			 let th = (guess_theory t) in
			   if List.exists 
			     (fun c2 -> not (pf_conv_x gl t (pf_type_of gl c2))) args
			   then 
			     errorlabstrm "Ring :"
			       [< 'sTR" All terms must have the same type" >];
			   (tclTHEN (raw_polynom th None args) (guess_equiv_tac th)) gl		   
		     | _ -> errorlabstrm "polynom :" 
			 [< 'sTR" This goal is not an equality nor a setoid equivalence" >]))
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

