(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* ML part of the Ring tactic *)

open Pp
open Util
open Flags
open Term
open Names
open Libnames
open Nameops
open Reductionops
open Tacticals
open Tacexpr
open Tacmach
open Proof_trees
open Printer
open Equality
open Vernacinterp
open Vernacexpr
open Libobject
open Closure
open Tacred
open Tactics
open Pattern
open Hiddentac
open Nametab
open Quote
open Mod_subst

let mt_evd = Evd.empty
let constr_of c = Constrintern.interp_constr mt_evd (Global.env()) c

let ring_dir = ["Coq";"ring"]
let setoids_dir = ["Coq";"Setoids"]

let ring_constant = Coqlib.gen_constant_in_modules "Ring"
  [ring_dir@["LegacyRing_theory"];
   ring_dir@["Setoid_ring_theory"];
   ring_dir@["Ring_normalize"];
   ring_dir@["Ring_abstract"];
   setoids_dir@["Setoid"];
   ring_dir@["Setoid_ring_normalize"]]

(* Ring theory *)
let coq_Ring_Theory = lazy (ring_constant "Ring_Theory")
let coq_Semi_Ring_Theory = lazy (ring_constant "Semi_Ring_Theory")

(* Setoid ring theory *)
let coq_Setoid_Ring_Theory = lazy (ring_constant "Setoid_Ring_Theory")
let coq_Semi_Setoid_Ring_Theory = lazy(ring_constant "Semi_Setoid_Ring_Theory")

(* Ring normalize *)
let coq_SPplus = lazy (ring_constant "SPplus")
let coq_SPmult = lazy (ring_constant "SPmult")
let coq_SPvar = lazy (ring_constant "SPvar")
let coq_SPconst = lazy (ring_constant "SPconst")
let coq_Pplus = lazy (ring_constant "Pplus")
let coq_Pmult = lazy (ring_constant "Pmult")
let coq_Pvar = lazy (ring_constant "Pvar")
let coq_Pconst = lazy (ring_constant "Pconst")
let coq_Popp = lazy (ring_constant "Popp")
let coq_interp_sp = lazy (ring_constant "interp_sp")
let coq_interp_p = lazy (ring_constant "interp_p")
let coq_interp_cs = lazy (ring_constant "interp_cs")
let coq_spolynomial_simplify = lazy (ring_constant "spolynomial_simplify")
let coq_polynomial_simplify = lazy (ring_constant "polynomial_simplify")
let coq_spolynomial_simplify_ok = lazy(ring_constant "spolynomial_simplify_ok")
let coq_polynomial_simplify_ok = lazy (ring_constant "polynomial_simplify_ok")

(* Setoid theory *)
let coq_Setoid_Theory = lazy(ring_constant "Setoid_Theory")

let coq_seq_refl = lazy(ring_constant "Seq_refl")
let coq_seq_sym = lazy(ring_constant "Seq_sym")
let coq_seq_trans = lazy(ring_constant "Seq_trans")

(* Setoid Ring normalize *)
let coq_SetSPplus = lazy (ring_constant "SetSPplus")
let coq_SetSPmult = lazy (ring_constant "SetSPmult")
let coq_SetSPvar = lazy (ring_constant "SetSPvar")
let coq_SetSPconst = lazy (ring_constant "SetSPconst")
let coq_SetPplus = lazy (ring_constant "SetPplus")
let coq_SetPmult = lazy (ring_constant "SetPmult")
let coq_SetPvar = lazy (ring_constant "SetPvar")
let coq_SetPconst = lazy (ring_constant "SetPconst")
let coq_SetPopp = lazy (ring_constant "SetPopp")
let coq_interp_setsp = lazy (ring_constant "interp_setsp")
let coq_interp_setp = lazy (ring_constant "interp_setp")
let coq_interp_setcs = lazy (ring_constant "interp_setcs")
let coq_setspolynomial_simplify =
  lazy (ring_constant "setspolynomial_simplify")
let coq_setpolynomial_simplify =
  lazy (ring_constant "setpolynomial_simplify")
let coq_setspolynomial_simplify_ok =
  lazy (ring_constant "setspolynomial_simplify_ok")
let coq_setpolynomial_simplify_ok =
  lazy (ring_constant "setpolynomial_simplify_ok")

(* Ring abstract *)
let coq_ASPplus = lazy (ring_constant "ASPplus")
let coq_ASPmult = lazy (ring_constant "ASPmult")
let coq_ASPvar = lazy (ring_constant "ASPvar")
let coq_ASP0 = lazy (ring_constant "ASP0")
let coq_ASP1 = lazy (ring_constant "ASP1")
let coq_APplus = lazy (ring_constant "APplus")
let coq_APmult = lazy (ring_constant "APmult")
let coq_APvar = lazy (ring_constant "APvar")
let coq_AP0 = lazy (ring_constant "AP0")
let coq_AP1 = lazy (ring_constant "AP1")
let coq_APopp = lazy (ring_constant "APopp")
let coq_interp_asp = lazy (ring_constant "interp_asp")
let coq_interp_ap = lazy (ring_constant "interp_ap")
let coq_interp_acs = lazy (ring_constant "interp_acs")
let coq_interp_sacs = lazy (ring_constant "interp_sacs")
let coq_aspolynomial_normalize = lazy (ring_constant "aspolynomial_normalize")
let coq_apolynomial_normalize = lazy (ring_constant "apolynomial_normalize")
let coq_aspolynomial_normalize_ok =
  lazy (ring_constant "aspolynomial_normalize_ok")
let coq_apolynomial_normalize_ok =
  lazy (ring_constant "apolynomial_normalize_ok")

(* Logic --> to be found in Coqlib *)
open Coqlib

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
      oppm : constr option;
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
      Summary.init_function = (fun () -> theories_map := Cmap.empty) }

(* declare a new type of object in the environment, "tactic-ring-theory"
   The functions theory_to_obj and obj_to_theory do the conversions
   between theories and environement objects. *)


let subst_morph subst morph =
  let plusm' = subst_mps subst morph.plusm in
  let multm' = subst_mps subst morph.multm in
  let oppm' = Option.smartmap (subst_mps subst) morph.oppm in
    if plusm' == morph.plusm
      && multm' == morph.multm
      && oppm' == morph.oppm then
	morph
    else
      { plusm = plusm' ;
	multm = multm' ;
	oppm = oppm' ;
      }

let subst_set subst cset =
  let same = ref true in
  let copy_subst c newset =
    let c' = subst_mps subst c in
      if not (c' == c) then same := false;
      ConstrSet.add c' newset
  in
  let cset' = ConstrSet.fold copy_subst cset ConstrSet.empty in
    if !same then cset else cset'

let subst_theory subst th =
  let th_equiv' = Option.smartmap (subst_mps subst) th.th_equiv in
  let th_setoid_th' = Option.smartmap (subst_mps subst) th.th_setoid_th in
  let th_morph' = Option.smartmap (subst_morph subst) th.th_morph in
  let th_a' = subst_mps subst th.th_a in
  let th_plus' = subst_mps subst th.th_plus in
  let th_mult' = subst_mps subst th.th_mult in
  let th_one' = subst_mps subst th.th_one in
  let th_zero' = subst_mps subst th.th_zero in
  let th_opp' = Option.smartmap (subst_mps subst) th.th_opp in
  let th_eq' = subst_mps subst th.th_eq in
  let th_t' = subst_mps subst th.th_t in
  let th_closed' = subst_set subst th.th_closed in
    if th_equiv' == th.th_equiv
      && th_setoid_th' == th.th_setoid_th
      && th_morph' == th.th_morph
      && th_a' == th.th_a
      && th_plus' == th.th_plus
      && th_mult' == th.th_mult
      && th_one' == th.th_one
      && th_zero' == th.th_zero
      && th_opp' == th.th_opp
      && th_eq' == th.th_eq
      && th_t' == th.th_t
      && th_closed' == th.th_closed
    then
      th
    else
    { th_ring = th.th_ring ;
      th_abstract = th.th_abstract ;
      th_setoid = th.th_setoid ;
      th_equiv = th_equiv' ;
      th_setoid_th = th_setoid_th' ;
      th_morph = th_morph' ;
      th_a = th_a' ;
      th_plus = th_plus' ;
      th_mult = th_mult' ;
      th_one = th_one' ;
      th_zero = th_zero' ;
      th_opp = th_opp' ;
      th_eq = th_eq' ;
      th_t = th_t' ;
      th_closed = th_closed' ;
    }


let subst_th (_,subst,(c,th as obj)) =
  let c' = subst_mps subst c in
  let th' = subst_theory subst th in
    if c' == c && th' == th then obj else
      (c',th')


let (theory_to_obj, obj_to_theory) =
  let cache_th (_,(c, th)) = theories_map_add (c,th) in
  declare_object {(default_object "tactic-ring-theory") with
		    open_function = (fun i o -> if i=1 then cache_th o);
                    cache_function = cache_th;
		    subst_function = subst_th;
		    classify_function = (fun x -> Substitute x) }

(* from the set A, guess the associated theory *)
(* With this simple solution, the theory to use is automatically guessed *)
(* But only one theory can be declared for a given Set *)

let guess_theory a =
  try
    theories_map_find a
  with Not_found ->
    errorlabstrm "Ring"
      (str "No Declared Ring Theory for " ++
	 pr_lconstr a ++ fnl () ++
	 str "Use Add [Semi] Ring to declare it")

(* Looks up an option *)

let unbox = function
  | Some w -> w
  | None -> anomaly "Ring : Not in case of a setoid ring."

(* Protects the convertibility test against undue exceptions when using it
   with untyped terms *)

let safe_pf_conv_x gl c1 c2 = try pf_conv_x gl c1 c2 with _ -> false


(* Add a Ring or a Semi-Ring to the database after a type verification *)

let implement_theory env t th args =
  is_conv env Evd.empty (Typing.type_of env Evd.empty t) (mkLApp (th, args))

(* (\* The following test checks whether the provided morphism is the default *)
(*    one for the given operation. In principle the test is too strict, since *)
(*    it should possible to provide another proof for the same fact (proof *)
(*    irrelevance). In particular, the error message is be not very explicative. *\) *)
let states_compatibility_for env plus mult opp morphs =
 let check op compat = true in
(*   is_conv env Evd.empty (Setoid_replace.default_morphism op).Setoid_replace.lem *)
(*    compat in *)
 check plus morphs.plusm &&
 check mult morphs.multm &&
 (match (opp,morphs.oppm) with
     None, None -> true
   | Some opp, Some compat -> check opp compat
   | _,_ -> assert false)

let add_theory want_ring want_abstract want_setoid a aequiv asetth amorph aplus amult aone azero aopp aeq t cset =
  if theories_map_mem a then errorlabstrm "Add Semi Ring"
    (str "A (Semi-)(Setoid-)Ring Structure is already declared for " ++
       pr_lconstr a);
  let env = Global.env () in
    if (want_ring & want_setoid & (
	not (implement_theory env t coq_Setoid_Ring_Theory
	  [| a; (unbox aequiv); aplus; amult; aone; azero; (unbox aopp); aeq|])
        ||
	not (implement_theory env (unbox asetth) coq_Setoid_Theory
	  [| a; (unbox aequiv) |]) ||
        not (states_compatibility_for env aplus amult aopp (unbox amorph))
        )) then
      errorlabstrm "addring" (str "Not a valid Setoid-Ring theory");
    if (not want_ring & want_setoid & (
        not (implement_theory env t coq_Semi_Setoid_Ring_Theory
	  [| a; (unbox aequiv); aplus; amult; aone; azero; aeq|]) ||
	not (implement_theory env (unbox asetth) coq_Setoid_Theory
	  [| a; (unbox aequiv) |]) ||
        not (states_compatibility_for env aplus amult aopp (unbox amorph))))
    then
      errorlabstrm "addring" (str "Not a valid Semi-Setoid-Ring theory");
    if (want_ring & not want_setoid &
	not (implement_theory env t coq_Ring_Theory
	  [| a; aplus; amult; aone; azero; (unbox aopp); aeq |])) then
      errorlabstrm "addring" (str "Not a valid Ring theory");
    if (not want_ring & not want_setoid &
	not (implement_theory env t coq_Semi_Ring_Theory
	  [| a; aplus; amult; aone; azero; aeq |])) then
      errorlabstrm "addring" (str "Not a valid Semi-Ring theory");
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
      | App (binop,[|c1; c2|]) when safe_pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_SPplus, [|th.th_a; aux c1; aux c2 |])
      | App (binop,[|c1; c2|]) when safe_pf_conv_x gl binop th.th_mult ->
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
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_Pplus, [|th.th_a; aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_Pmult, [|th.th_a; aux c1; aux c2 |])
      (* The special case of Zminus *)
      | App (binop, [|c1; c2|])
	  when safe_pf_conv_x gl c
            (mkApp (th.th_plus, [|c1; mkApp(unbox th.th_opp, [|c2|])|])) ->
	    mkLApp(coq_Pplus,
                  [|th.th_a; aux c1;
	            mkLApp(coq_Popp, [|th.th_a; aux c2|]) |])
      | App (unop, [|c1|]) when safe_pf_conv_x gl unop (unbox th.th_opp) ->
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
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_ASPplus, [| aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_ASPmult, [| aux c1; aux c2 |])
      | _ when safe_pf_conv_x gl c th.th_zero -> Lazy.force coq_ASP0
      | _ when safe_pf_conv_x gl c th.th_one -> Lazy.force coq_ASP1
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
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_APplus, [| aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_APmult, [| aux c1; aux c2 |])
      (* The special case of Zminus *)
      | App (binop, [|c1; c2|])
	  when safe_pf_conv_x gl c
            (mkApp(th.th_plus, [|c1; mkApp(unbox th.th_opp,[|c2|]) |])) ->
	    mkLApp(coq_APplus,
                   [|aux c1; mkLApp(coq_APopp,[|aux c2|]) |])
      | App (unop, [|c1|]) when safe_pf_conv_x gl unop (unbox th.th_opp) ->
	  mkLApp(coq_APopp, [| aux c1 |])
      | _ when safe_pf_conv_x gl c th.th_zero -> Lazy.force coq_AP0
      | _ when safe_pf_conv_x gl c th.th_one -> Lazy.force coq_AP1
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
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_SetPplus, [|th.th_a; aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_mult ->
	  mkLApp(coq_SetPmult, [|th.th_a; aux c1; aux c2 |])
      (* The special case of Zminus *)
      | App (binop, [|c1; c2|])
	  when safe_pf_conv_x gl c
	    (mkApp(th.th_plus, [|c1; mkApp(unbox th.th_opp,[|c2|])|])) ->
	      mkLApp(coq_SetPplus,
                     [| th.th_a; aux c1;
			mkLApp(coq_SetPopp, [|th.th_a; aux c2|]) |])
      | App (unop, [|c1|]) when safe_pf_conv_x gl unop (unbox th.th_opp) ->
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
                  th.th_eq; (unbox th.th_setoid_th);
		  (unbox th.th_morph).plusm; (unbox th.th_morph).multm;
		  (unbox (unbox th.th_morph).oppm); v; th.th_t; p |])))
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
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_plus ->
	  mkLApp(coq_SetSPplus, [|th.th_a; aux c1; aux c2 |])
      | App (binop, [|c1; c2|]) when safe_pf_conv_x gl binop th.th_mult ->
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
                  th.th_mult; th.th_one; th.th_zero; th.th_eq;
                  (unbox th.th_setoid_th);
		  (unbox th.th_morph).plusm;
                  (unbox th.th_morph).multm; v; th.th_t; p |])))
    lp

module SectionPathSet =
  Set.Make(struct
	     type t = full_path
	     let compare = Pervasives.compare
	   end)

(* Avec l'uniformisation des red_kind, on perd ici sur la structure
   SectionPathSet; peut-être faudra-t-il la déplacer dans Closure *)
let constants_to_unfold =
(*  List.fold_right SectionPathSet.add *)
  let transform s =
    let sp = path_of_string s in
    let dir, id = repr_path sp in
      Libnames.encode_con dir id
  in
  List.map transform
    [ "Coq.ring.Ring_normalize.interp_cs";
      "Coq.ring.Ring_normalize.interp_var";
      "Coq.ring.Ring_normalize.interp_vl";
      "Coq.ring.Ring_abstract.interp_acs";
      "Coq.ring.Ring_abstract.interp_sacs";
      "Coq.quote.Quote.varmap_find";
      (* anciennement des Local devenus Definition *)
      "Coq.ring.Ring_normalize.ics_aux";
      "Coq.ring.Ring_normalize.ivl_aux";
      "Coq.ring.Ring_normalize.interp_m";
      "Coq.ring.Ring_abstract.iacs_aux";
      "Coq.ring.Ring_abstract.isacs_aux";
      "Coq.ring.Setoid_ring_normalize.interp_cs";
      "Coq.ring.Setoid_ring_normalize.interp_var";
      "Coq.ring.Setoid_ring_normalize.interp_vl";
      "Coq.ring.Setoid_ring_normalize.ics_aux";
      "Coq.ring.Setoid_ring_normalize.ivl_aux";
      "Coq.ring.Setoid_ring_normalize.interp_m";
    ]
(*    SectionPathSet.empty *)

(* Unfolds the functions interp and find_btree in the term c of goal gl *)
open RedFlags
let polynom_unfold_tac =
  let flags =
    (mkflags(fBETA::fIOTA::(List.map fCONST constants_to_unfold))) in
  reduct_in_concl (cbv_norm_flags flags,DEFAULTcast)

let polynom_unfold_tac_in_term gl =
  let flags =
    (mkflags(fBETA::fIOTA::fZETA::(List.map fCONST constants_to_unfold)))
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
         if !term_quality && safe_pf_conv_x gl c'''i ci then
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
		 (tclORELSE
                   (Equality.general_rewrite true
		     Termops.all_occurrences c'i_eq_c''i)
                   (Equality.general_rewrite false
		     Termops.all_occurrences c'i_eq_c''i))
                 [tac]))
	 else
           (tclORELSE
              (tclORELSE
		 (h_exact c'i_eq_c''i)
		 (h_exact (mkApp(build_coq_eq_sym (),
				 [|th.th_a; c'''i; ci; c'i_eq_c''i |]))))
	      (tclTHENS
		 (elim_type
		    (mkApp(build_coq_eq (), [|th.th_a; c'''i; ci |])))
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
        (tclTHEN
	   (* Normalized sums associate on the right *)
	   (tclREPEAT
	      (tclTHENFIRST
		 (apply (mkApp(build_coq_f_equal2 (),
		               [| th.th_a; th.th_a; th.th_a;
				  th.th_plus |])))
		 reflexivity))
	   (tclTRY
	      (tclTHENLAST
		 (apply (mkApp(build_coq_f_equal2 (),
			       [| th.th_a; th.th_a; th.th_a;
				  th.th_plus |])))
		 reflexivity)))))

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
      if (List.mem e []) (*  (Setoid_replace.equiv_list ())) *)
      then Some (decompose_app c)
      else None
  | _ -> None

let polynom lc gl =
  Coqlib.check_required_library ["Coq";"ring";"LegacyRing"];
  match lc with
   (* If no argument is given, try to recognize either an equality or
      a declared relation with arguments c1 ... cn,
      do "Ring c1 c2 ... cn" and then try to apply the simplification
      theorems declared for the relation *)
    | [] ->
	(try
	  match Hipattern.match_with_equation (pf_concl gl) with
	   | _,_,Hipattern.PolymorphicLeibnizEq (t,c1,c2) ->
	       let th = guess_theory t in
	       (tclTHEN (raw_polynom th None [c1;c2]) (guess_eq_tac th)) gl
	   | _,_,Hipattern.HeterogenousEq (t1,c1,t2,c2)
	       when safe_pf_conv_x gl t1 t2 ->
	       let th = guess_theory t1 in
	       (tclTHEN (raw_polynom th None [c1;c2]) (guess_eq_tac th)) gl
	   | _ -> raise Exit
	  with Hipattern.NoEquationFound | Exit ->
	          (match match_with_equiv (pf_concl gl) with
		     | Some (equiv, c1::args) ->
			 let t = (pf_type_of gl c1) in
			 let th = (guess_theory t) in
			   if List.exists
			     (fun c2 -> not (safe_pf_conv_x gl t (pf_type_of gl c2))) args
			   then
			     errorlabstrm "Ring :"
			       (str" All terms must have the same type");
			   (tclTHEN (raw_polynom th None (c1::args)) (guess_equiv_tac th)) gl
		     | _ -> errorlabstrm "polynom :"
			 (str" This goal is not an equality nor a setoid equivalence")))
    (* Elsewhere, guess the theory, check that all terms have the same type
       and apply raw_polynom *)
    | c :: lc' ->
	let t = pf_type_of gl c in
	let th = guess_theory t in
	  if List.exists
	    (fun c1 -> not (safe_pf_conv_x gl t (pf_type_of gl c1))) lc'
	  then
	    errorlabstrm "Ring :"
	      (str" All terms must have the same type");
	  (tclTHEN (raw_polynom th None lc) polynom_unfold_tac) gl
