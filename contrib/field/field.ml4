(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma kernel/names.cmo parsing/ast.cmo parsing/g_tactic.cmo  parsing/g_ltac.cmo parsing/g_constr.cmo" i*)

(* $Id$ *)

open Names
open Proof_type
open Tacinterp
open Tacmach
open Term
open Util
open Vernacinterp

(* Interpretation of constr's *)
let constr_of com = Astterm.interp_constr Evd.empty (Global.env()) com

(* Construction of constants *)
let constant dir s =
  let dir = "Coq"::"field"::dir in
  let id = id_of_string s in
  try 
    Declare.global_reference_in_absolute_module dir id
  with Not_found ->
    anomaly ("Field: cannot find "^
	     (Nametab.string_of_qualid (Nametab.make_qualid dir id)))

(* To deal with the optional arguments *)
let constr_of_opt a opt =
  let ac = constr_of a in
  match opt with
  | None -> mkApp ((constant ["Field_Compl"] "None"),[|ac|])
  | Some f -> mkApp ((constant ["Field_Compl"] "Some"),[|ac;constr_of f|])

(* Table of theories *)
let th_tab = ref ((Hashtbl.create 53) : (constr,constr) Hashtbl.t)

let lookup typ = Hashtbl.find !th_tab typ

let _ = 
  let init () = th_tab := (Hashtbl.create 53) in
  let freeze () = !th_tab in
  let unfreeze fs = th_tab := fs in
  Summary.declare_summary "field"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init;
      Summary.survive_section   = false }

let load_addfield _ = ()
let cache_addfield (_,(typ,th)) = Hashtbl.add !th_tab typ th
let export_addfield x = Some x

(* Declaration of the Add Field library object *)
let (in_addfield,out_addfield)=
  Libobject.declare_object
    ("ADD_FIELD",
     { Libobject.load_function = load_addfield;
       Libobject.open_function = cache_addfield;
       Libobject.cache_function = cache_addfield;
       Libobject.export_function = export_addfield })

(* Adds a theory to the table *)
let add_field a aplus amult aone azero aopp aeq ainv aminus_o adiv_o rth
  ainv_l =
  begin
    (try
       Ring.add_theory true true false a None None None aplus amult aone azero (Some aopp) aeq rth
         Quote.ConstrSet.empty
     with | UserError("Add Semi Ring",_) -> ());
    let th = mkApp ((constant ["Field_Theory"] "Build_Field_Theory"),
      [|a;aplus;amult;aone;azero;aopp;aeq;ainv;aminus_o;adiv_o;rth;ainv_l|]) in
    Lib.add_anonymous_leaf (in_addfield (a,th))
  end

(* Vernac command declaration *)
let _ =
  let rec opt_arg (aminus_o,adiv_o) = function
    | (VARG_STRING "minus")::(VARG_CONSTR aminus)::l ->
      (match aminus_o with
      |	None -> opt_arg ((Some aminus),adiv_o) l
      |	_ -> anomaly "AddField")
    | (VARG_STRING "div")::(VARG_CONSTR adiv)::l ->
      (match adiv_o with
      |	None -> opt_arg (aminus_o,(Some adiv)) l
      |	_ -> anomaly "AddField")
    | _ -> (aminus_o,adiv_o) in
  vinterp_add "AddField"
    (function 
       | (VARG_CONSTR a)::(VARG_CONSTR aplus)::(VARG_CONSTR amult)
	 ::(VARG_CONSTR aone)::(VARG_CONSTR azero)::(VARG_CONSTR aopp)
	 ::(VARG_CONSTR aeq)::(VARG_CONSTR ainv)::(VARG_CONSTR rth)
         ::(VARG_CONSTR ainv_l)::l ->
         (fun () ->
           let (aminus_o,adiv_o) = opt_arg (None,None) l in
           add_field (constr_of a) (constr_of aplus) (constr_of amult)
             (constr_of aone) (constr_of azero) (constr_of aopp)
             (constr_of aeq) (constr_of ainv) (constr_of_opt a aminus_o)
             (constr_of_opt a adiv_o) (constr_of rth) (constr_of ainv_l))
       | _ -> anomaly "AddField")

(* Guesses the type and calls Field_Gen with the right theory *)
let field g =
  let evc = project g
  and env = pf_env g in
  let typ = constr_of_Constr (interp_tacarg (evc,env,[],[],Some g,get_debug ())
    <:tactic<
      Match Context With
      | [|-(eq ?1 ? ?)] -> ?1
      |	[|-(eqT ?1 ? ?)] -> ?1>>) in
  let th = VArg (Constr (lookup typ)) in
  (tac_interp [("FT",th)] [] (get_debug ()) <:tactic<Field_Gen FT>>) g

(* Declaration of Field *)
let _ = hide_tactic "Field" (function _ -> field)
