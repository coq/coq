(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Names
open Pp
open Proof_type
open Tacinterp
open Tacmach
open Term
open Typing
open Util
open Vernacinterp
open Vernacexpr
open Tacexpr

(* Interpretation of constr's *)
let constr_of c = Constrintern.interp_constr Evd.empty (Global.env()) c

(* Construction of constants *)
let constant dir s =
  let dir = make_dirpath
    (List.map id_of_string (List.rev ("Coq"::"field"::dir))) in
  let id = id_of_string s in
  try 
    Declare.global_reference_in_absolute_module dir id
  with Not_found ->
    anomaly ("Field: cannot find "^
	     (Libnames.string_of_qualid (Libnames.make_qualid dir id)))

(* To deal with the optional arguments *)
let constr_of_opt a opt =
  let ac = constr_of a in
  match opt with
  | None -> mkApp ((constant ["Field_Compl"] "None"),[|ac|])
  | Some f -> mkApp ((constant ["Field_Compl"] "Some"),[|ac;constr_of f|])

(* Table of theories *)
let th_tab = ref (Gmap.empty : (constr,constr) Gmap.t)

let lookup typ = Gmap.find typ !th_tab

let _ = 
  let init () = th_tab := Gmap.empty in
  let freeze () = !th_tab in
  let unfreeze fs = th_tab := fs in
  Summary.declare_summary "field"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init;
      Summary.survive_section   = false }

let load_addfield _ = ()
let cache_addfield (_,(typ,th)) = th_tab := Gmap.add typ th !th_tab
let subst_addfield (_,subst,(typ,th as obj)) =
  let typ' = subst_mps subst typ in
  let th' = subst_mps subst th in
    if typ' == typ && th' == th then obj else
      (typ',th')
let export_addfield x = Some x

(* Declaration of the Add Field library object *)
let (in_addfield,out_addfield)=
  Libobject.declare_object {(Libobject.default_object "ADD_FIELD") with
       Libobject.open_function = (fun i o -> if i=1 then cache_addfield o);
       Libobject.cache_function = cache_addfield;
       Libobject.subst_function = subst_addfield;
       Libobject.classify_function = (fun (_,a) -> Libobject.Substitute a);
       Libobject.export_function = export_addfield }

(* Adds a theory to the table *)
let add_field a aplus amult aone azero aopp aeq ainv aminus_o adiv_o rth
  ainv_l =
  begin
    (try
      Ring.add_theory true true false a None None None aplus amult aone azero
        (Some aopp) aeq rth Quote.ConstrSet.empty
     with | UserError("Add Semi Ring",_) -> ());
    let th = mkApp ((constant ["Field_Theory"] "Build_Field_Theory"),
      [|a;aplus;amult;aone;azero;aopp;aeq;ainv;aminus_o;adiv_o;rth;ainv_l|]) in
    begin
      let _ = type_of (Global.env ()) Evd.empty th in ();
      Lib.add_anonymous_leaf (in_addfield (a,th))
    end
  end

(* Vernac command declaration *)
open Extend
open Pcoq
open Genarg

let wit_minus_div_arg, rawwit_minus_div_arg = Genarg.create_arg "minus_div_arg"
let minus_div_arg = create_generic_entry "minus_div_arg" rawwit_minus_div_arg
let _ = Tacinterp.add_genarg_interp "minus_div_arg"
  (fun ist gl x ->
    (in_gen wit_minus_div_arg
      (out_gen (wit_pair (wit_opt wit_constr) (wit_opt wit_constr))
	(Tacinterp.genarg_interp ist gl
	  (in_gen (wit_pair (wit_opt rawwit_constr) (wit_opt rawwit_constr))
	    (out_gen rawwit_minus_div_arg x))))))

open Pcoq.Constr
GEXTEND Gram
  GLOBAL: minus_div_arg;
  minus_arg: [ [ IDENT "minus"; ":="; aminus = constr -> aminus ] ];
  div_arg: [ [ IDENT "div"; ":="; adiv = constr -> adiv ] ];
  minus_div_arg:
    [ [ "with"; m = minus_arg; d = OPT div_arg -> Some m, d
      | "with"; d = div_arg; m = OPT minus_arg -> m, Some d
      | -> None, None ] ];
END

VERNAC COMMAND EXTEND Field
  [ "Add" "Field" 
      constr(a) constr(aplus) constr(amult) constr(aone)
      constr(azero) constr(aopp) constr(aeq)
      constr(ainv) constr(rth) constr(ainv_l) minus_div_arg(md) ]
    -> [ let (aminus_o, adiv_o) = md in
         add_field
           (constr_of a) (constr_of aplus) (constr_of amult)
           (constr_of aone) (constr_of azero) (constr_of aopp)
           (constr_of aeq) (constr_of ainv) (constr_of_opt a aminus_o)
           (constr_of_opt a adiv_o) (constr_of rth) (constr_of ainv_l) ]
END

(* Guesses the type and calls Field_Gen with the right theory *)
let field g =
  Library.check_required_library ["Coq";"field";"Field"];
  let ist = { lfun=[]; lmatch=[]; debug=get_debug () } in
  let typ = constr_of_VConstr (pf_env g) (val_interp ist g
    <:tactic<
      Match Context With
      | [|- (eq ?1 ? ?)] -> ?1
      | [|- (eqT ?1 ? ?)] -> ?1>>) in
  let th = VConstr (lookup typ) in
  (tac_interp [(id_of_string "FT",th)] [] (get_debug ())
    <:tactic<
      Match Context With
      | [|- (eq ?1 ?2 ?3)] ->
        Let t = '(eqT ?1 ?2 ?3) In
        Cut t;[Intro;
          (Match Context With
          | [id:t |- ?] -> Rewrite id;Reflexivity)|Field_Gen FT]
      | [|- (eqT ? ? ?)] -> Field_Gen FT>>) g

(* Verifies that all the terms have the same type and gives the right theory *)
let guess_theory env evc = function
  | c::tl ->
    let t = type_of env evc c in
    if List.exists (fun c1 ->
      not (Reductionops.is_conv env evc t (type_of env evc c1))) tl then
      errorlabstrm "Field:" (str" All the terms must have the same type")
    else
      lookup t
  | [] -> anomaly "Field: must have a non-empty constr list here"

(* Guesses the type and calls Field_Term with the right theory *)
let field_term l g =
  Library.check_required_library ["Coq";"field";"Field"];
  let env = (pf_env g)
  and evc = (project g) in
  let th = valueIn (VConstr (guess_theory env evc l))
  and nl = List.map (fun x -> valueIn (VConstr x)) (Quote.sort_subterm g l) in
  (List.fold_right
    (fun c a ->
     let tac = (Tacinterp.interp <:tactic<(Field_Term $th $c)>>) in
     Tacticals.tclTHENFIRSTn tac [|a|]) nl Tacticals.tclIDTAC) g

(* Declaration of Field *)

TACTIC EXTEND Field
| [ "Field" ] -> [ field ]
| [ "Field" ne_constr_list(l) ] -> [ field_term l ]
END
