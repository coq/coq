(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Mod_subst
open Coqlib

(* Interpretation of constr's *)
let constr_of c = Constrintern.interp_constr Evd.empty (Global.env()) c

(* Construction of constants *)
let constant dir s = gen_constant "Field" ("field"::dir) s
let init_constant s = gen_constant_in_modules "Field" init_modules s

(* To deal with the optional arguments *)
let constr_of_opt a opt =
  let ac = constr_of a in
  let ac3 = mkArrow ac (mkArrow ac ac) in
  match opt with
  | None -> mkApp (init_constant "None",[|ac3|])
  | Some f -> mkApp (init_constant "Some",[|ac3;constr_of f|])

(* Table of theories *)
let th_tab = ref (Gmap.empty : (constr,constr) Gmap.t)

let lookup env typ =
  try Gmap.find typ !th_tab
  with Not_found ->
    errorlabstrm "field"
      (str "No field is declared for type" ++ spc() ++
      Printer.pr_lconstr_env env typ)

let _ =
  let init () = th_tab := Gmap.empty in
  let freeze () = !th_tab in
  let unfreeze fs = th_tab := fs in
  Summary.declare_summary "field"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init }

let load_addfield _ = ()
let cache_addfield (_,(typ,th)) = th_tab := Gmap.add typ th !th_tab
let subst_addfield (subst,(typ,th as obj)) =
  let typ' = subst_mps subst typ in
  let th' = subst_mps subst th in
    if typ' == typ && th' == th then obj else
      (typ',th')

(* Declaration of the Add Field library object *)
let (in_addfield,out_addfield)=
  Libobject.declare_object {(Libobject.default_object "ADD_FIELD") with
       Libobject.open_function = (fun i o -> if i=1 then cache_addfield o);
       Libobject.cache_function = cache_addfield;
       Libobject.subst_function = subst_addfield;
       Libobject.classify_function = (fun a -> Libobject.Substitute a)}

(* Adds a theory to the table *)
let add_field a aplus amult aone azero aopp aeq ainv aminus_o adiv_o rth
  ainv_l =
  begin
    (try
      Ring.add_theory true true false a None None None aplus amult aone azero
        (Some aopp) aeq rth Quote.ConstrSet.empty
     with | UserError("Add Semi Ring",_) -> ());
    let th = mkApp ((constant ["LegacyField_Theory"] "Build_Field_Theory"),
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

VERNAC ARGUMENT EXTEND divarg
| [ "div" ":=" constr(adiv) ] -> [ adiv ]
END

VERNAC ARGUMENT EXTEND minusarg
| [ "minus" ":=" constr(aminus) ] -> [ aminus ]
END

(*
(* The v7->v8 translator needs printers, then temporary use ARGUMENT EXTEND...*)
VERNAC ARGUMENT EXTEND minus_div_arg
| [ "with" minusarg(m) divarg_opt(d) ] -> [ Some m, d ]
| [ "with" divarg(d) minusarg_opt(m) ] -> [ m, Some d ]
| [ ] -> [ None, None ]
END
*)

(* For the translator, otherwise the code above is OK *)
open Ppconstr
let pp_minus_div_arg _prc _prlc _prt (omin,odiv) =
  if omin=None && odiv=None then mt() else
    spc() ++ str "with" ++
    pr_opt (fun c -> str "minus := " ++ _prc c) omin ++
    pr_opt (fun c -> str "div := " ++ _prc c) odiv
(*
let () =
  Pptactic.declare_extra_genarg_pprule true
    (rawwit_minus_div_arg,pp_minus_div_arg)
    (globwit_minus_div_arg,pp_minus_div_arg)
    (wit_minus_div_arg,pp_minus_div_arg)
*)
ARGUMENT EXTEND minus_div_arg
  TYPED AS constr_opt * constr_opt
  PRINTED BY pp_minus_div_arg
| [ "with" minusarg(m) divarg_opt(d) ] -> [ Some m, d ]
| [ "with" divarg(d) minusarg_opt(m) ] -> [ m, Some d ]
| [ ] -> [ None, None ]
END

VERNAC COMMAND EXTEND Field
  [ "Add" "Legacy" "Field"
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

(* Guesses the type and calls field_gen with the right theory *)
let field g =
  Coqlib.check_required_library ["Coq";"field";"LegacyField"];
  let typ =
    try match Hipattern.match_with_equation (pf_concl g) with
      | _,_,Hipattern.PolymorphicLeibnizEq (t,_,_) -> t
      | _ -> raise Exit
    with Hipattern.NoEquationFound | Exit ->
      error "The statement is not built from Leibniz' equality" in
  let th = VConstr ([],lookup (pf_env g) typ) in
  (interp_tac_gen [(id_of_string "FT",th)] [] (get_debug ())
    <:tactic< match goal with |- (@eq _ _ _) => field_gen FT end >>) g

(* Verifies that all the terms have the same type and gives the right theory *)
let guess_theory env evc = function
  | c::tl ->
    let t = type_of env evc c in
    if List.exists (fun c1 ->
      not (Reductionops.is_conv env evc t (type_of env evc c1))) tl then
      errorlabstrm "Field:" (str" All the terms must have the same type")
    else
      lookup env t
  | [] -> anomaly "Field: must have a non-empty constr list here"

(* Guesses the type and calls Field_Term with the right theory *)
let field_term l g =
  Coqlib.check_required_library ["Coq";"field";"LegacyField"];
  let env = (pf_env g)
  and evc = (project g) in
  let th = valueIn (VConstr ([],guess_theory env evc l))
  and nl = List.map (fun x -> valueIn (VConstr ([],x))) (Quote.sort_subterm g l) in
  (List.fold_right
    (fun c a ->
     let tac = (Tacinterp.interp <:tactic<(Field_Term $th $c)>>) in
     Tacticals.tclTHENFIRSTn tac [|a|]) nl Tacticals.tclIDTAC) g

(* Declaration of Field *)

TACTIC EXTEND legacy_field
| [ "legacy" "field" ] -> [ field ]
| [ "legacy" "field" ne_constr_list(l) ] -> [ field_term l ]
END
