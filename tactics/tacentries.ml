(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Libobject
open Pcoq
open Egramml
open Egramcoq
open Vernacexpr

(**********************************************************************)
(* Tactic Notation                                                    *)

let interp_prod_item lev = function
  | TacTerm s -> GramTerminal s
  | TacNonTerm (loc, nt, (_, sep)) ->
      let EntryName (etyp, e) = interp_entry_name lev nt sep in
      GramNonTerminal (loc, etyp, e)

let make_terminal_status = function
  | GramTerminal s -> Some s
  | GramNonTerminal _ -> None

let make_fresh_key =
  let id = Summary.ref ~name:"TACTIC-NOTATION-COUNTER" 0 in
  fun () ->
    let cur = incr id; !id in
    let lbl = Id.of_string ("_" ^ string_of_int cur) in
    let kn = Lib.make_kn lbl in
    let (mp, dir, _) = KerName.repr kn in
    (** We embed the full path of the kernel name in the label so that the
        identifier should be unique. This ensures that including two modules
        together won't confuse the corresponding labels. *)
    let lbl = Id.of_string_soft (Printf.sprintf "%s#%s#%i"
      (ModPath.to_string mp) (DirPath.to_string dir) cur)
    in
    KerName.make mp dir (Label.of_id lbl)

type tactic_grammar_obj = {
  tacobj_key : KerName.t;
  tacobj_local : locality_flag;
  tacobj_tacgram : tactic_grammar;
  tacobj_tacpp : Pptactic.pp_tactic;
  tacobj_body : Id.t list * Tacexpr.glob_tactic_expr;
}

let check_key key =
  if Tacenv.check_alias key then
    error "Conflicting tactic notations keys. This can happen when including \
    twice the same module."

let cache_tactic_notation (_, tobj) =
  let key = tobj.tacobj_key in
  let () = check_key key in
  Tacenv.register_alias key tobj.tacobj_body;
  Egramcoq.extend_tactic_grammar key tobj.tacobj_tacgram;
  Pptactic.declare_notation_tactic_pprule key tobj.tacobj_tacpp

let open_tactic_notation i (_, tobj) =
  let key = tobj.tacobj_key in
  if Int.equal i 1 && not tobj.tacobj_local then
    Egramcoq.extend_tactic_grammar key tobj.tacobj_tacgram

let load_tactic_notation i (_, tobj) =
  let key = tobj.tacobj_key in
  let () = check_key key in
  (** Only add the printing and interpretation rules. *)
  Tacenv.register_alias key tobj.tacobj_body;
  Pptactic.declare_notation_tactic_pprule key tobj.tacobj_tacpp;
  if Int.equal i 1 && not tobj.tacobj_local then
    Egramcoq.extend_tactic_grammar key tobj.tacobj_tacgram

let subst_tactic_notation (subst, tobj) =
  let (ids, body) = tobj.tacobj_body in
  { tobj with
    tacobj_key = Mod_subst.subst_kn subst tobj.tacobj_key;
    tacobj_body = (ids, Tacsubst.subst_tactic subst body);
  }

let classify_tactic_notation tacobj = Substitute tacobj

let inTacticGrammar : tactic_grammar_obj -> obj =
  declare_object {(default_object "TacticGrammar") with
       open_function = open_tactic_notation;
       load_function = load_tactic_notation;
       cache_function = cache_tactic_notation;
       subst_function = subst_tactic_notation;
       classify_function = classify_tactic_notation}

let cons_production_parameter = function
| TacTerm _ -> None
| TacNonTerm (_, _, (id, _)) -> Some id

let add_tactic_notation (local,n,prods,e) =
  let ids = List.map_filter cons_production_parameter prods in
  let prods = List.map (interp_prod_item n) prods in
  let pprule = {
    Pptactic.pptac_level = n;
    pptac_prods = prods;
  } in
  let tac = Tacintern.glob_tactic_env ids (Global.env()) e in
  let parule = {
    tacgram_level = n;
    tacgram_prods = prods;
  } in
  let tacobj = {
    tacobj_key = make_fresh_key ();
    tacobj_local = local;
    tacobj_tacgram = parule;
    tacobj_tacpp = pprule;
    tacobj_body = (ids, tac);
  } in
  Lib.add_anonymous_leaf (inTacticGrammar tacobj)

(**********************************************************************)
(* ML Tactic entries                                                  *)

type ml_tactic_grammar_obj = {
  mltacobj_name : Tacexpr.ml_tactic_name;
  (** ML-side unique name *)
  mltacobj_prod : Tacexpr.raw_tactic_expr grammar_prod_item list list;
  (** Grammar rules generating the ML tactic. *)
}

exception NonEmptyArgument

(** ML tactic notations whose use can be restricted to an identifier are added
    as true Ltac entries. *)
let extend_atomic_tactic name entries =
  let open Tacexpr in
  let map_prod prods =
    let (hd, rem) = match prods with
    | GramTerminal s :: rem -> (s, rem)
    | _ -> assert false (** Not handled by the ML extension syntax *)
    in
    let empty_value = function
    | GramTerminal s -> raise NonEmptyArgument
    | GramNonTerminal (_, typ, e) ->
      let Genarg.Rawwit wit = typ in
      let inj x = TacArg (Loc.ghost, TacGeneric (Genarg.in_gen typ x)) in
      let default = epsilon_value inj e in
      match default with
      | None -> raise NonEmptyArgument
      | Some def -> Tacintern.intern_tactic_or_tacarg Tacintern.fully_empty_glob_sign def
    in
    try Some (hd, List.map empty_value rem) with NonEmptyArgument -> None
  in
  let entries = List.map map_prod entries in
  let add_atomic i args = match args with
  | None -> ()
  | Some (id, args) ->
    let args = List.map (fun a -> Tacexp a) args in
    let entry = { mltac_name = name; mltac_index = i } in
    let body = TacML (Loc.ghost, entry, args) in
    Tacenv.register_ltac false false (Names.Id.of_string id) body
  in
  List.iteri add_atomic entries

let cache_ml_tactic_notation (_, obj) =
  extend_ml_tactic_grammar obj.mltacobj_name obj.mltacobj_prod

let open_ml_tactic_notation i obj =
  if Int.equal i 1 then cache_ml_tactic_notation obj

let inMLTacticGrammar : ml_tactic_grammar_obj -> obj =
  declare_object { (default_object "MLTacticGrammar") with
    open_function = open_ml_tactic_notation;
    cache_function = cache_ml_tactic_notation;
    classify_function = (fun o -> Substitute o);
    subst_function = (fun (_, o) -> o);
  }

let add_ml_tactic_notation name prods =
  let obj = {
    mltacobj_name = name;
    mltacobj_prod = prods;
  } in
  Lib.add_anonymous_leaf (inMLTacticGrammar obj);
  extend_atomic_tactic name prods
