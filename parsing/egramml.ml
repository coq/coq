(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Compat
open Names
open Pcoq
open Genarg
open Vernacexpr

(** Making generic actions in type generic_argument *)

let make_generic_action
  (f:Loc.t -> ('b * raw_generic_argument) list -> 'a) pil =
  let rec make env = function
    | [] ->
	Gram.action (fun loc -> f (to_coqloc loc) env)
    | None :: tl -> (* parse a non-binding item *)
        Gram.action (fun _ -> make env tl)
    | Some (p, t) :: tl -> (* non-terminal *)
        Gram.action (fun v -> make ((p, Unsafe.inj t v) :: env) tl) in
  make [] (List.rev pil)

(** Grammar extensions declared at ML level *)

type grammar_prod_item =
  | GramTerminal of string
  | GramNonTerminal of
      Loc.t * argument_type * prod_entry_key * Id.t option

let make_prod_item = function
  | GramTerminal s -> (gram_token_of_string s, None)
  | GramNonTerminal (_,t,e,po) ->
      (symbol_of_prod_entry_key e, Option.map (fun p -> (p,t)) po)

let make_rule mkact pt =
  let (symbs,ntl) = List.split (List.map make_prod_item pt) in
  let act = make_generic_action mkact ntl in
  (symbs, act)

(** Vernac grammar extensions *)

let vernac_exts = ref []

let get_extend_vernac_rule (s, i) =
  try
    let find ((name, j), _) = String.equal name s && Int.equal i j in
    let (_, rules) = List.find find !vernac_exts in
    rules
  with
  | Failure _ -> raise Not_found

let extend_vernac_command_grammar s nt gl =
  let nt = Option.default Vernac_.command nt in
  vernac_exts := (s,gl) :: !vernac_exts;
  let mkact loc l = VernacExtend (s,List.map snd l) in
  let rules = [make_rule mkact gl] in
  maybe_uncurry (Gram.extend nt) (None,[(None, None, List.rev rules)])
