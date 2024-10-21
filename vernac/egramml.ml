(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Extend
open Procq
open Genarg
open Vernacexpr

(** Grammar extensions declared at ML level *)

type 's grammar_prod_item =
  | GramTerminal of string
  | GramNonTerminal :
      ('a raw_abstract_argument_type * ('s, _, 'a) Symbol.t) Loc.located -> 's grammar_prod_item

type 'a ty_arg = ('a -> raw_generic_argument)

type ('self, 'tr, _, 'r) ty_rule =
| TyStop : ('self, Gramlib.Grammar.norec, 'r, 'r) ty_rule
| TyNext : ('self, _, 'a, 'r) ty_rule * ('self, _, 'b) Symbol.t * 'b ty_arg option ->
  ('self, Gramlib.Grammar.mayrec, 'b -> 'a, 'r) ty_rule

type ('self, 'r) any_ty_rule =
| AnyTyRule : ('self, _, 'act, Loc.t -> 'r) ty_rule -> ('self, 'r) any_ty_rule

let rec ty_rule_of_gram = function
| [] -> AnyTyRule TyStop
| GramTerminal s :: rem ->
  let AnyTyRule rem = ty_rule_of_gram rem in
  let tok = Procq.Symbol.token (Procq.terminal s) in
  let r = TyNext (rem, tok, None) in
  AnyTyRule r
| GramNonTerminal (_, (t, tok)) :: rem ->
  let AnyTyRule rem = ty_rule_of_gram rem in
  let inj = Some (fun obj -> Genarg.in_gen t obj) in
  let r = TyNext (rem, tok, inj) in
  AnyTyRule r

let rec ty_erase : type s tr a r. (s, tr, a, r) ty_rule -> (s, tr, a, r) Procq.Rule.t = function
| TyStop -> Procq.Rule.stop
| TyNext (rem, tok, _) -> Procq.Rule.next (ty_erase rem) tok

type 'r gen_eval = Loc.t -> raw_generic_argument list -> 'r

let rec ty_eval : type s tr a. (s, tr, a, Loc.t -> s) ty_rule -> s gen_eval -> a = function
| TyStop -> fun f loc -> f loc []
| TyNext (rem, tok, None) -> fun f _ -> ty_eval rem f
| TyNext (rem, tok, Some inj) -> fun f x ->
  let f loc args = f loc (inj x :: args) in
  ty_eval rem f

let make_rule f prod =
  let AnyTyRule ty_rule = ty_rule_of_gram (List.rev prod) in
  let symb = ty_erase ty_rule in
  let f loc l = f loc (List.rev l) in
  let act = ty_eval ty_rule f in
  Procq.Production.make symb act

let rec proj_symbol : type a b c. (a, b, c) ty_user_symbol -> (a, b, c) genarg_type = function
| TUentry a -> ExtraArg a
| TUentryl (a,l) -> ExtraArg a
| TUopt(o) -> OptArg (proj_symbol o)
| TUlist1 l -> ListArg (proj_symbol l)
| TUlist1sep (l,_) -> ListArg (proj_symbol l)
| TUlist0 l -> ListArg (proj_symbol l)
| TUlist0sep (l,_) -> ListArg (proj_symbol l)

(** Vernac grammar extensions *)

let vernac_exts = Hashtbl.create 211

let get_extend_vernac_rule s =
  snd (Hashtbl.find vernac_exts s)

let declare_vernac_command_grammar ~allow_override s nt gl =
  let () = if not allow_override && Hashtbl.mem vernac_exts s
    then CErrors.anomaly Pp.(str "bad vernac extend: " ++ str s.ext_entry ++ str ", " ++ int s.ext_index)
  in
  let nt = Option.default Pvernac.Vernac_.command nt in
  Hashtbl.add vernac_exts s (nt, gl)

type any_extend_statement = Extend : 'a Entry.t * 'a extend_statement -> any_extend_statement

let extend_vernac_command_grammar s =
  let nt, gl = Hashtbl.find vernac_exts s in
  let mkact loc l = VernacSynterp (VernacExtend (s, l)) in
  let rules = [make_rule mkact gl] in
  if Procq.Entry.is_empty nt then
    (* Small hack to tolerate empty entries in VERNAC { ... } EXTEND *)
    Extend (nt, (Procq.Fresh (Gramlib.Gramext.First, [None, None, rules])))
  else
    Extend (nt, (Procq.Reuse (None, rules)))

let to_extend_rules (Extend (nt, r)) = [ExtendRule (nt,r)]

let extend_vernac = Procq.create_grammar_command "VernacExtend" {
    gext_fun = (fun s st -> to_extend_rules @@ extend_vernac_command_grammar s, st);
    gext_eq = (==); (* FIXME *)
  }

let extend_vernac_command_grammar ~undoable s =
  if undoable then Procq.extend_grammar_command extend_vernac s
  else
    let Extend (nt, r) = extend_vernac_command_grammar s in
    grammar_extend nt r

let grammar_exts = Hashtbl.create 21

let declare_grammar_ext ~uid e =
  let () = if Hashtbl.mem grammar_exts uid
    then CErrors.anomaly Pp.(str "bad grammar extend uid: " ++ str uid)
  in
  Hashtbl.add grammar_exts uid e

let extend_grammar = Procq.create_grammar_command "GrammarExtend" {
    gext_fun = (fun s st -> to_extend_rules @@ Hashtbl.find grammar_exts s, st);
    gext_eq = (==); (* FIXME *)
  }

let grammar_extend ?plugin_uid nt r = match plugin_uid with
  | None ->
    Procq.grammar_extend nt r
  | Some (plugin,uid) ->
    let uid = plugin^":"^uid in
    declare_grammar_ext ~uid (Extend (nt, r));
    Mltop.add_init_function plugin (fun () ->
        Procq.extend_grammar_command extend_grammar uid)
