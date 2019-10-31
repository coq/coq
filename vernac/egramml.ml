(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Extend
open Pcoq
open Genarg
open Vernacexpr

(** Grammar extensions declared at ML level *)

type 's grammar_prod_item =
  | GramTerminal of string
  | GramNonTerminal :
      ('a raw_abstract_argument_type * ('s, _, 'a) symbol) Loc.located -> 's grammar_prod_item

type 'a ty_arg = ('a -> raw_generic_argument)

type ('self, 'tr, _, 'r) ty_rule =
| TyStop : ('self, Extend.norec, 'r, 'r) ty_rule
| TyNext : ('self, _, 'a, 'r) ty_rule * ('self, _, 'b) Extend.symbol * 'b ty_arg option ->
  ('self, Extend.mayrec, 'b -> 'a, 'r) ty_rule

type ('self, 'r) any_ty_rule =
| AnyTyRule : ('self, _, 'act, Loc.t -> 'r) ty_rule -> ('self, 'r) any_ty_rule

let rec ty_rule_of_gram = function
| [] -> AnyTyRule TyStop
| GramTerminal s :: rem ->
  let AnyTyRule rem = ty_rule_of_gram rem in
  let tok = Atoken (CLexer.terminal s) in
  let r = TyNext (rem, tok, None) in
  AnyTyRule r
| GramNonTerminal (_, (t, tok)) :: rem ->
  let AnyTyRule rem = ty_rule_of_gram rem in
  let inj = Some (fun obj -> Genarg.in_gen t obj) in
  let r = TyNext (rem, tok, inj) in
  AnyTyRule r

let rec ty_erase : type s tr a r. (s, tr, a, r) ty_rule -> (s, tr, a, r) Extend.rule = function
| TyStop -> Extend.Stop
| TyNext (rem, tok, _) -> Extend.Next (ty_erase rem, tok)

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
  Extend.Rule (symb, act)

let rec proj_symbol : type a b c. (a, b, c) ty_user_symbol -> (a, b, c) genarg_type = function
| TUentry a -> ExtraArg a
| TUentryl (a,l) -> ExtraArg a
| TUopt(o) -> OptArg (proj_symbol o)
| TUlist1 l -> ListArg (proj_symbol l)
| TUlist1sep (l,_) -> ListArg (proj_symbol l)
| TUlist0 l -> ListArg (proj_symbol l)
| TUlist0sep (l,_) -> ListArg (proj_symbol l)

(** Vernac grammar extensions *)

let vernac_exts = ref []

let get_extend_vernac_rule (s, i) =
  try
    let find ((name, j), _) = String.equal name s && CInt.equal i j in
    let (_, rules) = List.find find !vernac_exts in
    rules
  with
  | Failure _ -> raise Not_found

let extend_vernac_command_grammar s nt gl =
  let nt = COption.default Pvernac.Vernac_.command nt in
  vernac_exts := (s,gl) :: !vernac_exts;
  let mkact loc l = VernacExtend (s, l) in
  let rules = [make_rule mkact gl] in
  grammar_extend nt None (None, [None, None, rules])
