(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module G_proofs = G_proofs
module Metasyntax = Metasyntax
module Egramcoq = Egramcoq
module G_vernac = G_vernac
module Pcoq = Pcoq
module Tok = Tok
module CLexer = CLexer
module Egramml = Egramml
module Mltop = Mltop
module Vernacinterp = Vernacinterp
module Genintern = Genintern

module Extend =
  struct
    type 'a entry = 'a Extend.entry
    type ('self, 'a) symbol = ('self, 'a) Extend.symbol =
                            | Atoken : Tok.t -> ('self, string) symbol
                            | Alist1 : ('self, 'a) symbol -> ('self, 'a list) symbol
                            | Alist1sep : ('self, 'a) symbol * ('self, _) symbol -> ('self, 'a list) symbol
                            | Alist0 : ('self, 'a) symbol -> ('self, 'a list) symbol
                            | Alist0sep : ('self, 'a) symbol * ('self, _) symbol -> ('self, 'a list) symbol
                            | Aopt : ('self, 'a) symbol -> ('self, 'a option) symbol
                            | Aself : ('self, 'self) symbol
                                      | Anext : ('self, 'self) symbol
                                                | Aentry : 'a entry -> ('self, 'a) symbol
                            | Aentryl : 'a entry * int -> ('self, 'a) symbol
                            | Arules : 'a rules list -> ('self, 'a) symbol
     and ('self, 'a, 'r) rule = ('self, 'a, 'r) Extend.rule =
                              | Stop : ('self, 'r, 'r) rule
                                       | Next : ('self, 'a, 'r) rule * ('self, 'b) symbol -> ('self, 'b -> 'a, 'r) rule
     and ('a, 'r) norec_rule = ('a, 'r) Extend.norec_rule =
                                 { norec_rule : 's. ('s, 'a, 'r) rule }
     and 'a rules = 'a Extend.rules =
                  | Rules : ('act, Loc.t -> 'a) norec_rule * 'act -> 'a rules
    type gram_assoc = Extend.gram_assoc = NonA | RightA | LeftA
    type 'a production_rule = 'a Extend.production_rule =
                            | Rule : ('a, 'act, Loc.t -> 'a) rule * 'act -> 'a production_rule
    type 'a single_extend_statment = string option * gram_assoc option * 'a production_rule list
    type gram_position = Extend.gram_position =
      | First
      | Last
      | Before of string
      | After of string
      | Level of string
    type 'a extend_statment = Extend.gram_position option * 'a single_extend_statment list

    type 'a user_symbol = 'a Extend.user_symbol =
                        | Ulist1 of 'a user_symbol
                        | Ulist1sep of 'a user_symbol * string
                        | Ulist0 of 'a user_symbol
                        | Ulist0sep of 'a user_symbol * string
                        | Uopt of 'a user_symbol
                        | Uentry of 'a
                        | Uentryl of 'a * int
  end
