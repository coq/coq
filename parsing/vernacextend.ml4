(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "tools/compat5b.cmo" i*)

open Util
open Genarg
open Q_util
open Q_coqast
open Argextend
open Tacextend
open Pcoq
open Egrammar
open Compat

let rec make_let e = function
  | [] -> e
  | GramNonTerminal(loc,t,_,Some p)::l ->
      let p = Names.string_of_id p in
      let loc = join_loc loc (MLast.loc_of_expr e) in
      let e = make_let e l in
      <:expr< let $lid:p$ = Genarg.out_gen $make_rawwit loc t$ $lid:p$ in $e$ >>
  | _::l -> make_let e l

let check_unicity s l =
  let l' = List.map (fun (_,l,_) -> extract_signature l) l in
  if not (Util.list_distinct l') then
    Pp.warning_with !Pp_control.err_ft
      ("Two distinct rules of entry "^s^" have the same\n"^
      "non-terminals in the same order: put them in distinct vernac entries")

let make_clause (_,pt,e) =
  (make_patt pt,
   vala (Some (make_when (MLast.loc_of_expr e) pt)),
   make_let e pt)

let make_fun_clauses loc s l =
  check_unicity s l;
  Compat.make_fun loc (List.map make_clause l)

let mlexpr_of_clause =
  mlexpr_of_list
    (fun (a,b,c) -> mlexpr_of_list make_prod_item 
       (Option.List.cons (Option.map (fun a -> GramTerminal a) a) b))

let declare_command loc s nt cl =
  let gl = mlexpr_of_clause cl in
  let funcl = make_fun_clauses loc s cl in
  declare_str_items loc
    [ <:str_item< do {
	try Vernacinterp.vinterp_add $mlexpr_of_string s$ $funcl$
	with e -> Pp.pp (Errors.print e);
	Egrammar.extend_vernac_command_grammar $mlexpr_of_string s$ $nt$ $gl$
      } >> ]

open Pcaml
open PcamlSig

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "VERNAC"; "COMMAND"; "EXTEND"; s = UIDENT;
        OPT "|"; l = LIST1 rule SEP "|";
        "END" ->
         declare_command loc s <:expr<None>> l 
      | "VERNAC"; nt = LIDENT ; "EXTEND"; s = UIDENT;
        OPT "|"; l = LIST1 rule SEP "|";
        "END" ->
          declare_command loc s <:expr<Some $lid:nt$>> l ] ]
  ;
  (* spiwack: comment-by-guessing: it seems that the isolated string (which
      otherwise could have been another argument) is not passed to the
      VernacExtend interpreter function to discriminate between the clauses. *)
  rule:
    [ [ "["; s = STRING; l = LIST0 args; "]"; "->"; "["; e = Pcaml.expr; "]"
        ->
      if s = "" then Util.user_err_loc (loc,"",Pp.str"Command name is empty.");
      (Some s,l,<:expr< fun () -> $e$ >>)
      | "[" ; "-" ; l = LIST1 args ; "]" ; "->" ; "[" ; e = Pcaml.expr ; "]" ->
	  (None,l,<:expr< fun () -> $e$ >>)
    ] ]
  ;
  args:
    [ [ e = LIDENT; "("; s = LIDENT; ")" ->
        let t, g = interp_entry_name false None e "" in
        GramNonTerminal (loc, t, g, Some (Names.id_of_string s))
      | e = LIDENT; "("; s = LIDENT; ","; sep = STRING; ")" ->
        let t, g = interp_entry_name false None e sep in
        GramNonTerminal (loc, t, g, Some (Names.id_of_string s))
      | s = STRING ->
        GramTerminal s
    ] ]
  ;
  END
;;
