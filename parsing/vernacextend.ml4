(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo q_MLast.cmo" i*)

(* $Id$ *)

open Util
open Genarg
open Q_util
open Q_coqast
open Argextend
open Tacextend
open Pcoq
open Egrammar

let rec make_let e = function
  | [] -> e
  | GramNonTerminal(loc,t,_,Some p)::l ->
      let p = Names.string_of_id p in
      let loc = join_loc loc (MLast.loc_of_expr e) in
      let e = make_let e l in
      <:expr< let $lid:p$ = Genarg.out_gen $make_rawwit loc t$ $lid:p$ in $e$ >>
  | _::l -> make_let e l

let add_clause s (_,pt,e) l =
  let p = make_patt pt in
  let w = Some (make_when (MLast.loc_of_expr e) pt) in
  (p, w, make_let e pt)::l

let check_unicity s l =
  let l' = List.map (fun (_,l,_) -> extract_signature l) l in
  if not (Util.list_distinct l') then
    Pp.warning_with !Pp_control.err_ft
      ("Two distinct rules of entry "^s^" have the same\n"^
      "non-terminals in the same order: put them in distinct vernac entries")

let make_clauses s l =
  check_unicity s l;
  let default =
    (<:patt< _ >>,None,<:expr< failwith "Vernac extension: cannot occur" >>) in
  List.fold_right (add_clause s) l [default]

let mlexpr_of_clause =
  mlexpr_of_list
    (fun (a,b,c) -> mlexpr_of_list make_prod_item (GramTerminal a::b))

let declare_command loc s cl =
  let gl = mlexpr_of_clause cl in
  let icl = make_clauses s cl in
  <:str_item<
    declare
      open Pcoq;
      open Extrawit;
      try Vernacinterp.vinterp_add $mlexpr_of_string s$ (fun [ $list:icl$ ])
      with e -> Pp.pp (Cerrors.explain_exn e);
      Egrammar.extend_vernac_command_grammar $mlexpr_of_string s$ $gl$;
    end
  >>

open Pcaml

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "VERNAC"; "COMMAND"; "EXTEND"; s = UIDENT;
        OPT "|"; l = LIST1 rule SEP "|";
        "END" ->
         declare_command loc s l ] ]
  ;
  rule:
    [ [ "["; s = STRING; l = LIST0 args; "]"; "->"; "["; e = Pcaml.expr; "]"
        ->
      if s = "" then Util.user_err_loc (loc,"",Pp.str"Command name is empty.");
      (s,l,<:expr< fun () -> $e$ >>)
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
