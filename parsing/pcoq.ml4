(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Util

(* The lexer of Coq *)

(* Note: removing a token.
   We do nothing because [remove_token] is called only when removing a grammar
   rule with [Grammar.delete_rule]. The latter command is called only when
   unfreezing the state of the grammar entries (see GRAMMAR summary, file
   env/metasyntax.ml). Therefore, instead of removing tokens one by one,
   we unfreeze the state of the lexer. This restores the behaviour of the
   lexer. B.B. *)

let lexer = {
  Token.func = Lexer.func;
  Token.using = Lexer.add_token;
  Token.removing = (fun _ -> ());
  Token.tparse = Lexer.tparse;
  Token.text = Lexer.token_text }

module L =
  struct
    let lexer = lexer
  end

(* The parser of Coq *)

module G = Grammar.Make(L)

let grammar_delete e rls =
  List.iter
    (fun (_,_,lev) ->
       List.iter (fun (pil,_) -> G.delete_rule e pil) (List.rev lev))
    (List.rev rls)

type typed_entry =
  | Ast of Coqast.t G.Entry.e
  | ListAst of Coqast.t list G.Entry.e

type ext_kind =
  | ByGrammar of
      typed_entry * Gramext.position option *
      (string option * Gramext.g_assoc option *
       (Gramext.g_symbol list * Gramext.g_action) list) list
  | ByGEXTEND of (unit -> unit) * (unit -> unit)

let camlp4_state = ref []

(* The apparent parser of Coq; encapsulate G to keep track of the
   extensions. *)
module Gram =
  struct
    type parsable = G.parsable
    let parsable = G.parsable
    let tokens = G.tokens
    module Entry = G.Entry
    module Unsafe = G.Unsafe

    let extend e pos rls =
      camlp4_state :=
      (ByGEXTEND ((fun () -> grammar_delete e rls),
                  (fun () -> G.extend e pos rls)))
      :: !camlp4_state;
      G.extend e pos rls
    let delete_rule e pil =
      errorlabstrm "Pcoq.delete_rule"
        [< 'sTR "GDELETE_RULE forbidden." >]
  end


(* This extension command is used by the Grammar constr *)

let grammar_extend te pos rls =
  camlp4_state := ByGrammar (te,pos,rls) :: !camlp4_state;
  match te with
    | Ast e ->  G.extend e pos rls
    | ListAst e -> G.extend e pos rls

(* n is the number of extended entries (not the number of Grammar commands!)
   to remove. *)
let rec remove_grammars n =
  if n>0 then
    (match !camlp4_state with
       | [] -> anomaly "Pcoq.remove_grammars: too many rules to remove"
       | ByGrammar(Ast e,_,rls)::t ->
           grammar_delete e rls;
           camlp4_state := t;
           remove_grammars (n-1)
       | ByGrammar(ListAst e,_,rls)::t ->
           grammar_delete e rls;
           camlp4_state := t;
           remove_grammars (n-1)
       | ByGEXTEND (undo,redo)::t ->
           undo();
           camlp4_state := t;
           remove_grammars n;
           redo();
           camlp4_state := ByGEXTEND (undo,redo) :: !camlp4_state)

(* An entry that checks we reached the end of the input. *)
let eoi_entry en =
  let e = Gram.Entry.create ((Gram.Entry.name en) ^ "_eoi") in
  GEXTEND Gram
    e: [ [ x = en; EOI -> x ] ]
    ;
  END;
  e

let map_entry f en =
  let e = Gram.Entry.create ((Gram.Entry.name en) ^ "_map") in
  GEXTEND Gram
    e: [ [ x = en -> f x ] ]
    ;
  END;
  e

(* Parse a string, does NOT check if the entire string was read
   (use eoi_entry) *)

let parse_string f x =
  let strm = Stream.of_string x in Gram.Entry.parse f (Gram.parsable strm)

let slam_ast (_,fin) id ast =
  match id with
    | Coqast.Nvar ((deb,_), s) -> Coqast.Slam ((deb,fin), Some s, ast)
    | Coqast.Nmeta ((deb,_), s) -> Coqast.Smetalam ((deb,fin), s, ast)
    | _ -> invalid_arg "Ast.slam_ast"

(* This is to interpret the macro $ABSTRACT used in binders        *)
(* $ABSTRACT should occur in this configuration :                  *)
(* ($ABSTRACT name (s1 a1 ($LIST l1)) ... (s2 an ($LIST ln)) b)    *)
(* where li is id11::...::id1p1 and it produces the ast            *)
(* (s1' a1 [id11]...[id1p1](... (sn' an [idn1]...[idnpn]b)...))    *)
(* where s1' is overwritten by name if s1 is $BINDER otherwise s1  *)

let abstract_binder_ast (_,fin as loc) name a b =
  match a with
    | Coqast.Node((deb,_),s,d::l) ->
	let s' = if s="BINDER" then name else s in
	Coqast.Node((deb,fin),s', [d; List.fold_right (slam_ast loc) l b])
    | _ -> invalid_arg "Bad usage of $ABSTRACT macro"

let abstract_binders_ast loc name a b =
  match a with
    | Coqast.Node(_,"BINDERS",l) ->
	List.fold_right (abstract_binder_ast loc name) l b
    | _ -> invalid_arg "Bad usage of $ABSTRACT macro"

type entry_type = ETast | ETastl
    
let entry_type ast =
  match ast with
    | Coqast.Id (_, "LIST") -> ETastl
    | Coqast.Id (_, "AST") -> ETast
    | _ -> invalid_arg "Ast.entry_type"

let type_of_entry e =
  match e with
    | Ast _ -> ETast
    | ListAst _ -> ETastl

type gram_universe = (string, typed_entry) Hashtbl.t

let trace = ref false

(* The univ_tab is not part of the state. It contains all the grammar that
   exist or have existed before in the session. *)

let univ_tab = Hashtbl.create 7

let get_univ s =
  try 
    Hashtbl.find univ_tab s 
  with Not_found ->
    if !trace then begin 
      Printf.eprintf "[Creating univ %s]\n" s; flush stderr; () 
    end;
    let u = s, Hashtbl.create 29 in Hashtbl.add univ_tab s u; u
	
let get_entry (u, utab) s =
  try 
    Hashtbl.find utab s 
  with Not_found -> 
    errorlabstrm "Pcoq.get_entry"
      [< 'sTR"unknown grammar entry "; 'sTR u; 'sTR":"; 'sTR s >]
      
let new_entry etyp (u, utab) s =
  let ename = u ^ ":" ^ s in
  let e =
    match etyp with
      | ETast -> Ast (Gram.Entry.create ename)
      | ETastl -> ListAst (Gram.Entry.create ename)
  in
  Hashtbl.add utab s e; e
    
let create_entry (u, utab) s etyp =
  try
    let e = Hashtbl.find utab s in
    if type_of_entry e <> etyp then
      failwith ("Entry " ^ u ^ ":" ^ s ^ " already exists with another type");
    e
  with Not_found ->
    if !trace then begin
      Printf.eprintf "[Creating entry %s:%s]\n" u s; flush stderr; ()
    end;
    new_entry etyp (u, utab) s
      
let force_entry_type (u, utab) s etyp =
  try
    let entry = Hashtbl.find utab s in
    let extyp = type_of_entry entry in
    if etyp = extyp then 
      entry
    else begin
      prerr_endline
        ("Grammar entry " ^ u ^ ":" ^ s ^
         " redefined with another type;\n older entry hidden.");
      Hashtbl.remove utab s;
      new_entry etyp (u, utab) s
    end
  with Not_found -> 
    new_entry etyp (u, utab) s

(* Grammar entries *)

module Constr =
  struct
    let uconstr = snd (get_univ "constr")
    let gec s =
      let e = Gram.Entry.create ("Constr." ^ s) in
      Hashtbl.add uconstr s (Ast e); e

    let gec_list s =
      let e = Gram.Entry.create ("Constr." ^ s) in
      Hashtbl.add uconstr s (ListAst e); e

    let constr = gec "constr"
    let constr0 = gec "constr0"
    let constr1 = gec "constr1"
    let constr2 = gec "constr2"
    let constr3 = gec "constr3"
    let lassoc_constr4 = gec "lassoc_constr4"
    let constr5 = gec "constr5"
    let constr6 = gec "constr6"
    let constr7 = gec "constr7"
    let constr8 = gec "constr8"
    let constr9 = gec "constr9"
    let constr91 = gec "constr91"
    let constr10 = gec "constr10"
    let constr_eoi = eoi_entry constr
    let lconstr = gec "lconstr"
    let ident = gec "ident"
    let qualid = gec_list "qualid"
    let global = gec "global"
    let ne_ident_comma_list = gec_list "ne_ident_comma_list"
    let ne_constr_list = gec_list "ne_constr_list"
    let sort = gec "sort"
    let pattern = gec "pattern"
    let ne_binders_list = gec_list "ne_binders_list"

    let uconstr = snd (get_univ "constr")
  end


module Tactic =
  struct
    let utactic = snd (get_univ "tactic")
    let gec s =
      let e = Gram.Entry.create ("Tactic." ^ s) in
      Hashtbl.add utactic s (Ast e); e
    
    let gec_list s =
      let e = Gram.Entry.create ("Tactic." ^ s) in
      Hashtbl.add utactic s (ListAst e); e

    let autoargs = gec_list "autoargs"    
    let binding_list = gec "binding_list"
    let castedopenconstrarg = gec "castedopenconstrarg"
    let castedconstrarg = gec "castedconstrarg"
    let com_binding_list = gec_list "com_binding_list"
    let constrarg = gec "constrarg"
    let constrarg_binding_list = gec_list "constrarg_binding_list"
    let numarg_binding_list = gec_list "numarg_binding_list"
    let lconstrarg_binding_list = gec_list "lconstrarg_binding_list"
    let constrarg_list = gec_list "constrarg_list"
    let ident_or_numarg = gec "ident_or_numarg"
    let ident_or_constrarg = gec "ident_or_constrarg"
    let identarg = gec "identarg"
    let hypident = gec "hypident"
    let idmeta_arg = gec "idmeta_arg"
    let idmetahyp = gec "idmetahyp"
    let qualidarg = gec "qualidarg"
    let input_fun = gec "input_fun"
    let lconstrarg = gec "lconstrarg"
    let let_clause = gec "let_clause"
    let letcut_clause = gec "letcut_clause"
    let clausearg = gec "clausearg"
    let match_context_rule = gec "match_context_rule"
    let match_hyps = gec "match_hyps"
    let match_pattern = gec "match_pattern"
    let match_context_list = gec_list "match_context_list"
    let match_rule = gec "match_rule"
    let match_list = gec_list "match_list"
    let ne_identarg_list = gec_list "ne_identarg_list"
    let ne_hyp_list = gec_list "ne_hyp_list"
    let ne_idmetahyp_list = gec_list "ne_idmetahyp_list"
    let ne_qualidarg_list = gec_list "ne_qualidarg_list"
    let ne_pattern_list = gec_list "ne_pattern_list"
    let clause_pattern = gec "clause_pattern"
    let one_intropattern = gec "one_intropattern"
    let intropattern = gec "intropattern"
    let ne_intropattern = gec "ne_intropattern"
    let simple_intropattern = gec "simple_intropattern"
    let ne_unfold_occ_list = gec_list "ne_unfold_occ_list"
    let rec_clause = gec "rec_clause"
    let red_tactic = gec "red_tactic"
    let red_flag = gec "red_flag"
    let numarg = gec "numarg"
    let pattern_occ = gec "pattern_occ"
    let pattern_occ_hyp = gec "pattern_occ_hyp"
    let pure_numarg = gec "pure_numarg"
    let simple_binding = gec "simple_binding"
    let simple_binding_list = gec_list "simple_binding_list"
    let simple_tactic = gec "simple_tactic"
    let tactic = gec "tactic"
    let tactic_arg = gec "tactic_arg"
    let tactic_atom0 = gec "tactic_atom0"
    let tactic_atom = gec "tactic_atom"
    let tactic_expr = gec "tactic_expr"
    let tactic_expr_par = gec "tactic_expr_par"
    let unfold_occ = gec "unfold_occ"
    let with_binding_list = gec "with_binding_list"
    let fixdecl = gec_list "fixdecl"
    let cofixdecl = gec_list "cofixdecl"
    let tacarg_list = gec_list "tacarg_list"
    let tactic_eoi = eoi_entry tactic
  end


module Vernac_ =
  struct
    let uvernac = snd (get_univ "vernac")
    let gec s =
      let e = Gram.Entry.create ("Vernac." ^ s) in
      Hashtbl.add uvernac s (Ast e); e
    
    let gec_list s =
      let e = Gram.Entry.create ("Vernac." ^ s) in
      Hashtbl.add uvernac s (ListAst e); e
    
    let identarg = gec "identarg"
    let ne_identarg_list = gec_list "ne_identarg_list"
    let qualidarg = gec "qualidarg"
    let commentarg = gec "commentarg"
    let commentarg_list = gec_list "commentarg_list"
    let ne_qualidarg_list = gec_list "ne_qualidarg_list"
    let numarg = gec "numarg"
    let numarg_list = gec_list "numarg_list"
    let ne_numarg_list = gec_list "ne_numarg_list"
    let stringarg = gec "stringarg"
    let ne_stringarg_list = gec_list "ne_stringarg_list"
    let constrarg = gec "constrarg"
    let ne_constrarg_list = gec_list "ne_constrarg_list"
    let tacarg = gec "tacarg"
    let sortarg = gec "sortarg"
    let theorem_body = gec "theorem_body"
    let thm_tok = gec "thm_tok"

    let gallina = gec "gallina"
    let gallina_ext = gec "gallina_ext"
    let command = gec "command"
    let syntax = gec "syntax_command"
    let vernac = gec "vernac"
    let vernac_eoi = eoi_entry vernac
  end


module Prim =
  struct
    let uprim = snd (get_univ "prim")
    let gec s =
      let e = Gram.Entry.create ("Prim." ^ s) in
      	Hashtbl.add uprim s (Ast e); e
    let ast = gec "ast"
    let ast_eoi = eoi_entry ast
    let astact = gec "astact"
    let astpat = gec "astpat"
    let entry_type = gec "entry_type"
    let grammar_entry = gec "grammar_entry"
    let grammar_entry_eoi = eoi_entry grammar_entry
    let ident = gec "ident"
    let metaident = gec "metaident"
    let number = gec "number"
    let path = gec "path"
    let string = gec "string"
    let syntax_entry = gec "syntax_entry"
    let syntax_entry_eoi = eoi_entry syntax_entry
    let uprim = snd (get_univ "prim")
    let var = gec "var"
  end


let main_entry = Gram.Entry.create "vernac"

GEXTEND Gram
  main_entry:
    [ [ a = Vernac_.vernac -> Some a | EOI -> None ] ]
  ;
END

(* Quotations *)

open Prim
open Constr
open Tactic
open Vernac_

(* current file and toplevel/vernac.ml *)

let define_quotation default s e =
  (if default then
    GEXTEND Gram
      ast: [ [ "<<"; c = e; ">>" -> c ] ];
     (* Uncomment this to keep compatibility with old grammar syntax
     constr: [ [ "<<"; c = e; ">>" -> c ] ];
     vernac: [ [ "<<"; c = e; ">>" -> c ] ];
     tactic: [ [ "<<"; c = e; ">>" -> c ] ];
     *)
   END);
  (GEXTEND Gram
     GLOBAL: ast constr vernac tactic;
     ast:
       [ [ "<:"; IDENT $s$; ":<"; c = e; ">>" -> c ] ];
     (* Uncomment this to keep compatibility with old grammar syntax
     constr:
       [ [ "<:"; IDENT $s$; ":<"; c = e; ">>" -> c ] ];
     vernac:
       [ [ "<:"; IDENT $s$; ":<"; c = e; ">>" -> c ] ];
     tactic:
       [ [ "<:"; IDENT $s$; ":<"; c = e; ">>" -> c ] ];
     *)
   END)

let _ = define_quotation false "ast" ast in ()

let constr_parser = ref Constr.constr
let tactic_parser = ref Tactic.tactic
let vernac_parser = ref Vernac_.vernac

let update_constr_parser p = constr_parser := p
let update_tactic_parser p = tactic_parser := p
let update_vernac_parser p = vernac_parser := p

(**********************************************************************)
(* The following is to dynamically set the parser in Grammar actions  *)
(* and Syntax pattern, according to the universe of the rule defined  *)

let default_action_parser_ref = ref ast

let get_default_action_parser () = !default_action_parser_ref

let set_default_action_parser f = (default_action_parser_ref := f)

let set_default_action_parser_by_name = function
  | "constr" -> set_default_action_parser !constr_parser
  | "tactic" -> set_default_action_parser !tactic_parser
  | "vernac" -> set_default_action_parser !vernac_parser
  | _ -> set_default_action_parser ast

let default_action_parser =
  Gram.Entry.of_parser "default_action_parser" 
    (fun strm -> Gram.Entry.parse_token (get_default_action_parser ()) strm)

