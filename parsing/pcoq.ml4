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
open Ast
open Genarg
open Tacexpr
open Vernacexpr

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

module type Gramobj =
sig
  type grammar_object
  type 'a entry

  val in_entry : 'a -> 'b G.Entry.e -> 'a entry
  val object_of_entry : 'a entry -> grammar_object G.Entry.e
  val type_of_entry : 'a entry -> 'a
end

module Gramobj : Gramobj =
struct
  type grammar_object = Obj.t
  type 'a entry = 'a * grammar_object G.Entry.e

  let in_entry t e = (t,Obj.magic e)
  let object_of_entry (t,e) = e
  let type_of_entry (t,e) = t
end

type grammar_object = Gramobj.grammar_object
let in_typed_entry = Gramobj.in_entry
let type_of_typed_entry = Gramobj.type_of_entry
let object_of_typed_entry = Gramobj.object_of_entry
type typed_entry = entry_type Gramobj.entry

module type Gramtypes =
sig
  val inAstListType : Coqast.t list G.Entry.e -> typed_entry
  val inTacticAtomAstType : raw_atomic_tactic_expr G.Entry.e -> typed_entry
  val inThmTokenAstType : theorem_kind G.Entry.e -> typed_entry
  val inDynamicAstType : typed_ast G.Entry.e -> typed_entry
  val inReferenceAstType : reference_expr G.Entry.e -> typed_entry
  val inPureAstType : constr_ast G.Entry.e -> typed_entry
  val inGenAstType : 'a raw_abstract_argument_type ->
      'a G.Entry.e -> typed_entry
  val outGenAstType : 'a raw_abstract_argument_type -> typed_entry -> 'a G.Entry.e
end

module Gramtypes : Gramtypes =
struct
  let inAstListType = in_typed_entry AstListType
  let inTacticAtomAstType = in_typed_entry TacticAtomAstType
  let inThmTokenAstType = in_typed_entry ThmTokenAstType
  let inDynamicAstType = in_typed_entry DynamicAstType
  let inReferenceAstType = in_typed_entry ReferenceAstType
  let inPureAstType = in_typed_entry (GenAstType ConstrArgType)
  let inGenAstType rawwit = in_typed_entry (GenAstType (unquote rawwit))

  let outGenAstType (a:'a raw_abstract_argument_type) o =
    if type_of_typed_entry o <> GenAstType (unquote a) 
      then anomaly "outGenAstType: wrong type";
    Obj.magic (object_of_typed_entry o)
end

open Gramtypes

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
      errorlabstrm "Pcoq.delete_rule" (str "GDELETE_RULE forbidden.")
  end


(* This extension command is used by the Grammar constr *)

let grammar_extend te pos rls =
  camlp4_state := ByGrammar (te,pos,rls) :: !camlp4_state;
  let a = !Gramext.warning_verbose in
  Gramext.warning_verbose := Options.is_verbose ();
  G.extend (object_of_typed_entry te) pos rls;
  Gramext.warning_verbose := a

(* n is the number of extended entries (not the number of Grammar commands!)
   to remove. *)
let remove_grammar rls te = grammar_delete (object_of_typed_entry te) rls

let rec remove_grammars n =
  if n>0 then
    (match !camlp4_state with
       | [] -> anomaly "Pcoq.remove_grammars: too many rules to remove"
       | ByGrammar(g,_,rls)::t ->
           remove_grammar rls g;
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

(*
let slam_ast (_,fin) id ast =
  match id with
    | Coqast.Nvar (loc, s) -> Coqast.Slam (loc, Some s, ast)
    | Coqast.Nmeta (loc, s) -> Coqast.Smetalam (loc, s, ast)
    | _ -> invalid_arg "Ast.slam_ast"
*)

(*
let entry_type ast =
  match ast with
    | Coqast.Id (_, "LIST") -> ETastl
    | Coqast.Id (_, "AST") -> ETast
    | _ -> invalid_arg "Ast.entry_type"
*)

(*
let entry_type ast =
  match ast with
    | AstListType -> ETastl
    | _ -> ETast
*)

type gram_universe = (string, typed_entry) Hashtbl.t

let trace = ref false

(* The univ_tab is not part of the state. It contains all the grammar that
   exist or have existed before in the session. *)

let univ_tab = Hashtbl.create 7

let create_univ s =
  let u = s, Hashtbl.create 29 in Hashtbl.add univ_tab s u; u

let uprim   = create_univ "prim"
let uconstr = create_univ "constr"
let utactic = create_univ "tactic"
let uvernac = create_univ "vernac"

let create_univ_if_new s =
  (* compatibilite *)
  let s = if s = "command" then (warning "'command' grammar universe is obsolete; use name 'constr' instead"; "constr") else s in
  try
    Hashtbl.find univ_tab s
  with Not_found -> 
    if !trace then begin 
      Printf.eprintf "[Creating univ %s]\n" s; flush stderr; () 
    end;
    let u = s, Hashtbl.create 29 in Hashtbl.add univ_tab s u; u

let get_univ = create_univ_if_new

let get_entry (u, utab) s =
  try
    Hashtbl.find utab s 
  with Not_found -> 
    errorlabstrm "Pcoq.get_entry"
      (str "unknown grammar entry " ++ str u ++ str ":" ++ str s)

let new_entry etyp (u, utab) s =
  let ename = u ^ ":" ^ s in
  let e = in_typed_entry etyp (Gram.Entry.create ename) in
  Hashtbl.add utab s e; e

let entry_type (u, utab) s =
  try
    let e = Hashtbl.find utab s in
    Some (type_of_typed_entry e)
  with Not_found -> None

let get_entry_type (u,n) =  type_of_typed_entry (get_entry (get_univ u) n)

let create_entry_if_new (u, utab) s etyp =
  try
    if type_of_typed_entry (Hashtbl.find utab s) <> etyp then
      failwith ("Entry " ^ u ^ ":" ^ s ^ " already exists with another type")
  with Not_found ->
    if !trace then begin
      Printf.eprintf "[Creating entry %s:%s]\n" u s; flush stderr; ()
    end;
    let _ = new_entry etyp (u, utab) s in ()

let create_entry (u, utab) s etyp =
  try
    let e = Hashtbl.find utab s in
    if type_of_typed_entry e <> etyp then
      failwith ("Entry " ^ u ^ ":" ^ s ^ " already exists with another type");
    e
  with Not_found ->
    if !trace then begin
      Printf.eprintf "[Creating entry %s:%s]\n" u s; flush stderr; ()
    end;
    new_entry etyp (u, utab) s

let create_constr_entry u s =
  outGenAstType rawwit_constr (create_entry u s (GenAstType ConstrArgType))

let create_generic_entry s wit = 
  let (u,utab) = utactic in
  let etyp = unquote wit in
  try
    let e = Hashtbl.find utab s in
    if type_of_typed_entry e <> GenAstType etyp then
      failwith ("Entry " ^ u ^ ":" ^ s ^ " already exists with another type");
    outGenAstType wit e
  with Not_found ->
    if !trace then begin
      Printf.eprintf "[Creating entry %s:%s]\n" u s; flush stderr; ()
    end;
  let e = Gram.Entry.create s in
  Hashtbl.add utab s (inGenAstType wit e); e

let get_generic_entry s =
  let (u,utab) = utactic in
  try
    object_of_typed_entry (Hashtbl.find utab s)
  with Not_found -> 
    error ("unknown grammar entry "^u^":"^s)

let get_generic_entry_type (u,utab) s =
  try
    match type_of_typed_entry (Hashtbl.find utab s) with
      | GenAstType t -> t
      | _ -> error "Not a generic type"
  with Not_found -> 
    error ("unknown grammar entry "^u^":"^s)

let force_entry_type (u, utab) s etyp =
  try
    let entry = Hashtbl.find utab s in
    let extyp = type_of_typed_entry entry in
    if etyp = PureAstType && extyp = GenAstType ConstrArgType then
      entry else
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

let make_entry (u,univ) in_fun s =
  let e = Gram.Entry.create (u ^ ":" ^ s) in
  Hashtbl.add univ s (in_fun e); e

let make_gen_entry u rawwit = make_entry u (inGenAstType rawwit)

module Prim =
  struct
    let gec_gen x = make_gen_entry uprim x
    let gec = make_entry uprim inPureAstType
    let gec_list = make_entry uprim inAstListType
    
    let preident = gec_gen rawwit_pre_ident "preident"
    let ident = gec_gen rawwit_ident "ident"
    let rawident = Gram.Entry.create "Prim.rawident"
    let natural = gec_gen rawwit_int "natural"
    let integer = gec_gen rawwit_int "integer"
    let string = gec_gen rawwit_string "string"
    let qualid = gec_gen rawwit_qualid "qualid"
    let reference = make_entry uprim inReferenceAstType "reference"
    let dirpath = Gram.Entry.create "Prim.dirpath"
    let astpat = make_entry uprim inDynamicAstType "astpat"
    let ast = gec "ast"
    let astlist = gec_list "astlist"
    let ast_eoi = eoi_entry ast
    let astact = gec "astact"
    let metaident = gec "metaident"
    let numarg = gec "numarg"
    let var = gec "var"
  end


module Constr =
  struct
    let gec = make_entry uconstr inPureAstType
    let gec_constr = make_gen_entry uconstr rawwit_constr
    let gec_list = make_entry uconstr inAstListType

    let constr = gec_constr "constr"
    let constr0 = gec_constr "constr0"
    let constr1 = gec_constr "constr1"
    let constr2 = gec_constr "constr2"
    let constr3 = gec_constr "constr3"
    let lassoc_constr4 = gec_constr "lassoc_constr4"
    let constr5 = gec_constr "constr5"
    let constr6 = gec_constr "constr6"
    let constr7 = gec_constr "constr7"
    let constr8 = gec_constr "constr8"
    let constr9 = gec_constr "constr9"
    let constr91 = gec_constr "constr91"
    let constr10 = gec_constr "constr10"
    let constr_eoi = eoi_entry constr
    let lconstr = gec_constr "lconstr"
    let ident = gec "ident"
    let qualid = gec "qualid"
    let global = gec "global"
    let ne_ident_comma_list = gec_list "ne_ident_comma_list"
    let ne_constr_list = gec_list "ne_constr_list"
    let sort = gec_constr "sort"
    let pattern = gec "pattern"
    let constr_pattern = gec "constr_pattern"
    let ne_binders_list = gec_list "ne_binders_list"
  end


module Tactic =
  struct
    let gec = make_entry utactic inPureAstType
    let gec_list = make_entry utactic inAstListType
    let castedopenconstr = 
      make_gen_entry utactic rawwit_casted_open_constr "castedopenconstr"
    let constr_with_bindings =
      make_gen_entry utactic rawwit_constr_with_bindings "constr_with_bindings"
    let constrarg = make_gen_entry utactic rawwit_constr_may_eval "constrarg"
    let quantified_hypothesis =
      make_gen_entry utactic rawwit_quant_hyp "quantified_hypothesis"
    let int_or_var = make_gen_entry utactic rawwit_int_or_var "int_or_var"
    let red_tactic = make_gen_entry utactic rawwit_red_expr "red_tactic"
    let simple_tactic = make_entry utactic inTacticAtomAstType "simple_tactic"
    let tactic_arg = Gram.Entry.create "tactic:tactic_arg"
    let tactic = make_gen_entry utactic rawwit_tactic "tactic"
    let tactic_eoi = eoi_entry tactic
  end


module Vernac_ =
  struct
    let thm_token = make_entry uvernac inThmTokenAstType "thm_token"
    let class_rawexpr = Gram.Entry.create "vernac:class_rawexpr"
    let gec_vernac s = Gram.Entry.create ("vernac:" ^ s)
    let gallina = gec_vernac "gallina"
    let gallina_ext = gec_vernac "gallina_ext"
    let command = gec_vernac "command"
    let syntax = gec_vernac "syntax_command"
    let vernac = gec_vernac "Vernac_.vernac"
    let vernac_eoi = eoi_entry vernac
  end


let main_entry = Gram.Entry.create "vernac"

GEXTEND Gram
  main_entry:
    [ [ a = Vernac_.vernac -> Some (loc,a) | EOI -> None ] ]
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
     GLOBAL: ast constr command tactic;
     ast:
       [ [ "<:"; IDENT $s$; ":<"; c = e; ">>" -> c ] ];
     (* Uncomment this to keep compatibility with old grammar syntax
     constr:
       [ [ "<:"; IDENT $s$; ":<"; c = e; ">>" -> c ] ];
     command:
       [ [ "<:"; IDENT $s$; ":<"; c = e; ">>" -> c ] ];
     tactic:
       [ [ "<:"; IDENT $s$; ":<"; c = e; ">>" -> c ] ];
     *)
   END)

let _ = define_quotation false "ast" ast in ()

let gecdyn s =
  let e = Gram.Entry.create ("Dyn." ^ s) in
  Hashtbl.add (snd uconstr) s (inDynamicAstType e); e

let dynconstr = gecdyn "dynconstr"
let dyntactic = gecdyn "dyntactic"
let dynvernac = gecdyn "dynvernac"
let dynastlist = gecdyn "dynastlist"
let dynast = gecdyn "dynast"

let globalizer = ref (fun x -> x)
let set_globalizer f = globalizer := f

GEXTEND Gram
  dynconstr: [ [ a = Constr.constr -> !globalizer (PureAstNode a) ] ];
(*
  dyntactic: [ [ a = Tactic.tactic -> !globalizer (TacticAstNode a) ] ];
  dynvernac: [ [ a = Vernac_.vernac -> !globalizer(VernacAstNode a) ] ];
*)
  dynastlist: [ [ a = Prim.astlist -> AstListNode a ] ];
  dynast:    [ [ a = ast -> PureAstNode a ] ];
END

(**********************************************************************)
(* The following is to dynamically set the parser in Grammar actions  *)
(* and Syntax pattern, according to the universe of the rule defined  *)

type parser_type =
  | AstListParser
  | AstParser
  | ConstrParser
  | TacticParser
  | VernacParser

let default_action_parser_ref = ref dynast

let get_default_action_parser () = !default_action_parser_ref

let entry_type_from_name =  function
  | "constr" -> GenAstType ConstrArgType
  | "tactic" -> failwith "Not supported"
  | "vernac" -> failwith "Not supported"
  | s -> GenAstType ConstrArgType

let entry_type_of_parser =  function
  | AstListParser -> Some AstListType
  | _ -> None

let parser_type_from_name =  function
  | "constr" -> ConstrParser
  | "tactic" -> TacticParser
  | "vernac" -> VernacParser
  | s -> AstParser

let set_default_action_parser = function
  | AstListParser -> default_action_parser_ref := dynastlist
  | AstParser -> default_action_parser_ref := dynast
  | ConstrParser  -> default_action_parser_ref := dynconstr
  | TacticParser -> default_action_parser_ref := dyntactic
  | VernacParser -> default_action_parser_ref := dynvernac

let default_action_parser =
  Gram.Entry.of_parser "default_action_parser" 
    (fun strm -> Gram.Entry.parse_token (get_default_action_parser ()) strm)
