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
open Names
open Libnames
open Rawterm
open Topconstr
open Ast
open Genarg
open Tacexpr
open Ppextend
open Extend

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

(* grammar_object is the superclass of all grammar entry *)
module type Gramobj =
sig
  type grammar_object
  val weaken_entry : 'a G.Entry.e -> grammar_object G.Entry.e
end

module Gramobj : Gramobj =
struct
  type grammar_object = Obj.t
  let weaken_entry e = Obj.magic e
end

type grammar_object = Gramobj.grammar_object
type typed_entry = entry_type * grammar_object G.Entry.e
let in_typed_entry t e = (t,Gramobj.weaken_entry e)
let type_of_typed_entry (t,e) = t
let object_of_typed_entry (t,e) = e
let weaken_entry x = Gramobj.weaken_entry x

module type Gramtypes =
sig
  open Decl_kinds
  val inGramObj : 'a raw_abstract_argument_type -> 'a G.Entry.e -> typed_entry
  val outGramObj : 'a raw_abstract_argument_type -> typed_entry -> 'a G.Entry.e
end

module Gramtypes : Gramtypes =
struct
  let inGramObj rawwit = in_typed_entry (unquote rawwit)
  let outGramObj (a:'a raw_abstract_argument_type) o =
    if type_of_typed_entry o <> unquote a
      then anomaly "outGramObj: wrong type";
    (* downcast from grammar_object *)
    Obj.magic (object_of_typed_entry o)
end

open Gramtypes

type ext_kind =
  | ByGrammar of
      grammar_object G.Entry.e * Gramext.position option *
      (string option * Gramext.g_assoc option *
       (Token.t Gramext.g_symbol list * Gramext.g_action) list) list
  | ByGEXTEND of (unit -> unit) * (unit -> unit)

let camlp4_state = ref []

(* The apparent parser of Coq; encapsulate G to keep track of the
   extensions. *)
module Gram =
  struct
    type te = Token.t
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


let camlp4_verbosity silent f x =
  let a = !Gramext.warning_verbose in
  Gramext.warning_verbose := silent;
  f x;
  Gramext.warning_verbose := a

(* This extension command is used by the Grammar constr *)

let grammar_extend te pos rls =
  camlp4_state := ByGrammar (Gramobj.weaken_entry te,pos,rls) :: !camlp4_state;
  camlp4_verbosity (Options.is_verbose ()) (G.extend te pos) rls

(* n is the number of extended entries (not the number of Grammar commands!)
   to remove. *)
let rec remove_grammars n =
  if n>0 then
    (match !camlp4_state with
       | [] -> anomaly "Pcoq.remove_grammars: too many rules to remove"
       | ByGrammar(g,_,rls)::t ->
           grammar_delete g rls;
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

type gram_universe = (string, typed_entry) Hashtbl.t

let trace = ref false

(* The univ_tab is not part of the state. It contains all the grammar that
   exist or have existed before in the session. *)

let univ_tab = (Hashtbl.create 7 : (string, string * gram_universe) Hashtbl.t)

let create_univ s =
  let u = s, Hashtbl.create 29 in Hashtbl.add univ_tab s u; u

let uprim   = create_univ "prim"
let uconstr = create_univ "constr"
let umodule = create_univ "module"
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
  outGramObj rawwit_constr (create_entry u s ConstrArgType)

let create_generic_entry s wit = 
  let (u,utab) = utactic in
  let etyp = unquote wit in
  try
    let e = Hashtbl.find utab s in
    if type_of_typed_entry e <> etyp then
      failwith ("Entry " ^ u ^ ":" ^ s ^ " already exists with another type");
    outGramObj wit e
  with Not_found ->
    if !trace then begin
      Printf.eprintf "[Creating entry %s:%s]\n" u s; flush stderr; ()
    end;
  let e = Gram.Entry.create s in
  Hashtbl.add utab s (inGramObj wit e); e

let get_generic_entry s =
  let (u,utab) = utactic in
  try
    object_of_typed_entry (Hashtbl.find utab s)
  with Not_found -> 
    error ("unknown grammar entry "^u^":"^s)

let get_generic_entry_type (u,utab) s =
  try type_of_typed_entry (Hashtbl.find utab s)
  with Not_found -> 
    error ("unknown grammar entry "^u^":"^s)

let force_entry_type (u, utab) s etyp =
  try
    let entry = Hashtbl.find utab s in
    let extyp = type_of_typed_entry entry in
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

(* [make_gen_entry] builds entries extensible by giving its name (a string) *)
(* For entries extensible only via the ML name, Gram.Entry.create is enough *)

let make_gen_entry (u,univ) rawwit s =
  let e = Gram.Entry.create (u ^ ":" ^ s) in
  Hashtbl.add univ s (inGramObj rawwit e); e

(* Grammar entries *)

module Prim =
  struct
    let gec_gen x = make_gen_entry uprim x
    
    (* Entries that can be refered via the string -> Gram.Entry.e table *)
    (* Typically for tactic or vernac extensions *)
    let preident = gec_gen rawwit_pre_ident "preident"
    let ident = gec_gen rawwit_ident "ident"
    let natural = gec_gen rawwit_int "natural"
    let integer = gec_gen rawwit_int "integer"
    let bigint = Gram.Entry.create "Prim.bigint"
    let string = gec_gen rawwit_string "string"
    let reference = make_gen_entry uprim rawwit_ref "reference"

    (* A synonym of ident, for compatibility *)
    let var = gec_gen rawwit_ident "var"

    let name = Gram.Entry.create "Prim.name"
    let identref = Gram.Entry.create "Prim.identref"

    (* A synonym of ident - maybe ident will be located one day *)
    let base_ident = Gram.Entry.create "Prim.base_ident"

    let qualid = Gram.Entry.create "Prim.qualid"
    let dirpath = Gram.Entry.create "Prim.dirpath"

    (* For old ast printer *)
    let astpat = Gram.Entry.create "Prim.astpat"
    let ast = Gram.Entry.create "Prim.ast"
    let astlist = Gram.Entry.create "Prim.astlist"
    let ast_eoi = eoi_entry ast
    let astact = Gram.Entry.create "Prim.astact"
  end


module Constr =
  struct
    let gec_constr = make_gen_entry uconstr rawwit_constr
    let gec_constr_list = make_gen_entry uconstr (wit_list0 rawwit_constr)

    (* Entries that can be refered via the string -> Gram.Entry.e table *)
    let constr = gec_constr "constr"
    let constr9 = gec_constr "constr9"
    let constr_eoi = eoi_entry constr
    let lconstr = gec_constr "lconstr"
    let ident = make_gen_entry uconstr rawwit_ident "ident"
    let global = make_gen_entry uconstr rawwit_ref "global"
    let sort = make_gen_entry uconstr rawwit_sort "sort"
    let pattern = Gram.Entry.create "constr:pattern"
    let constr_pattern = gec_constr "constr_pattern"
  end

module Module =
  struct
    let module_expr = Gram.Entry.create "module_expr"
    let module_type = Gram.Entry.create "module_type"
  end

module Tactic =
  struct
    (* Main entry for extensions *)
    let simple_tactic = Gram.Entry.create "tactic:simple_tactic"

    (* Entries that can be refered via the string -> Gram.Entry.e table *)
    (* Typically for tactic user extensions *)
    let castedopenconstr = 
      make_gen_entry utactic rawwit_casted_open_constr "castedopenconstr"
    let constr_with_bindings =
      make_gen_entry utactic rawwit_constr_with_bindings "constr_with_bindings"
    let constrarg = make_gen_entry utactic rawwit_constr_may_eval "constrarg"
    let quantified_hypothesis =
      make_gen_entry utactic rawwit_quant_hyp "quantified_hypothesis"
    let int_or_var = make_gen_entry utactic rawwit_int_or_var "int_or_var"
    let red_expr = make_gen_entry utactic rawwit_red_expr "red_expr"

    (* Main entries for ltac *)
    let tactic_arg = Gram.Entry.create "tactic:tactic_arg"
    let tactic = make_gen_entry utactic rawwit_tactic "tactic"

    (* Main entry for quotations *)
    let tactic_eoi = eoi_entry tactic
  end


module Vernac_ =
  struct
    let gec_vernac s = Gram.Entry.create ("vernac:" ^ s)

    (* The different kinds of vernacular commands *)
    let gallina = gec_vernac "gallina"
    let gallina_ext = gec_vernac "gallina_ext"
    let command = gec_vernac "command"
    let syntax = gec_vernac "syntax_command"
    let vernac = gec_vernac "Vernac_.vernac"

    (* Various vernacular entries needed to be exported *)
    let thm_token = Gram.Entry.create "vernac:thm_token"
    let class_rawexpr = Gram.Entry.create "vernac:class_rawexpr"

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
let globalizer = ref (fun x -> failwith "No globalizer")
let set_globalizer f = globalizer := f

let f = (ast : Coqast.t G.Entry.e)

let define_ast_quotation default s (e:Coqast.t G.Entry.e) =
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

(*
let _ = define_ast_quotation false "ast" ast in ()
*)

let dynconstr = Gram.Entry.create "Constr.dynconstr"
let dyncasespattern = Gram.Entry.create "Constr.dyncasespattern"

GEXTEND Gram
  dynconstr:
  [ [ a = Constr.constr -> ConstrNode a 
    (* For compatibility *)
    | "<<"; a = Constr.constr; ">>" -> ConstrNode a ] ]
  ;
  dyncasespattern: [ [ a = Constr.pattern -> CasesPatternNode a ] ];
END

(**********************************************************************)
(* The following is to dynamically set the parser in Grammar actions  *)
(* and Syntax pattern, according to the universe of the rule defined  *)

type parser_type =
  | ConstrParser
  | CasesPatternParser

let default_action_parser_ref = ref dynconstr

let get_default_action_parser () = !default_action_parser_ref

let entry_type_of_parser =  function
  | ConstrParser -> Some ConstrArgType
  | CasesPatternParser -> failwith "entry_type_of_parser: cases_pattern, TODO"

let parser_type_from_name =  function
  | "constr" -> ConstrParser
  | "cases_pattern" -> CasesPatternParser
  | "tactic" -> assert false
  | "vernac" -> error "No longer supported"
  | s -> ConstrParser

let set_default_action_parser = function
  | ConstrParser  -> default_action_parser_ref := dynconstr
  | CasesPatternParser  -> default_action_parser_ref := dyncasespattern

let default_action_parser =
  Gram.Entry.of_parser "default_action_parser" 
    (fun strm -> Gram.Entry.parse_token (get_default_action_parser ()) strm)

(* This determines if a reference to constr_n is a reference to the level
   below wrt associativity (to be translated in camlp4 into "constr" without 
   level) or to another level (to be translated into "constr LEVEL n") *)

(* Camlp4 levels do not treat NonA *)
let camlp4_assoc = function
  | Some Gramext.NonA | Some Gramext.RightA -> Gramext.RightA 
  | None | Some Gramext.LeftA -> Gramext.LeftA

let adjust_level assoc = function
  (* If NonA on the right-hand side, set to NEXT *)
  | (n,BorderProd (false,Some Gramext.NonA)) -> Some None
  (* If NonA on the left-hand side, adopt the current assoc ?? *)
  | (n,BorderProd (true,Some Gramext.NonA)) -> None
  (* Associativity is None means force the level *)
  | (n,BorderProd (_,None)) -> Some (Some n)
  (* If the expected assoc is the current one, SELF on both sides *)
  | (n,BorderProd (_,Some a)) when a = camlp4_assoc assoc -> None
  (* Otherwise, force the level, n or n-1, according to expected assoc *)
  | (n,BorderProd (left,Some a)) ->
      if (left & a = Gramext.LeftA) or ((not left) & a = Gramext.RightA)
      then Some (Some n) else Some (Some (n-1))
(*  | (8,InternalProd) -> None (* Or (Some 8) for factorization ? *)*)
  | (n,InternalProd) -> Some (Some n)

let compute_entry allow_create adjust = function
  | ETConstr (10,_) -> weaken_entry Constr.lconstr, None, true
  | ETConstr (9,_) -> weaken_entry Constr.constr9, None, true
  | ETConstr (n,q) -> weaken_entry Constr.constr, adjust (n,q), false
  | ETIdent -> weaken_entry Constr.ident, None, false
  | ETBigint -> weaken_entry Prim.bigint, None, false
  | ETReference -> weaken_entry Constr.global, None, false
  | ETPattern -> weaken_entry Constr.pattern, None, false
  | ETOther (u,n) ->
      let u = get_univ u in
      let e =
        try get_entry u n
        with e when allow_create -> create_entry u n ConstrArgType in
      object_of_typed_entry e, None, true

let get_constr_entry = compute_entry true (fun (n,()) -> Some n)

let get_constr_production_entry ass = compute_entry false (adjust_level ass)

let constr_prod_level = function
  | 8 -> "top"
  | 4 -> "4L"
  | n -> string_of_int n

let symbol_of_production assoc typ =
  match get_constr_production_entry assoc typ with
    | (eobj,None,_) -> Gramext.Snterm (Gram.Entry.obj eobj)
    | (eobj,Some None,_) -> Gramext.Snext
    | (eobj,Some (Some lev),_) -> 
        Gramext.Snterml (Gram.Entry.obj eobj,constr_prod_level lev)
