(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Coqast
open Ast
open Extend
open Vernacexpr
open Names
open Nametab

(*** Syntax keys ***)

(* We define keys for ast and astpats. This is a kind of hash
 * function.  An ast may have several keys, but astpat only one. The
 * idea is that if an ast A matches a pattern P, then the key of P
 * is in the set of keys of A. Thus, we can split the syntax entries
 * according to the key of the pattern. *)

type key =
  | Cst of Names.constant (* keys for global constants rules *)
  | SecVar of Names.variable
  | Ind of Names.inductive
  | Cstr of Names.constructor
  | Nod of string      (* keys for other constructed asts rules *)
  | Oth                (* key for other syntax rules *)
  | All     (* key for catch-all rules (i.e. with a pattern such as $x .. *)

let warning_verbose = ref true

let ast_keys = function
  | Node(_,"APPLIST", Node(_,"CONST", [Path (_,sl)]) ::_) ->
      [Cst sl; Nod "APPLIST"; All]
  | Node(_,"APPLIST", Node(_,"SECVAR", [Nvar (_,s)]) ::_) ->
      [SecVar s; Nod "APPLIST"; All]
  | Node(_,"APPLIST", Node(_,"MUTIND", [Path (_,sl); Num (_,tyi)]) ::_) ->
      [Ind (sl,tyi); Nod "APPLIST"; All]
  | Node(_,"APPLIST", Node(_,"MUTCONSTRUCT",
			   [Path (_,sl); Num (_,tyi); Num (_,i)]) ::_) ->
      [Cstr ((sl,tyi),i); Nod "APPLIST"; All]
  | Node(_,s,_) -> [Nod s; All]
  | _ -> [Oth; All]

let spat_key astp =
  match astp with
    | Pnode("APPLIST",
            Pcons(Pnode("CONST",
                        Pcons(Pquote(Path (_,sl)),_)), _))
      -> Cst sl
    | Pnode("APPLIST",
            Pcons(Pnode("SECVAR",
                        Pcons(Pquote(Nvar (_,s)),_)), _))
      -> SecVar s
    | Pnode("APPLIST",
            Pcons(Pnode("MUTIND",
                        Pcons(Pquote(Path (_,sl)),
			      Pcons(Pquote(Num (_,tyi)),_))), _))
      -> Ind (sl,tyi)
    | Pnode("APPLIST",
            Pcons(Pnode("MUTCONSTRUCT",
                        Pcons(Pquote(Path (_,sl)),
			      Pcons(Pquote(Num (_,tyi)),
				    Pcons(Pquote(Num (_,i)),_)))), _))
      -> Cstr ((sl,tyi),i)
    | Pnode(na,_) -> Nod na
    | Pquote ast -> List.hd (ast_keys ast)
    | Pmeta _ -> All
    | _ -> Oth

let se_key se = spat_key se.syn_astpat

(** Syntax entry tables (state of the pretty_printer) **)
let from_name_table = ref Gmap.empty
let from_key_table = ref Gmapl.empty

let infix_symbols_map = ref Stringmap.empty
let infix_names_map = ref Spmap.empty

(* Summary operations *)
type frozen_t = (string * string, astpat syntax_entry) Gmap.t * 
                (string * key, astpat syntax_entry) Gmapl.t *
                 section_path Stringmap.t * string list Spmap.t

let freeze () =
  (!from_name_table, !from_key_table, !infix_symbols_map, !infix_names_map)

let unfreeze (fnm,fkm,infs,infn) =
  from_name_table := fnm;
  from_key_table := fkm;
  infix_symbols_map := infs;
  infix_names_map := infn

let init () =
  from_name_table := Gmap.empty;
  from_key_table := Gmapl.empty
(*
  infix_symbols_map := Stringmap.empty;
  infix_names_map := Spmap.empty
*)

let find_syntax_entry whatfor gt =
  let gt_keys = ast_keys gt in
  let entries =
    List.flatten
      (List.map (fun k -> Gmapl.find (whatfor,k) !from_key_table) gt_keys)
  in 
  first_match (fun se -> se.syn_astpat) [] gt entries

let remove_with_warning name =
  if Gmap.mem name !from_name_table then begin
    let se = Gmap.find name !from_name_table in
    let key = (fst name, se_key se) in
    if !warning_verbose then
      (Options.if_verbose
    	warning ("overriding syntax rule "^(fst name)^":"^(snd name)^"."));
    from_name_table := Gmap.remove name !from_name_table;
    from_key_table := Gmapl.remove key se !from_key_table
  end

let add_rule whatfor se =
  let name = (whatfor,se.syn_id) in
  let key = (whatfor, se_key se) in
  remove_with_warning name;
  from_name_table := Gmap.add name se !from_name_table;
  from_key_table := Gmapl.add key se !from_key_table

let add_ppobject {sc_univ=wf;sc_entries=sel} = List.iter (add_rule wf) sel


(* Pretty-printing machinery *)

type std_printer = Coqast.t -> std_ppcmds
type unparsing_subfunction = string -> tolerability option -> std_printer

type std_constr_printer = Genarg.constr_ast -> std_ppcmds

(* Module of primitive printers *)
module Ppprim =
  struct
    type t = std_printer -> std_printer
    let tab = ref ([] : (string * t) list)
    let map a = List.assoc a !tab
    let add (a,ppr) = tab := (a,ppr)::!tab
  end

(* A printer for the tokens. *)
let token_printer stdpr = function
  | (Id _ | Num _ | Str _ | Path _ as ast) -> print_ast ast
  | a -> stdpr a

(* Register the primitive printer for "token". It is not used in syntax/PP*.v,
 * but any ast matching no PP rule is printed with it. *)

let _ = Ppprim.add ("token",token_printer)

(* A primitive printer to do "print as" (to specify a length for a string) *)
let print_as_printer stdpr = function
  | Node (_, "AS", [Num(_,n); Str(_,s)]) -> stras (n,s)
  | ast                                  -> stdpr ast

let _ = Ppprim.add ("print_as",print_as_printer)

(* Handle infix symbols *)

let find_infix_symbols sp =
  try Spmap.find sp !infix_names_map with Not_found -> []

let find_infix_name a =
  try Stringmap.find a !infix_symbols_map
  with Not_found -> anomaly ("Undeclared symbol: "^a)

let declare_infix_symbol sp s =
  let l = find_infix_symbols sp in
  infix_names_map := Spmap.add sp (s::l) !infix_names_map;
  infix_symbols_map := Stringmap.add s sp !infix_symbols_map

let meta_pattern m = Pmeta(m,Tany)

let make_hunks (lp,rp) s e1 e2 =
  let n,s =
    if is_letter (s.[String.length s -1]) or is_letter (s.[0])
    then 1,s^" " else 0,s
  in
  [PH (meta_pattern e1, None, lp);
   UNP_BRK (n, 1); RO s;
   PH (meta_pattern e2, None, rp)]

let build_syntax (ref,e1,e2,assoc) =
  let sp = match ref with
  | TrueGlobal r -> Nametab.sp_of_global (Global.env()) r
  | SyntacticDef sp -> sp in
  let rec find_symbol = function
    | [] ->
	let s = match ref with
	  | TrueGlobal r ->
	      string_of_qualid (shortest_qualid_of_global (Global.env()) r)
	  | SyntacticDef sp -> string_of_path sp in
	UNP_BOX (PpHOVB 0,
	  [RO "("; RO s; UNP_BRK (1, 1); PH (meta_pattern e1, None, E);
	   UNP_BRK (1, 1); PH (meta_pattern e2, None, E); RO ")"])
    | a::l ->
	if find_infix_name a = sp then
	  UNP_BOX (PpHOVB 1, make_hunks assoc a e1 e2)
	else
	  find_symbol l
  in find_symbol (find_infix_symbols sp)


(* Print the syntax entry. In the unparsing hunks, the tokens are
 * printed using the token_printer, unless another primitive printer
 * is specified. *)

let print_syntax_entry whatfor sub_pr env se = 
  let rule_prec = (se.syn_id, se.syn_prec) in
  let rec print_hunk = function
    | PH(e,externpr,reln) ->
	let node = Ast.pat_sub Ast.dummy_loc env e in
	let printer =
	  match externpr with (* May branch to an other printer *)
	    | Some c ->
                (try (* Test for a primitive printer *) Ppprim.map c
                with Not_found -> token_printer )
	    | _ -> token_printer in
	printer (sub_pr whatfor (Some(rule_prec,reln))) node
    | RO s -> str s
    | UNP_TAB -> tab ()
    | UNP_FNL -> fnl ()
    | UNP_BRK(n1,n2) -> brk(n1,n2)
    | UNP_TBRK(n1,n2) -> tbrk(n1,n2)
    | UNP_BOX (b,sub) -> ppcmd_of_box b (prlist print_hunk sub)
    | UNP_INFIX (sp,e1,e2,assoc) -> print_hunk (build_syntax (sp,e1,e2,assoc))
  in 
  prlist print_hunk se.syn_hunks

(* [genprint whatfor dflt inhprec ast] prints out the ast of
 * 'universe' whatfor. If the term is not matched by any
 * pretty-printing rule, then it will call dflt on it, which is
 * responsible for printing out the term (usually #GENTERM...).
 * In the case of tactics and commands, dflt also prints 
 * global constants basenames. *)

let genprint dflt whatfor inhprec ast =
  let rec rec_pr whatfor inherited gt =
    match find_syntax_entry whatfor gt with
      | Some(se, env) ->     
	  let rule_prec = (se.syn_id, se.syn_prec) in
	  let no_paren = tolerable_prec inherited rule_prec in
	  let printed_gt = print_syntax_entry whatfor rec_pr env se in
	  if no_paren then 
	    printed_gt
	  else 
	    (str"(" ++ printed_gt ++ str")")
      | None -> dflt gt (* No rule found *)
  in
  try 
    rec_pr whatfor inhprec ast
  with
    | Failure _ -> (str"<PP failure: " ++ dflt ast ++ str">")
    | Not_found -> (str"<PP search failure: " ++ dflt ast ++ str">")
