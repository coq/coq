(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Libnames
open Coqast
open Ast
open Extend
open Ppextend
open Names
open Nametab
open Topconstr
open Symbols
 
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

(* Summary operations *)
type frozen_t = (string * string, astpat syntax_entry) Gmap.t * 
                (string * key, astpat syntax_entry) Gmapl.t

let freeze () =
  (!from_name_table, !from_key_table)

let unfreeze (fnm,fkm) =
  from_name_table := fnm;
  from_key_table := fkm

let init () =
  from_name_table := Gmap.empty;
  from_key_table := Gmapl.empty

let find_syntax_entry whatfor gt =
  let gt_keys = ast_keys gt in
  let entries =
    List.flatten
      (List.map (fun k -> Gmapl.find (whatfor,k) !from_key_table) gt_keys)
  in 
  find_all_matches (fun se -> se.syn_astpat) [] gt entries

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
type primitive_printer = Coqast.t -> std_ppcmds option

(* Module of primitive printers *)
module Ppprim =
  struct
    type t = std_printer -> std_printer
    let tab = ref ([] : (string * t) list)
    let map a = List.assoc a !tab
    let add (a,ppr) = tab := (a,ppr)::!tab
  end

(**********************************************************************)
(* Primitive printers (e.g. for numerals)                             *)

(* This is the map associating to a printer the scope it belongs to   *)
(* and its ML code                                                    *)

let primitive_printer_tab = 
  ref (Stringmap.empty : (scope_name * primitive_printer) Stringmap.t)
let declare_primitive_printer s sc pp =
  primitive_printer_tab := Stringmap.add s (sc,pp) !primitive_printer_tab
let lookup_primitive_printer s =
  Stringmap.find s !primitive_printer_tab

(* Register the primitive printer for "token". It is not used in syntax/PP*.v,
 * but any ast matching no PP rule is printed with it. *)
(*
let _ = declare_primitive_printer "token" token_printer
*)

(* A printer for the tokens. *)
let token_printer stdpr = function
  | (Id _ | Num _ | Str _ | Path _ as ast) -> print_ast ast
  | a -> stdpr a

(* Unused ??
(* A primitive printer to do "print as" (to specify a length for a string) *)
let print_as_printer = function
  | Node (_, "AS", [Num(_,n); Str(_,s)]) -> Some (stras (n,s))
  | ast                                  -> None

let _ = declare_primitive_printer "print_as" default_scope print_as_printer
*)

(* Handle infix symbols *)

let pr_parenthesis inherited se strm =
  if tolerable_prec inherited se.syn_prec then
    strm
  else 
    (str"(" ++ strm ++ str")")
    
let print_delimiters inh se strm = function
  | None -> pr_parenthesis inh se strm
  | Some key ->
      let left = "'"^key^":" and right = "'" in
      let lspace =
	if is_letter (left.[String.length left -1]) then str " " else mt () in
      let rspace =
        let c = right.[0] in
	if is_ident_tail c then str " " else mt () in
      hov 0 (str left ++ lspace ++ strm ++ rspace ++ str right)

(* Print the syntax entry. In the unparsing hunks, the tokens are
 * printed using the token_printer, unless another primitive printer
 * is specified. *)

let print_syntax_entry sub_pr scopes env se = 
  let rec print_hunk rule_prec scopes = function
    | PH(e,externpr,reln) ->
	let node = Ast.pat_sub dummy_loc env e in
	let printer =
	  match externpr with (* May branch to an other printer *)
	    | Some c ->
                (try (* Test for a primitive printer *) Ppprim.map c
                with Not_found -> token_printer)
	    | _ -> token_printer in
	printer (sub_pr scopes (Some(rule_prec,reln))) node
    | RO s -> str s
    | UNP_TAB -> tab ()
    | UNP_FNL -> fnl ()
    | UNP_BRK(n1,n2) -> brk(n1,n2)
    | UNP_TBRK(n1,n2) -> tbrk(n1,n2)
    | UNP_BOX (b,sub) -> ppcmd_of_box b (prlist (print_hunk rule_prec scopes) sub)
    | UNP_SYMBOLIC _ -> anomaly "handled by call_primitive_parser"
  in 
  prlist (print_hunk se.syn_prec scopes) se.syn_hunks

let call_primitive_parser rec_pr otherwise inherited scopes (se,env) =
  try (
  match se.syn_hunks with
    | [PH(e,Some c,reln)] ->
	  (* Test for a primitive printer; may raise Not_found *)
	  let sc,pr = lookup_primitive_printer c in
	  (* Look if scope [sc] associated to this printer is OK *)
	  (match Symbols.availability_of_numeral sc scopes with
	    | None -> otherwise ()
	    | Some key ->
	        (* We can use this printer *)
	        let node = Ast.pat_sub dummy_loc env e in
	        match pr node with
		  | Some strm -> print_delimiters inherited se strm key
		  | None -> otherwise ())
    | [UNP_SYMBOLIC (sc,pat,sub)] ->
	(match Symbols.availability_of_notation (sc,pat) scopes with
	  | None -> otherwise ()
	  | Some (scopt,key) ->
	      print_delimiters inherited se
		(print_syntax_entry rec_pr
		  (option_fold_right Symbols.push_scope scopt scopes) env 
		  {se with syn_hunks = [sub]}) key)
    | _ ->
	pr_parenthesis inherited se (print_syntax_entry rec_pr scopes env se)
  )
  with Not_found -> (* To handle old style printer *)
	pr_parenthesis inherited se (print_syntax_entry rec_pr scopes env se)

(* [genprint whatfor dflt inhprec ast] prints out the ast of
 * 'universe' whatfor. If the term is not matched by any
 * pretty-printing rule, then it will call dflt on it, which is
 * responsible for printing out the term (usually #GENTERM...).
 * In the case of tactics and commands, dflt also prints 
 * global constants basenames. *)

let genprint dflt whatfor inhprec ast =
  let rec rec_pr scopes inherited gt =
    let entries = find_syntax_entry whatfor gt in
    let rec test_rule = function
      | se_env::rules ->
	  call_primitive_parser
	    rec_pr 
	    (fun () -> test_rule rules) 
	    inherited scopes se_env
      | [] -> dflt gt (* No rule found *)
    in test_rule entries
  in
  try 
    rec_pr (Symbols.current_scopes ()) inhprec ast
  with
    | Failure _ -> (str"<PP failure: " ++ dflt ast ++ str">")
    | Not_found -> (str"<PP search failure: " ++ dflt ast ++ str">")
