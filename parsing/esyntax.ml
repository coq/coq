
(* $Id$ *)

open Pp
open Util
open Coqast
open Ast
open Extend

(*** Syntax keys ***)

(* We define keys for ast and astpats. This is a kind of hash
 * function.  An ast may have several keys, but astpat only one. The
 * idea is that if an ast A matches a pattern P, then the key of P
 * is in the set of keys of A. Thus, we can split the syntax entries
 * according to the key of the pattern. *)

type key =
  | Cst of string list (* keys for global constants rules *)
  | Ind of string list * int 
  | Cstr of (string list * int) * int
  | Nod of string      (* keys for other constructed asts rules *)
  | Oth                (* key for other syntax rules *)
  | All     (* key for catch-all rules (i.e. with a pattern such as $x .. *)

let ast_keys = function
  | Node(_,"APPLIST", Node(_,"CONST", [Path (_,sl,_)]) ::_) ->
      [Cst sl; Nod "APPLIST"; All]
  | Node(_,"APPLIST", Node(_,"MUTIND", [Path (_,sl,_); Num (_,tyi)]) ::_) ->
      [Ind (sl,tyi); Nod "APPLIST"; All]
  | Node(_,"APPLIST", Node(_,"MUTCONSTRUCT",
			   [Path (_,sl,_); Num (_,tyi); Num (_,i)]) ::_) ->
      [Cstr ((sl,tyi),i); Nod "APPLIST"; All]
  | Node(_,s,_) -> [Nod s; All]
  | _ -> [Oth; All]

let spat_key astp =
  match astp with
    | Pnode("APPLIST",
            Pcons(Pnode("CONST",
                        Pcons(Pquote(Path (_,sl,s)),_)), _))
      -> Cst sl
    | Pnode("APPLIST",
            Pcons(Pnode("MUTIND",
                        Pcons(Pquote(Path (_,sl,s)),
			      Pcons(Pquote(Num (_,tyi)),_))), _))
      -> Ind (sl,tyi)
    | Pnode("APPLIST",
            Pcons(Pnode("MUTCONSTRUCT",
                        Pcons(Pquote(Path (_,sl,s)),
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
type frozen_t = (string * string, syntax_entry) Gmap.t * 
                (string * key, syntax_entry) Gmapl.t

let freeze () = (!from_name_table, !from_key_table)

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
  first_match (fun se -> se.syn_astpat) [] gt entries

let remove_with_warning name =
  if Gmap.mem name !from_name_table then begin
    let se = Gmap.find name !from_name_table in
    let key = (fst name, se_key se) in
    warning ("overriding syntax rule "^(fst name)^":"^(snd name)^".");
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

(* Module of primitive printers *)
module Ppprim =
  struct
    type t = std_printer -> std_printer
    let tab = ref ([] : (string * t) list)
    let map a = List.assoc a !tab
    let add (a,ppr) = tab := (a,ppr)::!tab
  end

(* A printer for the tokens. *)
let token_printer stdpr ast =
  match ast with
    | Id _ | Num _ | Str _ | Path _ -> print_ast ast
    | _ -> stdpr ast

(* Register the primitive printer for "token". It is not used in syntax/PP*.v,
 * but any ast matching no PP rule is printed with it. *)

let _ = Ppprim.add ("token",token_printer)

(* A primitive printer to do "print as" (to specify a length for a string) *)
let print_as_printer stdpr = function
  | Node (_, "AS", [Num(_,n); Str(_,s)]) -> [< 'sTRas (n,s) >]
  | ast                                  -> stdpr ast

let _ = Ppprim.add ("print_as",print_as_printer)


(* Print the syntax entry. In the unparsing hunks, the tokens are
 * printed using the token_printer, unless another primitive printer
 * is specified. *)

let print_syntax_entry whatfor sub_pr env se = 
  let rule_prec = (se.syn_id, se.syn_prec) in
  let rec print_hunk = function
    | PH(e,externpr,reln) ->
        let printer =
          match externpr with (* May branch to an other printer *)
            | Some (c,entry_prec) ->
                (try (* Test for a primitive printer *)
		   (Ppprim.map c) (sub_pr whatfor (Some(rule_prec,reln)))
                 with Not_found -> token_printer (sub_pr c entry_prec))
            | None -> token_printer (sub_pr whatfor (Some(rule_prec,reln)))
        in 
	printer (Ast.pat_sub Ast.dummy_loc env e)
    | RO s -> [< 'sTR s >]
    | UNP_TAB -> [< 'tAB >]
    | UNP_FNL -> [< 'fNL >]
    | UNP_BRK(n1,n2) -> [< 'bRK(n1,n2) >]
    | UNP_TBRK(n1,n2) -> [< 'tBRK(n1,n2) >]
    | UNP_BOX (b,sub) -> ppcmd_of_box b (prlist print_hunk sub)
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
	    [< 'sTR"(" ; printed_gt; 'sTR")" >]
      | None -> dflt gt (* No rule found *)
  in
  try 
    rec_pr whatfor inhprec ast
  with
    | Failure _ -> [< 'sTR"<PP failure: "; dflt ast; 'sTR">" >]
    | Not_found -> [< 'sTR"<PP search failure: "; dflt ast; 'sTR">" >]
