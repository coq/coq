
(* $Id$ *)

open Pp
open Util
open Names
open Term
open Proof_trees
open Tacmach
open Macros
open Coqast
open Ast


let tactic_tab = 
  (Hashtbl.create 17 : (string, tactic_arg list -> tactic) Hashtbl.t)

let tacinterp_add (s,f) =
  try 
    Hashtbl.add tactic_tab s f
  with Failure _ ->
    errorlabstrm "tacinterp_add"
      [< 'sTR"Cannot add the tactic " ; 'sTR s ; 'sTR" twice" >]
      
let overwriting_tacinterp_add (s,f) =
  if Hashtbl.mem tactic_tab s then begin
    Hashtbl.remove tactic_tab s;
    warning ("Overwriting definition of tactic interpreter command "^s)
  end;
  Hashtbl.add tactic_tab s f

let tacinterp_init () = Hashtbl.clear tactic_tab

let tacinterp_map s = Hashtbl.find tactic_tab s

let err_msg_tactic_not_found macro_loc macro =
  user_err_loc
    (macro_loc,"macro_expand",
     [< 'sTR"Tactic macro ";'sTR macro; 'sPC; 'sTR"not found" >])

let cvt_bind = function
  | Node(_,"BINDING", [Num(_,n); Node(_,"COMMAND",[c])]) -> (NoDep n,c)
  | Node(_,"BINDING", [Nvar(_,s); Node(_,"COMMAND",[c])]) -> 
      let id = id_of_string s in (Dep id,c)
  | Node(_,"BINDING", [Node(_,"COMMAND",[c])]) -> (Com,c)
  | x -> errorlabstrm "cvt_bind"
        [< 'sTR "Not the expected form in binding!"; print_ast x >]
	
let rec cvt_intro_pattern = function
  | Node(_,"IDENTIFIER", [Nvar(_,s)]) -> IdPat   (id_of_string s)
  | Node(_,"DISJPATTERN", l) -> DisjPat (List.map cvt_intro_pattern l)
  | Node(_,"CONJPATTERN", l) -> ConjPat (List.map cvt_intro_pattern l)
  | Node(_,"LISTPATTERN", l) -> ListPat (List.map cvt_intro_pattern l)
  | x -> errorlabstrm "cvt_intro_pattern"
        [< 'sTR "Not the expected form for an introduction pattern!"; 
            print_ast x >]

let cvt_letpattern (o,l) = function
  | Node(_,"HYPPATTERN", Nvar(_,s)::nums) ->
      (o, (id_of_string s, List.map num_of_ast nums)::l)
  | Node(_,"CCLPATTERN", nums) ->
      if o<>None then error "\"Goal\" occurs twice"
      else (Some (List.map num_of_ast nums), l)
  | arg -> 
      invalid_arg_loc (Ast.loc arg,"cvt_hyppattern")

let cvt_letpatterns astl = List.fold_left cvt_letpattern (None,[]) astl

let cvt_arg = function
  | Nvar(_,s) -> 
      Identifier (id_of_string s)
  | Str(_,s) -> 
      Quoted_string s
  | Num(_,n) -> 
      Integer n
  | Node(_,"COMMAND",[c]) -> 
      Command c
  | Node(_,"BINDINGS",astl) -> 
      Bindings (List.map cvt_bind astl)
  | Node(_,"REDEXP",[Node(_,redname,args)]) -> 
      Redexp (redname,args)
  | Node(_,"CLAUSE",cl) -> 
      Clause (List.map (compose id_of_string nvar_of_ast) cl)
  | Node(_,"TACTIC",[ast]) -> 
      Tacexp ast
  | Node(_,"FIXEXP", [Nvar(_,s); Num(_,n);Node(_,"COMMAND",[c])]) ->
      Fixexp (id_of_string s,n,c)
  | Node(_,"COFIXEXP", [Nvar(_,s); Node(_,"COMMAND",[c])]) ->
      Cofixexp (id_of_string s,c)
  | Node(_,"INTROPATTERN", [ast]) -> 
      Intropattern (cvt_intro_pattern ast)
  | Node(_,"LETPATTERNS", astl) -> 
      let (o,l) = (cvt_letpatterns astl) in Letpatterns (o,l)
  | x -> 
      anomaly_loc (Ast.loc x, "Tacinterp.cvt_bind",
                   [< 'sTR "Unrecognizable ast node : "; print_ast x >])

let rec interp = function
  | Node(loc,opn,tl) ->
      (match (opn, tl) with
         | ("TACTICLIST",_) -> interp_semi_list tclIDTAC tl
	 | ("DO",[n;tac]) -> tclDO (num_of_ast n) (interp tac)
	 | ("TRY",[tac]) -> tclTRY (interp tac)
	 | ("INFO",[tac]) -> tclINFO (interp tac)
	 | ("REPEAT",[tac]) -> tclREPEAT (interp tac)
	 | ("ORELSE",[tac1;tac2]) -> tclORELSE (interp tac1) (interp tac2)
	 | ("FIRST",l) -> tclFIRST (List.map interp l)
	 | ("TCLSOLVE",l) -> tclSOLVE (List.map interp l)
	 | ("CALL",macro::args) ->
	     interp (macro_expand loc (nvar_of_ast macro) 
		       (List.map cvt_arg args))
	 | _ -> interp_atomic loc opn (List.map cvt_arg tl))
  | ast -> user_err_loc(Ast.loc ast,"Tacinterp.interp",
			[< 'sTR"A non-ASTnode constructor was found" >])
	
and interp_atomic loc opn args = 
  try 
    tacinterp_map opn args
  with Not_found ->
    try 
      vernac_tactic(opn,args)
    with e -> 
      Stdpp.raise_with_loc loc e
	
and interp_semi_list acc = function
  | (Node(_,"TACLIST",seq))::l ->
      interp_semi_list (tclTHENS acc (List.map interp seq)) l
  | t::l -> interp_semi_list (tclTHEN acc (interp t)) l
  | [] -> acc

	
let is_just_undef_macro ast =
  match ast with
    | Node(_,"TACTICLIST",[Node(loc,"CALL",macro::_)]) ->
        let id = nvar_of_ast macro in
      	(try let _ = Macros.lookup id in None with Not_found -> Some id)
    | _ -> None

let vernac_interp =
  let gentac =
    hide_tactic "Interpret"
      (fun vargs gl -> match vargs with 
	 | [Tacexp com] -> interp com gl
	 | _ -> assert false) 
  in
  fun com -> gentac [Tacexp com]

let vernac_interp_atomic =
  let gentac =
    hide_tactic "InterpretAtomic"
      (fun argl gl -> match argl with 
	 | (Identifier id)::args -> 
	     interp_atomic dummy_loc (string_of_id id) args gl
	 | _ -> assert false)
  in 
  fun opn args -> gentac ((Identifier opn)::args)

let bad_tactic_args s =
  anomalylabstrm s
    [< 'sTR"Tactic "; 'sTR s; 'sTR" called with bad arguments" >]
