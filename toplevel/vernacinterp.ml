
(* $Id$ *)

open Pp
open Util
open Names
open Himsg
open Proof_type
open Tacinterp
open Coqast
open Ast

exception ProtectedLoop
exception Drop
exception Quit

let disable_drop e =
  if e <> Drop then e
  else UserError("Vernac.disable_drop",[< 'sTR"Drop is forbidden." >])

type vernac_arg = 
  | VARG_VARGLIST of vernac_arg list
  | VARG_STRING of string
  | VARG_NUMBER of int
  | VARG_NUMBERLIST of int list
  | VARG_IDENTIFIER of identifier
  | VARG_QUALID of section_path
  | VARG_CONSTANT of constant_path
  | VCALL of string * vernac_arg list
  | VARG_CONSTR of Coqast.t
  | VARG_CONSTRLIST of Coqast.t list
  | VARG_TACTIC of Coqast.t
  | VARG_TACTIC_ARG of tactic_arg
  | VARG_BINDER of identifier list * Coqast.t
  | VARG_BINDERLIST of (identifier list * Coqast.t) list
  | VARG_AST of Coqast.t
  | VARG_ASTLIST of Coqast.t list
  | VARG_UNIT
  | VARG_DYN of Dyn.t


(* Table of vernac entries *)
let vernac_tab =
  (Hashtbl.create 51 : (string, vernac_arg list -> unit -> unit) Hashtbl.t)

let vinterp_add s f =
  try 
    Hashtbl.add vernac_tab s f
  with Failure _ ->
    errorlabstrm "vinterp_add"
      [< 'sTR"Cannot add the vernac command " ; 'sTR s ; 'sTR" twice" >]

let overwriting_vinterp_add s f =
  begin 
    try 
      let _ = Hashtbl.find vernac_tab s in Hashtbl.remove vernac_tab s 
    with Not_found -> ()
  end;
  Hashtbl.add vernac_tab s f

let vinterp_map s =
  try 
    Hashtbl.find vernac_tab s
  with Not_found -> 
    errorlabstrm "Vernac Interpreter"
      [< 'sTR"Cannot find vernac command " ; 'sTR s >]

let vinterp_init () = Hashtbl.clear vernac_tab


(* Conversion Coqast.t -> vernac_arg *)
let rec cvt_varg ast =
  match ast with
    | Node(_,"VERNACARGLIST",l) -> 
	VARG_VARGLIST (List.map cvt_varg l)
    | Node(_,"VERNACCALL",(Str (_,na))::l) ->
        VCALL (na,List.map cvt_varg l)
    | Node(_,"VERNACCALL",(Id (_,na))::l) ->
        VCALL (na,List.map cvt_varg l)

    | Nvar(_,s) -> VARG_IDENTIFIER (id_of_string s)
    | Node(loc,"QUALIDARG",p) -> VARG_QUALID (Astterm.interp_qualid p)
    | Node(loc,"QUALIDCONSTARG",p) ->
	let q = Astterm.interp_qualid p in
	let sp =
	  try Nametab.locate_constant q
	  with Not_found -> Pretype_errors.error_global_not_found_loc loc q
	in VARG_CONSTANT sp
    | Str(_,s) -> VARG_STRING s
    | Num(_,n) -> VARG_NUMBER n
    | Node(_,"NONE",[]) -> VARG_UNIT
    | Node(_,"CONSTR",[c]) -> VARG_CONSTR c
    | Node(_,"CONSTRLIST",l) -> VARG_CONSTRLIST l
    | Node(_,"TACTIC",[c]) -> VARG_TACTIC c
    | Node(_,"BINDER",c::idl) ->
        VARG_BINDER(List.map (compose id_of_string nvar_of_ast) idl, c)
    | Node(_,"BINDERLIST",l) ->
        VARG_BINDERLIST
          (List.map (compose (function 
				| (VARG_BINDER (x_0,x_1)) -> (x_0,x_1)
			  	| _ -> assert false) cvt_varg) l)
    | Node(_,"NUMBERLIST",ln) ->
        VARG_NUMBERLIST (List.map num_of_ast ln) 

    | Node(_,"AST",[a]) -> VARG_AST a
    | Node(_,"ASTLIST",al) -> VARG_ASTLIST al
    | Node(_,"TACTIC_ARG",[targ]) ->
      let (evc,env)= Command.get_current_context () in
      VARG_TACTIC_ARG (interp_tacarg (evc,env,[],[],None,get_debug ()) targ)
    | Node(_,"VERNACDYN",[Dynamic (_,d)]) -> VARG_DYN d
    | _ -> anomaly_loc (Ast.loc ast, "Vernacinterp.cvt_varg",
                        [< 'sTR "Unrecognizable ast node of vernac arg:";
			  'bRK(1,0); print_ast ast >])

(* Interpretation of a vernac command *)

let call (opn,converted_args) =
  let loc = ref "Looking up command" in
  try
    let callback = vinterp_map opn in
    loc:= "Checking arguments";
    let hunk = callback converted_args in
    loc:= "Executing command";
    hunk()
  with
    | Drop -> raise Drop
    | ProtectedLoop -> raise ProtectedLoop
    | e ->
        if !Options.debug then
	  mSGNL [< 'sTR"Vernac Interpreter " ; 'sTR !loc >];
        raise e

let interp = function
  | Node(_,opn,argl) as cmd ->
      let converted_args =
      	try 
	  List.map cvt_varg argl
      	with e ->
          if !Options.debug then
            mSGNL [< 'sTR"Vernac Interpreter " ; 'sTR"Converting arguments" >];
          raise e
      in 
      call (opn,converted_args)
  | cmd -> 
      errorlabstrm "Vernac Interpreter"
        [< 'sTR"Malformed vernac AST : " ; print_ast cmd >]

let bad_vernac_args s =
  anomalylabstrm s
    [< 'sTR"Vernac "; 'sTR s; 'sTR" called with bad arguments" >]
