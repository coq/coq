
(* $Id$ *)

open Pp
open Util
open Names
open Term
open Proof_type
open Libobject
open Library
open Coqast
open Pcoq
open Ast

(* The data stored in the table *)

type macro_data = {
  mac_args : string list;
  mac_body : Ast.act }

(* Summary and Object declaration *)

type t = macro_data Stringmap.t
type frozen_t = macro_data Stringmap.t

let mactab = ref Stringmap.empty

let lookup id = Stringmap.find id !mactab

let _ = 
  let init () = mactab := Stringmap.empty  in
  let freeze () = !mactab in
  let unfreeze fs = mactab := fs in
  Summary.declare_summary "tactic-macro"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init }

let (inMD,outMD) =
  let add (na,md) = mactab := Stringmap.add na md !mactab in
  let cache_md (_,(na,md)) = add (na,md) in 
  let specification_md x = x in
  declare_object ("TACTIC-MACRO-DATA",
                  { cache_function = cache_md;
		    load_function = (fun _ -> ());
                    open_function = cache_md;
                    specification_function = specification_md })

let add_macro_hint na (ids,body) =
  if Stringmap.mem na !mactab then errorlabstrm "add_macro_hint"
    [< 'sTR "There is already a Tactic Macro named "; 'sTR na >];
  let _ = Lib.add_leaf (id_of_string na) OBJ
	    (inMD(na,{mac_args = ids; mac_body = body})) in
  ()

let macro_expand macro_loc macro argcoms = 
  let md =
    try 
      lookup macro
    with Not_found ->
      user_err_loc(macro_loc,"macro_expand",
		   [< 'sTR"Tactic macro ";'sTR macro; 'sPC;
		      'sTR"not defined" >]) 
  in
  let transform = 
    List.map 
      (function
	 | Command c -> c
	 | _ -> user_err_loc(macro_loc,"macro_expand", 
			     [<'sTR "The arguments of a tactic macro";
			       'sPC; 'sTR"must be terms">])) 
  in
  let argcoms = transform argcoms in
  if List.length argcoms <> List.length md.mac_args then 
    user_err_loc
      (macro_loc,"macro_expand",
       [< 'sTR "Tactic macro "; 'sTR macro; 'sPC;
          'sTR "applied to the wrong number of arguments:"; 'sPC;
          'iNT (List.length argcoms) ; 'sTR" instead of ";
          'iNT (List.length md.mac_args) >]);
  let astb = 
    List.map2 (fun id argcom -> (id, Vast argcom)) md.mac_args argcoms in
  match Ast.eval_act macro_loc astb md.mac_body with
    | Vast ast -> ast
    | _ -> anomaly "expand_macro : eval_act did not return a Vast"


