(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp_control
open Pp
open System
open Util
open Names
open Vernacinterp
open Mlimport
open Miniml
open Genpp

(*s Utility functions. *)

let open_par = function true -> [< 'sTR"(" >] | false -> [< >]
let close_par = function true -> [< 'sTR")" >] | false -> [< >]

(* uncurry_list : ('a -> std_pcmds) -> 'a list -> std_ppcmds
 * formats a list [x1;...;xn] in its uncurried form (x1,...,xn). *)

let uncurry_list f = function
    []  -> [< >]
  | [x] -> [< (f x) >]
  | xl  -> [< 'sTR"(" ;
      	      prlist_with_sep (fun () -> [< 'sTR", " >]) (fun x -> (f x)) xl ;
	      'sTR")"
      	    >]

let uncurry_list2 f = function
    []  -> [< >]
  | [x] -> [< (f x) >]
  | xl  -> [< 'sTR"(" ;
      	      hOV 0 [< prlist_with_sep
			 (fun () -> [< 'sTR"," ; 'sPC >]) 
			 (fun x -> (f x)) xl  ;
		       'sTR")" >]
      	    >]

type extraction_params = {
  needed : identifier list;
  expand : identifier list;
  expansion : bool;
  exact : bool
  }

let list_ids = 
  List.map (function (VARG_IDENTIFIER id) -> id | _ -> assert false)

let rec parse_rem op = function
    VARG_STRING "noopt" :: r -> 
      parse_rem 
	{ needed = op.needed; expand = op.expand; 
	  expansion = false; exact = op.exact } r
  | VARG_STRING "exact" :: r -> 
      parse_rem 
	{ needed = op.needed; expand = op.expand; 
	  expansion = op.expansion; exact = true } r
  | VARG_STRING "expand" :: VARG_VARGLIST l :: r ->
      parse_rem { needed = op.needed; expand = op.expand @ list_ids l;
		  expansion = op.expansion; exact = op.exact } r
  | [] -> op
  | _ -> assert false

let parse_param = function
    VARG_VARGLIST l :: r ->
      parse_rem { needed = list_ids l; expand = []; 
		  expansion = true; exact = false } r
  | _ -> assert false

module type ExtractionParams = sig
  val opt : extraction_params -> ml_decl list -> ml_decl list
  val suffixe : string
  val cofix : bool
  val pp_of_env : ml_decl list -> std_ppcmds
  module Renaming : Extraction.Renaming
end

module Make = functor (M : ExtractionParams) -> struct

  module Translation = Extraction.Make(M.Renaming)

  let change_names =
    map_succeed 
      (fun id -> try Extraction.get_global_name id 
       with Anomaly _ -> failwith "caught") 
      
  let exact prm env =
    let keep = function
      | Dtype il -> 
	  List.exists (fun (_,id,_) -> List.mem id prm.needed) il
      | Dabbrev (id,_,_) -> List.mem id prm.needed
      | Dglob (id,_) -> List.mem id prm.needed
    in
    map_succeed 
      (fun d -> if not (keep d) then failwith "caught" else d) env
      
  let pp cicenv prm =
    let mlenv = Translation.extract M.cofix cicenv in
    let needed' = change_names prm.needed in
    let expand' = change_names prm.expand in
    let prm' = 
      { needed = needed' ; expand = expand' ; 
	expansion = prm.expansion ; exact = prm.exact }
    in
    let env = M.opt prm' mlenv in
    let env = if prm'.exact then exact prm' env else env in
    M.pp_of_env env

  let pp_recursive prm =
    let gl = List.map (Nametab.sp_of_id CCI) prm.needed in
    let cicenv = Close_env.close gl in
    pp cicenv prm

  let write file strm =
    let chan = open_trapping_failure open_out file M.suffixe in
    let ft = with_output_to chan in
    (try  pP_with ft strm ; pp_flush_with ft ()
     with e -> pp_flush_with ft () ; close_out chan; raise e);
    close_out chan

  let write_extraction_file file prm =
    (* TODO: comment tester qu'il n'y a pas de section ouverte et
	 pemettre pour autant la compilation (donc une section
	 particuliere qui est le module) if Lib.cwd() <> [] then
	 errorlabstrm "Genpp.Pp_to_file.write_extraction_file" [< 'sTR
	 "There are still open sections !" >]; *)
    let strm = pp_recursive prm in
    write file strm

  let write_extraction_module m =
    let cicenv = Close_env.module_env m in
    let idl = List.map (Environ.id_of_global (Global.env())) cicenv in
    let prm = 
      { needed = idl; expand = []; expansion = false; exact = true } in
    let strm = pp cicenv prm in
    let file = string_of_id m in
    write file strm
	
end
