(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Names
open Miniml
open Table
open Mlutil
open Ocaml
open Nametab


(*s Modules considerations *)

let current_module = ref None

let module_of_r r = 
  snd (split_dirpath (dirpath (sp_of_r r)))

let module_option r = 
  let m = module_of_r r in
  if Some m = !current_module then ""
  else (String.capitalize (string_of_id m)) ^ "."

let check_ml r d = 
  if to_inline r then 
    try 
      find_ml_extraction r 
    with Not_found -> d
  else d


(*s tables of global renamings *)

let keywords = ref Idset.empty
let global_ids = ref Idset.empty

let renamings = Hashtbl.create 97

let cache r f =  
  try Hashtbl.find renamings r 
  with Not_found -> let id = f r in Hashtbl.add renamings r id; id 
    
(*s Renaming issues at toplevel *)

module ToplevelParams = struct
  let toplevel = true
  let globals () = Idset.empty
  let rename_global r = Names.id_of_string (Global.string_of_global r)
  let pp_type_global = Printer.pr_global
  let pp_global = Printer.pr_global
end

(*s Renaming issues for a monolithic extraction. *)

module MonoParams = struct

  let toplevel = false

  let globals () = !global_ids
		     
  let rename_global_id id = 
    let id' = rename_id id !global_ids in
    global_ids := Idset.add id' !global_ids; 
    id'

  let rename_type_global r =  
    cache r
      (fun r -> 
	 let id = Environ.id_of_global (Global.env()) r in
	 rename_global_id (lowercase_id id))
      
  let rename_global r = 
    cache r
      (fun r -> 
	 let id = Environ.id_of_global (Global.env()) r in
	 match r with
	   | ConstructRef _ -> rename_global_id (uppercase_id id)
	   | _ -> rename_global_id (lowercase_id id))
      
  let pp_type_global r = 
    string (check_ml r (string_of_id (rename_type_global r)))
      
  let pp_global r = 
    string (check_ml r (string_of_id (rename_global r)))
      
end


(*s Renaming issues in a modular extraction. *)

module ModularParams = struct

  let toplevel = false

  let globals () = !global_ids 

  let clash r id = 
    try 
      let _ = locate (make_qualid (dirpath (sp_of_r r)) id)
      in true
    with _ -> false

  let rename_global_id r id id' prefix =
    let id' = 
      if (Idset.mem id' !keywords) || (id <> id' && clash r id') then 
	id_of_string (prefix^(string_of_id id))
      else id'
    in global_ids := Idset.add id' !global_ids; id'

  let rename_type_global r = 
    cache r 
      (fun r ->     
	 let id = Environ.id_of_global (Global.env()) r in 
	 rename_global_id r id (lowercase_id id) "coq_")

  let rename_global r =
    cache r 
      (fun r -> 
	 let id = Environ.id_of_global (Global.env()) r in 
	 match r with
	   | ConstructRef _ -> rename_global_id r id (uppercase_id id) "Coq_"
	   | _ -> rename_global_id r id (lowercase_id id) "coq_")

  let pp_type_global r = 
    string 
      (check_ml r ((module_option r)^(string_of_id (rename_type_global r))))

  let pp_global r = 
    string 
      (check_ml r ((module_option r)^(string_of_id (rename_global r))))

end


module ToplevelPp = Ocaml.Make(ToplevelParams)

module OcamlMonoPp = Ocaml.Make(MonoParams)
module OcamlModularPp = Ocaml.Make(ModularParams)

module HaskellMonoPp = Haskell.Make(MonoParams)
module HaskellModularPp = Haskell.Make(ModularParams)


(*s Extraction to a file. *)

let init_global_ids lang = 
  Hashtbl.clear renamings;
  keywords := 
  (match lang with 
     | "ocaml" -> Ocaml.keywords
     | "haskell" -> Haskell.keywords
     | _ -> assert false);
  global_ids := !keywords

let extract_to_file f prm decls =
  current_module := prm.mod_name;
  init_global_ids prm.lang;
  let preamble,pp_decl = match prm.lang,prm.mod_name with 
    | "ocaml", None -> Ocaml.preamble, OcamlMonoPp.pp_decl
    | "ocaml", _ -> Ocaml.preamble, OcamlModularPp.pp_decl
    | "haskell", None -> Haskell.preamble, HaskellMonoPp.pp_decl
    | "haskell", _ -> Haskell.preamble, HaskellModularPp.pp_decl
    | _ -> assert false
  in
  let cout = open_out f in
  let ft = Pp_control.with_output_to cout in
  if decls <> [] then pP_with ft (hV 0 (preamble prm));
  begin 
    try
      List.iter (fun d -> mSGNL_with ft (pp_decl d)) decls
    with e ->
      pp_flush_with ft (); close_out cout; raise e
  end;
  pp_flush_with ft ();
  close_out cout



