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
open Nameops
open Miniml
open Table
open Mlutil
open Ocaml
open Nametab
open Util

(*s Modules considerations *)

let current_module = ref None

let sp_of_r r = match r with 
    | ConstRef sp -> sp
    | IndRef (sp,_) -> sp
    | ConstructRef ((sp,_),_) -> sp
    | _ -> assert false

let qualid_of_dirpath d = 
  let dir,id = split_dirpath d in 
  make_qualid dir id 

(* [long_module r] computes the dirpath of the module of the global 
   reference [r]. The difficulty comes from the possible section names 
   at the beginning of the dirpath (due to Remark). *)

let long_module r = 
  let rec check_module d = 
    try 
      locate_loaded_library (qualid_of_dirpath d)
    with Not_found -> 
      let d' = 
	try 
	  dirpath_prefix d 
	with _ -> errorlabstrm "long_module_message"
	(str "Can't find the module of" ++ spc () ++ 
	   Printer.pr_global r)
      in check_module d' 
  in check_module (dirpath (sp_of_r r))

(* From a valid module dirpath [d], we check if [r] belongs to this module. *)
      
let is_long_module d r = 
  let dir = repr_dirpath d 
  and dir' = repr_dirpath (dirpath (sp_of_r r)) in 
  let l = List.length dir 
  and l' = List.length dir' in 
  if l' < l then false 
  else dir = snd (list_chop (l'-l) dir')

let short_module r = 
  snd (split_dirpath (long_module r))

let module_option r = 
  let m = short_module r in
  if Some m = !current_module then ""
  else (String.capitalize (string_of_id m)) ^ "."

let check_ml r d = 
  if to_inline r then 
    try 
      find_ml_extraction r 
    with Not_found -> d
  else d

(*s Tables of global renamings *)

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
  let rename_global r = Termops.id_of_global (Global.env()) r
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
	 let id = Termops.id_of_global (Global.env()) r in
	 rename_global_id (lowercase_id id))
      
  let rename_global r = 
    cache r
      (fun r -> 
	 let id = Termops.id_of_global (Global.env()) r in
	 match r with
	   | ConstructRef _ -> rename_global_id (uppercase_id id)
	   | _ -> rename_global_id (lowercase_id id))
      
  let pp_type_global r = 
    str (check_ml r (string_of_id (rename_type_global r)))
      
  let pp_global r = 
    str (check_ml r (string_of_id (rename_global r)))
      
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
	 let id = Termops.id_of_global (Global.env()) r in 
	 rename_global_id r id (lowercase_id id) "coq_")

  let rename_global r =
    cache r 
      (fun r -> 
	 let id = Termops.id_of_global (Global.env()) r in 
	 match r with
	   | ConstructRef _ -> rename_global_id r id (uppercase_id id) "Coq_"
	   | _ -> rename_global_id r id (lowercase_id id) "coq_")

  let pp_type_global r = 
    str 
      (check_ml r ((module_option r)^(string_of_id (rename_type_global r))))

  let pp_global r = 
    str
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
  cons_cofix := Refset.empty;
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
  if decls <> [] then pp_with ft (hv 0 (preamble prm));
  begin 
    try
      List.iter (fun d -> msgnl_with ft (pp_decl d)) decls
    with e ->
      pp_flush_with ft (); close_out cout; raise e
  end;
  pp_flush_with ft ();
  close_out cout



