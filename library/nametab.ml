
(* $Id$ *)

open Util
open Names
open Libobject
open Declarations
open Term

type cci_table = global_reference Idmap.t
type obj_table = (section_path * obj) Idmap.t
type mod_table = module_contents Stringmap.t
and module_contents = Closed of cci_table * obj_table * mod_table

let mod_tab = ref (Stringmap.empty : mod_table)
let cci_tab = ref (Idmap.empty : cci_table)
let obj_tab = ref (Idmap.empty : obj_table)

let sp_of_id _ id = Idmap.find id !cci_tab

let constant_sp_of_id id =
  match Idmap.find id !cci_tab with
    | ConstRef sp -> sp
    | _ -> raise Not_found

let push_cci id sp = cci_tab := Idmap.add id sp !cci_tab
let push_obj id sp = obj_tab := Idmap.add id sp !obj_tab
let push_module id mc = mod_tab := Stringmap.add id mc !mod_tab

let push = push_cci

let locate sp =
  let (dir,id,_) = repr_path sp in
  let rec search (ccitab,modtab) = function
    | id :: dir' ->
	let (Closed (ccitab, _, modtab)) = Stringmap.find id modtab in
	search (ccitab,modtab) dir'
    | [] -> Idmap.find id ccitab
  in search (!cci_tab,!mod_tab) dir

let locate_obj sp =
  let (dir,id,_) = repr_path sp in
  let rec search (objtab,modtab) = function
    | id :: dir' ->
	let (Closed (_, objtab, modtab)) = Stringmap.find id modtab in
	search (objtab,modtab) dir'
    | [] -> Idmap.find id objtab
  in search (!obj_tab,!mod_tab) dir

let locate_constant sp =
  match locate sp with
    | ConstRef sp -> sp
    | _ -> raise Not_found

let open_module_contents id =
  let (Closed (ccitab,objtab,modtab)) = Stringmap.find id !mod_tab in
  Idmap.iter push_cci ccitab;
  Idmap.iter (fun _ -> Libobject.open_object) objtab;
  Stringmap.iter push_module modtab

(* Registration as a global table and roolback. *)
    
let init () =
  cci_tab := Idmap.empty;
  obj_tab := Idmap.empty;
  mod_tab := Stringmap.empty;

type frozen = cci_table Idmap.t * obj_table Idmap.t * mod_table Stringmap.t

let freeze () = (!cci_tab, !obj_tab, !mod_tab)
		  
let unfreeze (ccitab,objtab,modtab) =
  cci_tab := ccitab; obj_tab := objtab; mod_tab := modtab

let _ = 
  Summary.declare_summary "names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let rollback f x =
  let fs = freeze () in
  try f x with e -> begin unfreeze fs; raise e end

