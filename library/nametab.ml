
(* $Id$ *)

open Util
open Names
open Libobject
open Declarations
open Term

type cci_table = global_reference Stringmap.t
type obj_table = (section_path * obj) Stringmap.t
type mod_table = module_contents Stringmap.t
and module_contents = Closed of cci_table * obj_table * mod_table

let mod_tab = ref (Stringmap.empty : mod_table)
let cci_tab = ref (Stringmap.empty : cci_table)
let obj_tab = ref (Stringmap.empty : obj_table)

let sp_of_id _ id = Stringmap.find (string_of_id id) !cci_tab

let constant_sp_of_id id =
  match Stringmap.find (string_of_id id) !cci_tab with
    | ConstRef sp -> sp
    | _ -> raise Not_found

let push_cci s sp = cci_tab := Stringmap.add s sp !cci_tab
let push_obj s sp = obj_tab := Stringmap.add s sp !obj_tab
let push_module s mc = mod_tab := Stringmap.add s mc !mod_tab

let push_object id = push_obj (string_of_id id)
let push id = push_cci (string_of_id id) 

let locate qid =
  let (dir,id) = repr_qualid qid in
  let rec search (ccitab,modtab) = function
    | id :: dir' ->
	let (Closed (ccitab, _, modtab)) = Stringmap.find id modtab in
	search (ccitab,modtab) dir'
    | [] -> Stringmap.find id ccitab
  in search (!cci_tab,!mod_tab) dir

let locate_obj qid =
  let (dir,id) = repr_qualid qid in
  let rec search (objtab,modtab) = function
    | id :: dir' ->
	let (Closed (_, objtab, modtab)) = Stringmap.find id modtab in
	search (objtab,modtab) dir'
    | [] -> Stringmap.find id objtab
  in search (!obj_tab,!mod_tab) dir

let locate_constant qid =
  match locate qid with
    | ConstRef sp -> sp
    | _ -> raise Not_found

let open_module_contents s =
  let (Closed (ccitab,objtab,modtab)) = Stringmap.find s !mod_tab in
  Stringmap.iter push_cci ccitab;
  Stringmap.iter (fun _ -> Libobject.open_object) objtab;
  Stringmap.iter push_module modtab

(* Registration as a global table and roolback. *)
    
let init () =
  cci_tab := Stringmap.empty;
  obj_tab := Stringmap.empty;
  mod_tab := Stringmap.empty;

type frozen = cci_table Stringmap.t * obj_table Stringmap.t * mod_table Stringmap.t

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

