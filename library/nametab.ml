
(* $Id$ *)

open Names

let cci_tab = ref Idmap.empty
let fw_tab = ref Idmap.empty

let fw_sp_of_id id =
  Idmap.find id !fw_tab

let sp_of_id kind id =
  match kind with
    | FW -> Idmap.find id !fw_tab
    | CCI -> Idmap.find id !cci_tab
    | OBJ -> invalid_arg "Nametab.sp_of_id"
	  
let push id sp =
  match kind_of_path sp with
    | FW -> fw_tab := Idmap.add id sp !fw_tab
    | CCI -> cci_tab := Idmap.add id sp !cci_tab
    | OBJ -> invalid_arg "Nametab.push"

(* Registration as a global table and roolback. *)
    
let init () =
  cci_tab := Idmap.empty;
  fw_tab := Idmap.empty

type frozen = section_path Idmap.t * section_path Idmap.t

let freeze () = (!cci_tab, !fw_tab)
		  
let unfreeze (cci,fw) = cci_tab := cci; fw_tab := fw

let _ = 
  Summary.declare_summary "names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let rollback f x =
  let fs = freeze () in
  try f x with e -> begin unfreeze fs; raise e end
