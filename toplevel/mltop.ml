
(* $Id$ *)

open Util
open Pp
open Libobject
open Library
open System
open Vernacinterp

(* Code to hook Coq into the ML toplevel -- depends on having the
   objective-caml compiler mostly visible. The functions implemented here are:
   \begin{itemize}
   \item [dir_ml_load name]: Loads the ML module fname from the current ML 
     path. 
   \item [dir_ml_use]: Directive #use of Ocaml toplevel
   \item [dir_ml_dir]: Directive #directory of Ocaml toplevel
   \end{itemize}
 
   How to build an ML module interface with these functions.
   The idea is that the ML directory path is like the Coq directory
   path.  So we can maintain the two in parallel.
   In the same way, we can use the "ml_env" as a kind of ML
   environment, which we freeze, unfreeze, and add things to just like
   to the other environments.
   Finally, we can create an object which is an ML module, and require
   that the "caching" of the ML module cause the loading of the
   associated ML file, if that file has not been yet loaded.  Of
   course, the problem is how to record dependences between ML
   modules.
   (I do not know of a solution to this problem, other than to
   put all the needed names into the ML Module object.) *)

(* This path is where we look for .cmo *)
let coq_mlpath_copy = ref []
let keep_copy_mlpath s = coq_mlpath_copy := (glob s)::!coq_mlpath_copy

(* If there is a toplevel under Coq *)
type toplevel = { 
  load_obj : string -> unit;
  use_file : string -> unit;
  add_dir  : string -> unit }

(* Determines the behaviour of Coq with respect to ML files (compiled 
   or not) *)
type kind_load =
  | WithTop of toplevel
  | WithoutTop
  | Native

(* Must be always initialized *)
let load = ref Native

(* Sets and initializes the kind of loading *)
let set kload = load := kload

(* Resets load *)
let remove ()= load :=N ative

(* Tests if an Ocaml toplevel runs under Coq *)
let is_ocaml_top () =
  match !load with
    | WithTop _ -> true
    |_ -> false

(* Tests if we can load ML files *)
let enable_load () =
  match !load with
    | WithTop _ | WithoutTop -> true
    |_ -> false

(* Dynamic loading of .cmo *)
let dir_ml_load s = 
  match !load with
    | WithTop t -> 
	if is_in_path !coq_mlpath_copy s then
          try t.load_obj s
          with
            | (UserError _ | Failure _ | Anomaly _ | Not_found as u) -> raise u
            | _ -> errorlabstrm "Mltop.load_object"
                  [< 'sTR"Cannot link ml-object "; 'sTR s;
		     'sTR" to Coq code." >]
	else 
	  errorlabstrm "Mltop.load_object"
            [< 'sTR"File not found on loadpath : "; 'sTR s >]
    | WithoutTop ->
	if is_in_path !coq_mlpath_copy s then
          let gname = where_in_path !coq_mlpath_copy s in
          try
            Dynlink.loadfile gname;
	    Dynlink.add_interfaces 
	      [(String.capitalize (Filename.chop_suffix
				     (Filename.basename gname) ".cmo"))] 
	      [Filename.dirname gname]
	  with
	    | Dynlink.Error(a) ->
		errorlabstrm "Mltop.load_object"
                  [< 'sTR (Dynlink.error_message a) >]
	else errorlabstrm "Mltop.load_object"
          [< 'sTR"File not found on loadpath : "; 'sTR s >]
    | Native ->
	errorlabstrm "Mltop.no_load_object"
          [< 'sTR"Loading of ML object file forbidden in a native Coq" >]

(* Dynamic interpretation of .ml *)
let dir_ml_use s =
  match !load with
    | WithTop t -> t.use_file s
    | _ -> warning "Cannot access the ML compiler"

(* Adds a path to the ML paths *)
let dir_ml_dir s =
  match !load with
    | WithTop t -> t.add_dir s; keep_copy_mlpath s
    | WithoutTop -> keep_copy_mlpath s
    | _ -> ()

(* For Rec Add ML Path *)
let rdir_ml_dir dir=
  List.iter dir_ml_dir (alldir dir)

(* convertit un nom quelconque en nom de fichier ou de module *) 
let mod_of_name name =
  let base =
    if Filename.check_suffix name ".cmo" then
      Filename.chop_suffix name ".cmo"
    else 
      name
  in 
  String.capitalize base

let file_of_name name = make_suffix (String.uncapitalize name) ".cmo"

(* TODO: supprimer ce hack, si possible *)
(* Initialisation of ML modules that need the state (ex: tactics like
 * natural, omega ...)
 * Each module may add some inits (function of type unit -> unit).
 * These inits are executed right after the initial state loading if the
 * module is statically linked, or after the loading if it is required. *)

let init_list = ref ([] : (unit -> unit) list)

let add_init_with_state init_fun =
  init_list := init_fun :: !init_list

let init_with_state () =
  List.iter (fun f -> f()) (List.rev !init_list); init_list := []


(* known_loaded_module contains the names of the loaded ML modules
 * (linked or loaded with load_object). It is used not to loaded a 
 * module twice. It is NOT the list of ML modules Coq knows. *)

type ml_module_object = { mnames : string list }

let known_loaded_modules = ref ([] : string list)

let add_known_module mname =
  known_loaded_modules := add_set mname !known_loaded_modules

let module_is_known mname = List.mem mname !known_loaded_modules

let load_object mname fname=
  dir_ml_load fname;
  init_with_state();
  add_known_module mname

(* Summary of declared ML Modules *)

let loaded_modules = ref ([] : string list)
let get_loaded_modules () = !loaded_modules
let add_loaded_module md =
  loaded_modules := add_set md !loaded_modules

let orig_loaded_modules = ref (get_loaded_modules ())
let init_ml_modules () = loaded_modules := !orig_loaded_modules


let unfreeze_ml_modules x =
  List.iter
    (fun name ->
       let mname = mod_of_name name in
       if not (module_is_known mname) then
         if enable_load() then
           let fname= file_of_name mname in
           load_object mname fname                
         else 
	   errorlabstrm "Mltop.unfreeze_ml_modules"
             [< 'sTR"Loading of ML object file forbidden in a native Coq" >];
       add_loaded_module mname)
    x

let _ = 
  Summary.declare_summary "ML-MODULES"
    { Summary.freeze_function = (fun () -> List.rev (get_loaded_modules()));
      Summary.unfreeze_function = (fun x -> unfreeze_ml_modules x);
      Summary.init_function = (fun () -> init_ml_modules ()) }

(* Same as restore_ml_modules, but verbosely *)

let cache_ml_module_object {mnames=mnames} =
  List.iter
    (fun name ->
       let mname = mod_of_name name in
       if not (module_is_known mname) then
         let fname= file_of_name mname in
         begin try 
	   mSG [< 'sTR"[Loading ML file " ; 'sTR fname ; 'sTR" ..." >];
           load_object mname fname;
           mSGNL [< 'sTR"done]" >]
         with e -> 
	   begin pPNL [< 'sTR"failed]" >]; raise e end
	 end;
         add_loaded_module mname)
    mnames

let specification_ml_module_object x = x
					 
let (inMLModule,outMLModule) =
  declare_object ("ML-MODULE",
                  { load_function = cache_ml_module_object;
                    cache_function = (fun _ -> ());
                    specification_function = specification_ml_module_object })

let declare_ml_modules l =
  add_anonymous_object (inMLModule {mnames=l})
    
let print_ml_path () =
  let l = !coq_mlpath_copy in
  pPNL [< 'sTR"ML Load Path:"; 'fNL; 'sTR"  ";
          hV 0 (prlist_with_sep pr_fnl (fun s -> [< 'sTR s >]) l) >]

let _ = vinterp_add "DeclareMLModule"
	  (fun l ->
	     let sl = List.map 
			(function (VARG_STRING s) -> s 
			   | _ -> anomaly "DeclareMLModule : not a string") 
			l
	     in
    	     fun () -> declare_ml_modules sl)
	  
let _ = vinterp_add "AddMLPath"
	  (function 
	     | [VARG_STRING s] ->
		 (fun () -> dir_ml_dir (glob s))
	     | _ -> anomaly "AddMLPath : not a string")

let _ = vinterp_add "RecAddMLPath"
	  (function 
	     | [VARG_STRING s] ->
		 (fun () -> rdir_ml_dir (glob s))
	     | _ -> anomaly "RecAddMLPath : not a string")

let _ = vinterp_add "PrintMLPath"
	  (function 
	     | [] -> (fun () -> print_ml_path ())
	     | _ -> anomaly "PrintMLPath : does not expect any argument")

	  (* Printing of loaded ML modules *)
	  
let print_ml_modules () =
  let l = get_loaded_modules () in
  pP [< 'sTR"Loaded ML Modules : " ;
        hOV 0 (prlist_with_sep pr_fnl (fun s -> [< 'sTR s >]) l) >]

let _ = vinterp_add "PrintMLModules"
	  (function 
	     | [] -> (fun () -> print_ml_modules ())
	     | _ -> anomaly "PrintMLModules : does not expect an argument")
