
(* $Id$ *)

open Util
open Names
open Environ
open Libobject
open Lib

(* Modules on disk contain the following informations (after the magic 
   number, and before the digest). *)

type module_disk = { 
  md_name : string;
  md_compiled_env : compiled_env;
  md_declarations : library_segment;
  md_deps : (string * Digest.t * bool) list }

(* Modules loaded in memory contain the following informations. They are
   kept in the hash table [modules_table]. *)

type module_t = {
  module_name : string;
  module_compiled_env : compiled_env;
  module_declarations : library_segment;
  mutable module_opened : bool;
  mutable module_exported : bool;
  module_deps : (string * Digest.t * bool) list;
  module_digest : Digest.t }

let modules_table =
  (Hashtbl.create 17 : (string, module_t) Hashtbl.t)

let find_module s =
  try
    Hashtbl.find modules_table s
  with Not_found ->
    error ("Unknown module " ^ s)

let module_is_loaded s =
  try let _ = Hashtbl.find modules_table s in true with Not_found -> false

let module_is_opened s =
  (find_module s).module_opened

let vo_magic_number = 0700

let (raw_extern_module, raw_intern_module) =
  System.raw_extern_intern vo_magic_number ".vo"

let segment_iter f =
  let rec apply = function
    | _,Leaf obj -> f obj
    | _,ClosedSection (_,_,mseg) -> iter mseg
    | _,OpenedSection _ -> assert false
    | _,FrozenState _ -> ()
  and iter seg =
    List.iter apply seg
  in
  iter


(* [open_module s] opens a module which is assumed to be already loaded. *)

let open_module s =
  let m = find_module s in
  if not m.module_opened then begin
    segment_iter open_object m.module_declarations;
    m.module_opened <- true
  end


(* [load_module s] loads the module [s] from the disk, and [find_module s]
   returns the module of name [s], loading it if necessary. 
   The boolean [doexp] specifies if we open the modules which are declared
   exported in the dependencies (usually it is [true] at the highest level;
   it is always [false] in recursive loadings). *)

let load_objects s =
  let m = find_module s in
  segment_iter load_object m.module_declarations

let rec load_module_from doexp s f =
  let (fname,ch) = raw_intern_module f in
  let md = input_value ch in
  let digest = input_value ch in
  close_in ch;
  let m = { module_name = md.md_name;
	    module_compiled_env = md.md_compiled_env;
	    module_declarations = md.md_declarations;
	    module_opened = false;
	    module_exported = false;
	    module_deps = md.md_deps;
	    module_digest = digest } in
  if s <> md.md_name then
    error ("The file " ^ fname ^ " does not contain module " ^ s);
  List.iter (load_mandatory_module doexp s) m.module_deps;
  Hashtbl.add modules_table s m;
  m

and load_mandatory_module doexp caller (s,d,export) =
  let m = find_module false s s in
  if d <> m.module_digest then
    error ("module "^caller^" makes inconsistent assumptions over module "^s);
  if doexp && export then open_module s

and find_module doexp s f =
  try Hashtbl.find modules_table s with Not_found -> load_module_from doexp s f


let load_module s = function
  | None -> let _ = load_module_from true s s in ()
  | Some f -> let _ = load_module_from true s f in ()


(* [require_module] loads and opens a module. *)

let require_module spec name fileopt export =
  let file = match fileopt with
    | None -> name
    | Some f -> f in
  let m = load_module_from true name file in
  open_module name;
  if export then m.module_exported <- true


(* [save_module s] saves the module [m] to the disk. *)

let current_imports () =
  let l = ref [] in
  Hashtbl.iter 
    (fun _ m -> l := (m.module_name, m.module_digest, m.module_exported) :: !l)
    modules_table;
  !l

let save_module_to s f =
  let seg = contents_after None in
  let md = { 
    md_name = s;
    md_compiled_env = Global.export s;
    md_declarations = seg;
    md_deps = current_imports () } in
  let (_,ch) = raw_extern_module f in
  output_value ch md;
  flush ch;
  let di = Digest.file f in
  output_value ch di;
  close_out ch


