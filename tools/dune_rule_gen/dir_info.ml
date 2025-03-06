(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

let debug = false

(* Information about a directory containing .v files *)
type 'a t =
  { prefix : string list
  (** prefix of the directory, [] when root *)
  ; children : 'a t list
  (** List of children, this could be scanned lazily *)
  ; modules : 'a list
  (** modules [without the .v suffix] *)
  }

(* Scan a single directory *)
let to_module ~dir ~prefix file =
  let source = Path.make (Filename.concat dir file) in
  let name = Filename.remove_extension file in
  Coq_module.make ~source ~prefix ~name

let scan_dir ~prefix dir =
  let contents = Sys.readdir dir |> Array.to_list in
  let dirs, files = List.partition (fun f -> Filename.concat dir f |> Sys.is_directory) contents in
  let files = List.filter (fun f -> Filename.(check_suffix (concat dir f) ".v")) files in
  let modules = List.map (to_module ~dir ~prefix) files in
  dirs, modules

(* Scan a tree *)
let rec scan_subtree ~base_dir ~prefix children =
  let prefix = prefix @ [children] in
  scan ~prefix (Filename.concat base_dir children)
and scan ~prefix base_dir =
  if debug then
    Format.eprintf "[debug] [scan] Enter: %s @\n%!" base_dir;
  let children, modules = scan_dir ~prefix base_dir in
  let children = List.map (scan_subtree ~base_dir ~prefix) children in
  { prefix; children; modules }

let rec map ~(f : prefix:string list -> 'a -> 'b) di =
  { di with
    children = List.map (map ~f) di.children
  ; modules = List.map (f ~prefix:di.prefix) di.modules
  }

let rec iter ~(f : prefix:string list -> 'a -> unit) di : unit =
  f ~prefix:di.prefix di.modules;
  List.iter (iter ~f) di.children

let rec fold ~(f : prefix:string list -> 'b -> 'a list -> 'b) ~init di =
  let res = List.fold_left (fun init x -> fold ~f ~init x) init di.children in
  f ~prefix:di.prefix res di.modules

let rec coq_modules { modules; children; _ } =
  modules @ List.concat (List.map coq_modules children)

(* let rec fold ~(f : prefix:string list -> 'a -> 'b) di = *)

let rec pp pp_module fmt { prefix; children; modules } =
  let open Format in
  fprintf fmt "@[ { prefix = %a; children = %a; modules = %a }@]"
    (pp_print_list pp_print_string) prefix
    (pp_print_list (pp pp_module)) children
    (pp_print_list pp_module) modules

let pp = pp Coq_module.pp
