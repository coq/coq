(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Printf
open Coqdep_lexer
open Coqdep_common

(** The basic parts of coqdep (i.e. the parts used by [coqdep -boot])
    are now in [Coqdep_common]. The code that remains here concerns
    the other options. Calling this complete coqdep with the [-boot]
    option should be equivalent to calling [coqdep_boot].
*)

let option_D = ref false
let option_w = ref false
let option_sort = ref false
let option_dump = ref None

let warning_mult suf iter =
  let tab = Hashtbl.create 151 in
  let check f d =
    begin try
      let d' = Hashtbl.find tab f in
      if (Filename.dirname (file_name f d))
        <> (Filename.dirname (file_name f d')) then begin
	  eprintf "*** Warning : the file %s is defined twice!\n" (f ^ suf);
	  flush stderr
	end
    with Not_found -> () end;
    Hashtbl.add tab f d
  in
  iter check

let add_coqlib_known recur phys_dir log_dir f =
  match get_extension f [".vo"] with
    | (basename,".vo") ->
        let name = log_dir@[basename] in
	let paths = if recur then suffixes name else [name] in
        List.iter (fun f -> Hashtbl.add coqlibKnown f ()) paths
    | _ -> ()

let sort () =
  let seen = Hashtbl.create 97 in
  let rec loop file =
    let file = canonize file in
    if not (Hashtbl.mem seen file) then begin
      Hashtbl.add seen file ();
      let cin = open_in (file ^ ".v") in
      let lb = Lexing.from_channel cin in
      try
	while true do
	  match coq_action lb with
	    | Require sl ->
		List.iter
		  (fun s ->
		    try loop (Hashtbl.find vKnown s)
		    with Not_found -> ())
		sl
	    | RequireString s -> loop s
	    | _ -> ()
	done
      with Fin_fichier ->
	close_in cin;
	printf "%s%s " file !suffixe
    end
  in
  List.iter (fun (name,_) -> loop name) !vAccu

let (dep_tab : (string,string list) Hashtbl.t) = Hashtbl.create 151

let mL_dep_list b f =
  try
    Hashtbl.find dep_tab f
  with Not_found ->
    let deja_vu = ref ([] : string list) in
    try
      let chan = open_in f in
      let buf = Lexing.from_channel chan in
      try
	while true do
	  let (Use_module str) = caml_action buf in
	  if str = b then begin
	    eprintf "*** Warning : in file %s the" f;
	    eprintf " notation %s. is useless !\n" b;
	    flush stderr
	  end else
            if not (List.mem str !deja_vu) then addQueue deja_vu str
      	done; []
      with Fin_fichier -> begin
	close_in chan;
	let rl = List.rev !deja_vu in
      	Hashtbl.add dep_tab f rl;
	rl
      end
    with Sys_error _ -> []

let affiche_Declare f dcl =
  printf "\n*** In file %s: \n" f;
  printf "Declare ML Module";
  List.iter (fun str -> printf " \"%s\"" str) dcl;
  printf ".\n";
  flush stdout

let warning_Declare f dcl =
  eprintf "*** Warning : in file %s, the ML modules" f;
  eprintf " declaration should be\n";
  eprintf "*** Declare ML Module";
  List.iter (fun str -> eprintf " \"%s\"" str) dcl;
  eprintf ".\n";
  flush stderr

let traite_Declare f =
  let decl_list = ref ([] : string list) in
  let rec treat = function
    | s :: ll ->
	let s' = basename_noext s in
	(match search_ml_known s with
	   | Some mldir when not (List.mem s' !decl_list) ->
	       let fullname = file_name s' mldir in
	       let depl = mL_dep_list s (fullname ^ ".ml") in
	       treat depl;
	       decl_list := s :: !decl_list
	   | _ -> ());
	treat ll
    | [] -> ()
  in
    try
      let chan = open_in f in
      let buf = Lexing.from_channel chan in
	begin try
	    while true do
      	      let tok = coq_action buf in
      		(match tok with
		  | Declare sl ->
		      decl_list := [];
		      treat sl;
		      decl_list := List.rev !decl_list;
		      if !option_D then
			affiche_Declare f !decl_list
		      else if !decl_list <> sl then
			warning_Declare f !decl_list
		  | _ -> ())
	    done
	  with Fin_fichier -> () end;
	close_in chan
    with Sys_error _ -> ()

let declare_dependencies () =
  List.iter
    (fun (name,_) ->
       traite_Declare (name^".v");
       flush stdout)
    (List.rev !vAccu)

(** DAGs guaranteed to be transitive reductions *)
module DAG (Node : Set.OrderedType) :
sig
  type node = Node.t
  type t
  val empty : t
  val add_transitive_edge : node -> node -> t -> t
  val iter : (node -> node -> unit) -> t -> unit
end =
struct
  type node = Node.t
  module NSet = Set.Make(Node)
  module NMap = Map.Make(Node)

  (** Associate to a node the set of its neighbours *)
  type _t = NSet.t NMap.t

  (** Optimisation: construct the reverse graph at the same time *)
  type t = { dir : _t; rev : _t; }


  let node_equal x y = Node.compare x y = 0

  let add_edge x y graph =
    let set = try NMap.find x graph with Not_found -> NSet.empty in
    NMap.add x (NSet.add y set) graph

  let remove_edge x y graph =
    let set = try NMap.find x graph with Not_found -> NSet.empty in
    let set = NSet.remove y set in
    if NSet.is_empty set then NMap.remove x graph
    else NMap.add x set graph

  let has_edge x y graph =
    let set = try NMap.find x graph with Not_found -> NSet.empty in
    NSet.mem y set

  let connected x y graph =
    let rec aux rem seen =
      if NSet.is_empty rem then false
      else
        let x = NSet.choose rem in
        if node_equal x y then true
        else
          let rem = NSet.remove x rem in
          if NSet.mem x seen then
            aux rem seen
          else
            let seen = NSet.add x seen in
            let next = try NMap.find x graph with Not_found -> NSet.empty in
            let rem = NSet.union next rem in
            aux rem seen
    in
    aux (NSet.singleton x) NSet.empty

  (** Check whether there is a path from a to b going through the edge
      x -> y. *)
  let connected_through a b x y graph =
    let rec aux rem seen =
      if NMap.is_empty rem then false
      else
        let (n, through) = NMap.choose rem in
        if node_equal n b && through then true
        else
          let rem = NMap.remove n rem in
          let is_seen = try Some (NMap.find n seen) with Not_found -> None in
          match is_seen with
          | None ->
            let seen = NMap.add n through seen in
            let next = try NMap.find n graph with Not_found -> NSet.empty in
            let is_x = node_equal n x in
            let push m accu =
              let through = through || (is_x && node_equal m y) in
              NMap.add m through accu
            in
            let rem = NSet.fold push next rem in
            aux rem seen
          | Some false ->
            (** The path we took encountered x -> y but not the one in seen *)
            if through then aux (NMap.add n true rem) (NMap.add n true seen)
            else aux rem seen
          | Some true -> aux rem seen
    in
    aux (NMap.singleton a false) NMap.empty

  let closure x graph =
    let rec aux rem seen =
      if NSet.is_empty rem then seen
      else
        let x = NSet.choose rem in
        let rem = NSet.remove x rem in
        if NSet.mem x seen then 
          aux rem seen
        else
          let seen = NSet.add x seen in
          let next = try NMap.find x graph with Not_found -> NSet.empty in
          let rem = NSet.union next rem in
          aux rem seen
    in
    aux (NSet.singleton x) NSet.empty

    let empty = { dir = NMap.empty; rev = NMap.empty; }

    (** Online transitive reduction algorithm *)
    let add_transitive_edge x y graph =
      if connected x y graph.dir then graph
      else
        let dir = add_edge x y graph.dir in
        let rev = add_edge y x graph.rev in
        let graph = { dir; rev; } in
        let ancestors = closure x rev in
        let descendents = closure y dir in
        let fold_ancestor a graph =
          let fold_descendent b graph =
            let to_remove = has_edge a b graph.dir in
            let to_remove = to_remove && not (node_equal x a && node_equal y b) in
            let to_remove = to_remove && connected_through a b x y graph.dir in
            if to_remove then
              let dir = remove_edge a b graph.dir in
              let rev = remove_edge b a graph.rev in
              { dir; rev; }
            else graph
          in
          NSet.fold fold_descendent descendents graph
        in
        NSet.fold fold_ancestor ancestors graph

  let iter f graph =
    let iter x set = NSet.iter (fun y -> f x y) set in
    NMap.iter iter graph.dir

end

module Graph =
struct
(** Dumping a dependency graph **)

module DAG = DAG(struct type t = string let compare = compare end)

(** TODO: we should share this code with Coqdep_common *)
let treat_coq_file chan =
  let buf = Lexing.from_channel chan in
  let deja_vu_v = ref ([]: string list list)
  and deja_vu_ml = ref ([] : string list) in
  let mark_v_done acc str =
    let seen = List.mem str !deja_vu_v in
    if not seen then
      let () = addQueue deja_vu_v str in
      try
        let file_str = Hashtbl.find vKnown str in
        (canonize file_str, !suffixe) :: acc
      with Not_found -> acc
    else acc
  in
  let rec loop acc =
    let token = try Some (coq_action buf) with Fin_fichier -> None in
    match token with
    | None -> acc
    | Some action ->
      let acc = match action with
      | Require strl ->
        List.fold_left mark_v_done acc strl
      | RequireString s ->
        let str = Filename.basename s in
        mark_v_done acc [str]
      | Declare sl ->
        let declare suff dir s =
          let base = file_name s dir in
          let opt = if !option_natdynlk then " " ^ base ^ ".cmxs" else "" in
          (escape base, suff ^ opt)
        in
        let decl acc str =
          let s = basename_noext str in
          if not (List.mem s !deja_vu_ml) then
            let () = addQueue deja_vu_ml s in
            match search_mllib_known s with
            | Some mldir -> (declare ".cma" mldir s) :: acc
            | None ->
              match search_ml_known s with
              | Some mldir -> (declare ".cmo" mldir s) :: acc
              | None -> acc
          else acc
        in
        List.fold_left decl acc sl
      | Load str ->
        let str = Filename.basename str in
        let seen = List.mem [str] !deja_vu_v in
        if not seen then
          let () = addQueue deja_vu_v [str] in
          try
            let file_str = Hashtbl.find vKnown [str] in
            (canonize file_str, ".v") :: acc
          with Not_found -> acc
        else acc
      | AddLoadPath _ | AddRecLoadPath _ -> acc (** TODO *)
      in
      loop acc
  in
  loop []

let treat_coq_file f =
  let chan = try Some (open_in f) with Sys_error _ -> None in
  match chan with
  | None -> []
  | Some chan ->
    try
      let ans = treat_coq_file chan in
      let () = close_in chan in
      ans
    with Syntax_error (i, j) -> close_in chan; error_cannot_parse f (i, j)

type graph =
  | Element of string
  | Subgraph of string * graph list

let rec insert_graph name path graphs = match path, graphs with
  | [] , graphs -> (Element name) :: graphs
  | (box :: boxes), (Subgraph (hd, names)) :: tl when hd = box ->
    Subgraph (hd, insert_graph name boxes names) :: tl
  | _, hd :: tl -> hd :: (insert_graph name path tl)
  | (box :: boxes), [] -> [ Subgraph (box, insert_graph name boxes []) ]

let print_graphs chan graph =
  let rec print_aux name = function
  | [] -> name
  | (Element str) :: tl -> fprintf chan "\"%s\";\n" str; print_aux name tl
  | Subgraph (box, names) :: tl ->
    fprintf chan "subgraph cluster%n {\nlabel=\"%s\";\n" name box;
    let name = print_aux (name + 1) names in
    fprintf chan "}\n"; print_aux name tl
  in
  ignore (print_aux 0 graph)

let rec pop_common_prefix = function
  | [Subgraph (_, graphs)] -> pop_common_prefix graphs
  | graphs -> graphs

let split_path = Str.split (Str.regexp "/")

let rec pop_last = function
  | [] -> []
  | [ x ] -> []
  | x :: xs -> x :: pop_last xs

let get_boxes path = pop_last (split_path path)

let insert_raw_graph file =
  insert_graph file (get_boxes file)

let rec get_dependencies name args =
  let vdep  = treat_coq_file (name ^ ".v") in
  let fold (deps, graphs, alseen) (dep, _) =
    let dag = DAG.add_transitive_edge name dep deps in
    if not (List.mem dep alseen) then
      get_dependencies dep (dag, insert_raw_graph dep graphs, dep :: alseen)
    else
      (dag, graphs, alseen)
  in
  List.fold_left fold args vdep

let coq_dependencies_dump chan dumpboxes =
  let (deps, graphs, _) =
    List.fold_left (fun ih (name, _) -> get_dependencies name ih)
    (DAG.empty, List.fold_left (fun ih (file, _) -> insert_raw_graph file ih) [] !vAccu,
    List.map fst !vAccu) !vAccu
  in
  fprintf chan "digraph dependencies {\n"; flush chan;
  if dumpboxes then print_graphs chan (pop_common_prefix graphs)
  else List.iter (fun (name, _) -> fprintf chan "\"%s\"[label=\"%s\"]\n" name (basename_noext name)) !vAccu;
  DAG.iter (fun name dep -> fprintf chan "\"%s\" -> \"%s\"\n" dep name) deps;
  fprintf chan "}\n"

end

let usage () =
  eprintf " usage: coqdep [-w] [-c] [-D] [-I dir] [-R dir coqdir] <filename>+\n";
  eprintf " extra options:\n";
  eprintf "  -coqlib dir : set the coq standard library directory\n";
  eprintf "  -exclude-dir f : skip subdirectories named 'f' during -R search\n";
  eprintf "  -dumpgraph f : print a dot dependency graph in file 'f'\n";
  exit 1

let split_period = Str.split (Str.regexp (Str.quote "."))

let rec parse = function
  | "-c" :: ll -> option_c := true; parse ll
  | "-D" :: ll -> option_D := true; parse ll
  | "-w" :: ll -> option_w := true; parse ll
  | "-boot" :: ll -> option_boot := true; parse ll
  | "-sort" :: ll -> option_sort := true; parse ll
  | ("-noglob" | "-no-glob") :: ll -> option_noglob := true; parse ll
  | "-I" :: r :: "-as" :: ln :: ll -> add_dir add_known r [];
    add_dir add_known r (split_period ln);
    parse ll
  | "-I" :: r :: "-as" :: [] -> usage ()
  | "-I" :: r :: ll -> add_caml_dir r; parse ll
  | "-I" :: [] -> usage ()
  | "-R" :: r :: "-as" :: ln :: ll -> add_rec_dir add_known r (split_period ln); parse ll
  | "-R" :: r :: "-as" :: [] -> usage ()
  | "-R" :: r :: ln :: ll -> add_rec_dir add_known r (split_period ln); parse ll
  | "-Q" :: r :: ln :: ll -> add_dir add_known r (split_period ln); parse ll
  | "-R" :: ([] | [_]) -> usage ()
  | "-dumpgraph" :: f :: ll -> option_dump := Some (false, f); parse ll
  | "-dumpgraphbox" :: f :: ll -> option_dump := Some (true, f); parse ll
  | "-exclude-dir" :: r :: ll -> norec_dirnames := r::!norec_dirnames; parse ll
  | "-exclude-dir" :: [] -> usage ()
  | "-coqlib" :: r :: ll -> Flags.coqlib_spec := true; Flags.coqlib := r; parse ll
  | "-coqlib" :: [] -> usage ()
  | "-suffix" :: s :: ll -> suffixe := s ; parse ll
  | "-suffix" :: [] -> usage ()
  | "-slash" :: ll ->
    Printf.eprintf "warning: option -slash has no effect and is deprecated.\n";
    parse ll
  | ("-h"|"--help"|"-help") :: _ -> usage ()
  | f :: ll -> treat_file None f; parse ll
  | [] -> ()

let coqdep () =
  if Array.length Sys.argv < 2 then usage ();
  parse (List.tl (Array.to_list Sys.argv));
  if not Coq_config.has_natdynlink then option_natdynlk := false;
  (* NOTE: These directories are searched from last to first *)
  if !option_boot then begin
    add_rec_dir add_known "theories" ["Coq"];
    add_rec_dir add_known "plugins" ["Coq"];
    add_rec_dir (fun _ -> add_caml_known) "theories" ["Coq"];
    add_rec_dir (fun _ -> add_caml_known) "plugins" ["Coq"];
  end else begin
    Envars.set_coqlib ~fail:Errors.error;
    let coqlib = Envars.coqlib () in
    add_rec_dir add_coqlib_known (coqlib//"theories") ["Coq"];
    add_rec_dir add_coqlib_known (coqlib//"plugins") ["Coq"];
    let user = coqlib//"user-contrib" in
    if Sys.file_exists user then add_dir add_coqlib_known user [];
    List.iter (fun s -> add_dir add_coqlib_known s [])
      (Envars.xdg_dirs (fun x -> Pp.msg_warning (Pp.str x)));
    List.iter (fun s -> add_dir add_coqlib_known s []) Envars.coqpath;
  end;
  List.iter (fun (f,d) -> add_mli_known f d ".mli") !mliAccu;
  List.iter (fun (f,d) -> add_mllib_known f d ".mllib") !mllibAccu;
  List.iter (fun (f,suff,d) -> add_ml_known f d suff) !mlAccu;
  warning_mult ".mli" iter_mli_known;
  warning_mult ".ml" iter_ml_known;
  if !option_sort then begin sort (); exit 0 end;
  if !option_c && not !option_D then mL_dependencies ();
  if not !option_D then coq_dependencies ();
  if !option_w || !option_D then declare_dependencies ();
  begin match !option_dump with
  | None -> ()
  | Some (box, file) ->
    let chan = open_out file in
    try Graph.coq_dependencies_dump chan box; close_out chan
    with e -> close_out chan; raise e
  end

let _ =
  try
    coqdep ()
  with Errors.UserError(s,p) ->
    let pp = if s <> "_" then Pp.(str s ++ str ": " ++ p) else p in
    Pp.msgerrnl pp
