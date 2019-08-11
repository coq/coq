(** Gather and combine statistics across coqc runs

See description in dev/doc/statistics.md *)

let stats_enabled = ref false
let stats_dir = ref ""
let infiles = ref []


(*** statistics gathering callbacks and data structures ***)
(* modify this section to handle new statistics *)

(* production id *)
type pid = {
  file : string;
  char : int;
}

let pid_compare pid1 pid2 =
  let scmp = String.compare pid1.file pid2.file in
  if scmp <> 0 then scmp else compare pid1.char pid2.char

module PidOrd = struct type t = pid let compare = pid_compare end
module ProdMap = Map.Make(PidOrd)
module StringMap = Map.Make(String)

let prod_cnt_map = ref ProdMap.empty (* counters *)

let add_prod_count key n map =
  let count = try ProdMap.find key map with Not_found -> 0 in
  ProdMap.add key (count+n) map

(* callback for parser actions in GRAMMAR EXTEND *)
let parser_action file char =
  if !stats_enabled then
    prod_cnt_map := add_prod_count { file; char } 1 !prod_cnt_map

type extid = {
  plugin : string;
  etype : string;  (* use defined const *)
  ename : string;
  num : int;
}

let extid_compare extid1 extid2 =
  let scmp = String.compare extid1.plugin extid2.plugin in
  if scmp <> 0 then scmp else begin
    let scmp = String.compare extid1.etype extid2.etype in
    if scmp <> 0 then scmp else begin
      let scmp = String.compare extid1.ename extid2.ename in
      if scmp <> 0 then scmp else compare extid1.num extid2.num
    end
  end

module ExtOrd = struct type t = extid let compare = extid_compare end
module ExtMap = Map.Make(ExtOrd)

let ext_cnt_map = ref ExtMap.empty

let add_ext_count key n map =
  let count = try ExtMap.find key map with Not_found -> 0 in
  ExtMap.add key (count+n) map

(* callback for parser actions in GRAMMAR EXTEND *)
let parser_ext plugin etype ename num =
  if !stats_enabled then
    ext_cnt_map := add_ext_count { plugin; etype; ename; num } 1 !ext_cnt_map


type stats = {
  prod_cnt_map : int ProdMap.t;
  ext_cnt_map : int ExtMap.t;
}

let marshal outch =
  Marshal.to_channel outch { prod_cnt_map = (!prod_cnt_map); ext_cnt_map = (!ext_cnt_map) } []

let unmarshal inch =
  (Marshal.from_channel inch : stats)

let read_parser_stats_file file =
  let inch = open_in_bin file in
  let stats = unmarshal inch in
  close_in inch;
  stats

let combine_parser_stats_file file =
  let stats = read_parser_stats_file file in
  prod_cnt_map := ProdMap.fold (fun key c cnt_map -> add_prod_count key c cnt_map)
    stats.prod_cnt_map !prod_cnt_map;
  ext_cnt_map := ExtMap.fold (fun key c cnt_map -> add_ext_count key c cnt_map)
    stats.ext_cnt_map !ext_cnt_map

(* main routine for "print_stats" command for printing results after the run *)
let print_stats ()  =
  Printexc.record_backtrace true;
  let print_zeros = true in
  let dir s = "doc/tools/docgram/" ^ s in  (* todo: should share path with doc_grammar.ml *)
  let inch = open_in_bin (dir "prodmap") in
  let prod_map = (Marshal.from_channel inch : string ProdMap.t) in
  let ext_map = (Marshal.from_channel inch : pid ExtMap.t) in
  let numfiles = List.fold_left (fun n file ->
      try
        combine_parser_stats_file file; n+1
      with
      | Failure fail -> Printf.eprintf "Failure '%s' reading %s (skipped)\n" fail file; n
      | Sys_error err -> Printf.eprintf "Sys_error '%s' reading %s (skipped)\n" err file; n
      | End_of_file -> Printf.eprintf "End of file reading %s (skipped)\n" file; n)
    0 (List.tl (Array.to_list Sys.argv)) in
  if numfiles > 0 then begin
    ExtMap.iter (fun k c ->
        try
          prod_cnt_map := add_prod_count (ExtMap.find k ext_map) c !prod_cnt_map
        with Not_found -> Printf.eprintf "Can't find extension key '%s' %s %s %d\n" k.plugin k.etype k.ename k.num)
      !ext_cnt_map;
    close_in inch;
    let rev_map = ProdMap.fold (fun l p rmap -> StringMap.add p l rmap) prod_map StringMap.empty in
    StringMap.iter (fun p l ->
        let c = try ProdMap.find l !prod_cnt_map with Not_found -> 0 in
        if c > 0 || print_zeros then Printf.printf "%7d  %s\n" c p)
      rev_map
  end


(*** common stats infrastructure ***)

(* reads and combines any "*.stats" files in COQ_STATS_DIR, writes a new file.
 Called when coqc exits *)
let save_parser_stats combine () =
  (* include any other existing files *)
  let inDir = Filename.concat !stats_dir in
  let files = Sys.readdir !stats_dir in
  let stats_regexp = Str.regexp ".*\\.v\\.stats$" in
  Array.iter (fun file ->
      if Str.string_match stats_regexp file 0 then begin
        try
          let temp_name = inDir (file ^ (string_of_int (Unix.getpid ()))) in
          Sys.rename (inDir file) temp_name;  (* assume this is atomic *)
          combine temp_name;
          Sys.remove temp_name
        with Sys_error _ -> ()  (* another process grabbed the file *)
      end)
    files;

  let base_name =
    match !infiles with
    | f :: tl -> f
    | [] -> "??.v" in
  let file = Str.global_replace (Str.regexp_string "/") "_" base_name ^ ".stats" in
  let temp_file = inDir (file ^ ".temp") in
  let outch = open_out_bin temp_file in
  marshal outch;
  close_out outch;
  Sys.rename temp_file (inDir file)


(* check whether stats are enabled *)
let get_stats_enabled () = !stats_enabled

(* initialize statistics *)
let init () =
  stats_dir := (try Sys.getenv "COQ_STATS_DIR" with Not_found -> "");
  stats_enabled := !stats_dir <> "";
  if get_stats_enabled () then
    at_exit (save_parser_stats combine_parser_stats_file)

(* called to pass input filenames from coqc command-line parameters *)
let set_infiles files =
  infiles := files
