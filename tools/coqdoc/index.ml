(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Printf
open Common

type loc = int

type entry_type =
  | Library
  | Module
  | Definition
  | Inductive
  | Constructor
  | Lemma
  | Record
  | Projection
  | Instance
  | Class
  | Method
  | Variable
  | Axiom
  | TacticDefinition
  | Abbreviation
  | Notation
  | Section
  | Binder

type index_entry =
  | Def of (string * entry_type) list
  | Ref of coq_module * string * entry_type

let current_library = ref ""
  (** refers to the file being parsed *)

(** [deftable] stores only definitions and is used to build the index *)
let deftable = Hashtbl.create 97

(** [byidtable] is used to interpolate idents inside comments, which are not
    globalized otherwise. *)
let byidtable = Hashtbl.create 97

(** [reftable] stores references and definitions *)
let reftable = Hashtbl.create 97

let full_ident sp id =
  if sp <> "<>" then
    if id <> "<>" then
      sp ^ "." ^ id
    else sp
  else if id <> "<>"
  then id
  else ""
let hashtbl_append_def t k v =
  try
    match Hashtbl.find t k with
    | Def l -> Hashtbl.replace t k (Def (l @ [v]))
    | Ref _ -> Hashtbl.add t k (Def [v])
  with Not_found ->
    Hashtbl.add t k (Def [v])

let add_def loc1 loc2 ty sp id =
  let fullid = full_ident sp id in
  let def = (fullid, ty) in
  for loc = loc1 to loc2 do
    hashtbl_append_def reftable (!current_library, loc) def
  done;
  Hashtbl.add deftable !current_library (fullid, ty);
  Hashtbl.add byidtable id (!current_library, fullid, ty)

let add_ref m loc m' sp id ty =
  let fullid = full_ident sp id in
  if Hashtbl.mem reftable (m, loc) then ()
  else Hashtbl.add reftable (m, loc) (Ref (m', fullid, ty));
  let idx = if id = "<>" then m' else id in
    if Hashtbl.mem byidtable idx then ()
    else Hashtbl.add byidtable idx (m', fullid, ty)

let find m l = Hashtbl.find reftable (m, l)

let find_string s = let (m,s,t) = Hashtbl.find byidtable s in Ref (m,s,t)

(* Coq modules *)
let split_sp s =
  try
    let i = String.rindex s '.' in
      String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1)
  with
      Not_found -> "", s

let modules = Hashtbl.create 97
let local_modules = Hashtbl.create 97

let add_module m =
  let _,id = split_sp m in
  Hashtbl.add modules id m;
  Hashtbl.add local_modules m ()

type module_kind = Local | External of string | Unknown

let external_libraries = ref []

let add_external_library logicalpath url =
  external_libraries := (logicalpath,url) :: !external_libraries

let find_external_library logicalpath =
  let rec aux = function
    | [] -> raise Not_found
    | (l,u)::rest ->
        if String.length logicalpath > String.length l &&
          String.sub logicalpath 0 (String.length l + 1) = l ^"."
        then u
        else aux rest
  in aux !external_libraries

let init_coqlib_library () = add_external_library "Stdlib" !prefs.coqlib_url

let find_module m =
  if Hashtbl.mem local_modules m then
    Local
  else
    try External (find_external_library m ^ "/" ^ m)
    with Not_found -> Unknown


(* Building indexes *)

type 'a index = {
  idx_name : string;
  idx_entries : (char * (string * 'a) list) list;
  idx_size : int }

let map f i =
  { i with idx_entries =
      List.map
        (fun (c,l) -> (c, List.map (fun (s,x) -> (s,f s x)) l))
        i.idx_entries }

let compare_entries (s1,_) (s2,_) = Alpha.compare_string s1 s2

let sort_entries el =
  let t = Hashtbl.create 97 in
  List.iter
    (fun c -> Hashtbl.add t c [])
    ['A'; 'B'; 'C'; 'D'; 'E'; 'F'; 'G'; 'H'; 'I'; 'J'; 'K'; 'L'; 'M'; 'N';
     'O'; 'P'; 'Q'; 'R'; 'S'; 'T'; 'U'; 'V'; 'W'; 'X'; 'Y'; 'Z'; '_'; '*'];
  List.iter
    (fun ((s,_) as e) ->
      let c = Alpha.norm_char s.[0] in
      let c,l =
        try c,Hashtbl.find t c with Not_found -> '*',Hashtbl.find t '*' in
      Hashtbl.replace t c (e :: l))
    el;
  let res = ref [] in
  Hashtbl.iter (fun c l -> res := (c, List.sort compare_entries l) :: !res) t;
  List.sort (fun (c1,_) (c2,_) -> Alpha.compare_char c1 c2) !res

let display_letter c = if c = '*' then "other" else String.make 1 c

let type_name = function
  | Library ->
      let ln = !prefs.lib_name in
        if ln <> "" then String.lowercase_ascii ln else "library"
  | Module -> "module"
  | Definition -> "definition"
  | Inductive -> "inductive"
  | Constructor -> "constructor"
  | Lemma -> "lemma"
  | Record -> "record"
  | Projection -> "projection"
  | Instance -> "instance"
  | Class -> "class"
  | Method -> "method"
  | Variable -> "variable"
  | Axiom -> "axiom"
  | TacticDefinition -> "tactic"
  | Abbreviation -> "abbreviation"
  | Notation -> "notation"
  | Section -> "section"
  | Binder -> "binder"

let prepare_entry s = function
  | Notation ->
      (* We decode the encoding done in Dumpglob.cook_notation of coqtop *)
      (* Encoded notations have the form section:entry:sc:x_'++'_x       *)
      (* where:                                                          *)
      (* - the section, if any, ends with a "."                          *)
      (* - the scope can be empty                                        *)
      (* - tokens are separated with "_"                                 *)
      (* - non-terminal symbols are conventionally represented by "x"    *)
      (* - terminals are enclosed within simple quotes                   *)
      (* - existing simple quotes (that necessarily are parts of         *)
      (*   terminals) are doubled                                        *)
      (*   (as a consequence, when a terminal contains "_" or "x", these *)
      (*   necessarily appear enclosed within non-doubled simple quotes) *)
      (* - non-printable characters < 32 are left encoded so that they   *)
      (*   are human-readable in index files                             *)
      (* Example: "x ' %x _% y %'x %'_' z" is encoded as                 *)
      (*   "x_''''_'%x'_'_%'_x_'%''x'_'%''_'''_x"                        *)
      let err () = eprintf "Invalid notation in globalization file\n"; exit 1 in
      let h = try String.index_from s 0 ':' with _ -> err () in
      let i = try String.index_from s (h+1) ':' with _ -> err () in
      let m = try String.index_from s (i+1) ':' with _ -> err () in
      let entry = String.sub s (h+1) (i-h-1) in
      let sc = String.sub s (i+1) (m-i-1) in
      let ntn = Bytes.make (String.length s - m) ' ' in
      let k = ref 0 in
      let j = ref (m+1) in
      let quoted = ref false in
      let l = String.length s - 1 in
      while !j <= l do
        if not !quoted then begin
          (match s.[!j] with
          | '_' -> Bytes.set ntn !k ' '; incr k
          | 'x' -> Bytes.set ntn !k '_'; incr k
          | '\'' -> quoted := true
          | _ -> assert false)
        end
        else
          if s.[!j] = '\'' then
            if (!j = l || s.[!j+1] = '_') then quoted := false
            else (incr j; Bytes.set ntn !k s.[!j]; incr k)
          else begin
            Bytes.set ntn !k s.[!j];
            incr k
          end;
        incr j
      done;
      let ntn = Bytes.sub_string ntn 0 !k in
      let ntn = if sc = "" then ntn else ntn ^ " (" ^ sc ^ ")" in
      if entry = "" then ntn else entry ^ ":" ^ ntn
  | _ ->
      s

let include_entry = function
| Binder -> !prefs.binder_index
| _ -> true

let all_entries () =
  let gl = ref [] in
  let add_g s m t = gl := (s,(m,t)) :: !gl in
  let bt = Hashtbl.create 11 in
  let add_bt t s m =
    let l = try Hashtbl.find bt t with Not_found -> [] in
      Hashtbl.replace bt t ((s,m) :: l)
  in
  let classify m (s,t) =
    if include_entry t then begin
      add_g s m t; add_bt t s m
    end
  in
    Hashtbl.iter classify deftable;
    Hashtbl.iter (fun id m -> add_g id m Library; add_bt Library id m) modules;
    { idx_name = "global";
      idx_entries = sort_entries !gl;
      idx_size = List.length !gl },
    Hashtbl.fold (fun t e l -> (t, { idx_name = type_name t;
                                     idx_entries = sort_entries e;
                                     idx_size = List.length e }) :: l) bt []
