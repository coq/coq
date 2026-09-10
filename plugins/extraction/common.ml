(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open ModPath
open Namegen
open Nameops
open Table
open Miniml
open Mlutil

let ascii_of_id id =
  let s = Id.to_string id in
  for i = 0 to String.length s - 2 do
    if s.[i] == '_' && s.[i+1] == '_' then warning_id s
  done;
  Unicode.ascii_of_ident s

let is_mp_bound = function MPbound _ -> true | _ -> false

(*s Some pretty-print utility functions. *)

let pp_par par st = if par then str "(" ++ st ++ str ")" else st

(** [pp_apply] : a head part applied to arguments, possibly with parenthesis *)

let pp_apply st par args = match args with
  | [] -> st
  | _  -> hov 2 (pp_par par (st ++ spc () ++ prlist_with_sep spc identity args))

(** Same as [pp_apply], but with also protection of the head by parenthesis *)

let pp_apply2 st par args =
  let par' = not (List.is_empty args) || par in
  pp_apply (pp_par par' st) par args

let pr_binding = function
  | [] -> mt ()
  | l  -> str " " ++ prlist_with_sep (fun () -> str " ") Id.print l

let pp_tuple_light f = function
  | [] -> mt ()
  | [x] -> f true x
  | l ->
      pp_par true (prlist_with_sep (fun () -> str "," ++ spc ()) (f false) l)

let pp_tuple f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> pp_par true (prlist_with_sep (fun () -> str "," ++ spc ()) f l)

let pp_boxed_tuple f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> pp_par true (hov 0 (prlist_with_sep (fun () -> str "," ++ spc ()) f l))

(** By default, in module Format, you can do horizontal placing of blocks
    even if they include newlines, as long as the number of chars in the
    blocks is less that a line length. To avoid this awkward situation,
    we attach a big virtual size to [fnl] newlines. *)

(* EG: This looks quite suspicious... but beware of bugs *)
(* let fnl () = stras (1000000,"") ++ fnl () *)
let fnl () = fnl ()

let fnl2 () = fnl () ++ fnl ()

let space_if = function true -> str " " | false -> mt ()

let begins_with s prefix =
  let len = String.length prefix in
  String.length s >= len && String.equal (String.sub s 0 len) prefix

let begins_with_CoqXX s =
  let n = String.length s in
  n >= 4 && s.[0] == 'C' && s.[1] == 'o' && s.[2] == 'q' &&
  let i = ref 3 in
  try while !i < n do
    match s.[!i] with
    | '_' -> i:=n (*Stop*)
    | '0'..'9' -> incr i
    | _ -> raise Not_found
  done; true
  with Not_found -> false

let unquote s =
  if lang () != Scheme then s
  else String.map (fun c -> if c == '\'' then '~' else c) s

let rec qualify delim = function
  | [] -> assert false
  | [s] -> s
  | ""::l -> qualify delim l
  | s::l -> s^delim^(qualify delim l)

let dottify = qualify "."
let pseudo_qualify = qualify "__"

(*s Uppercase/lowercase renamings. *)

let is_upper s = match s.[0] with 'A' .. 'Z' -> true | _ -> false
let is_lower s = match s.[0] with 'a' .. 'z' | '_' -> true | _ -> false

let lowercase_prefix () = String.uncapitalize_ascii (Table.prefix ())
let uppercase_prefix () = Table.prefix ()

let lowercase_id id = Id.of_string (String.uncapitalize_ascii (ascii_of_id id))
let uppercase_id id =
  let s = ascii_of_id id in
  assert (not (String.is_empty s));
  if s.[0] == '_' then Id.of_string (uppercase_prefix ()^"_"^s)
  else Id.of_string (String.capitalize_ascii s)

type kind = Term | Type | Cons | Mod

module KOrd =
struct
  type t = kind * string
  let compare (k1, s1) (k2, s2) =
    let c = Stdlib.compare k1 k2 (* OK *) in
    if c = 0 then String.compare s1 s2
    else c
end

module KMap = CMap.Make(KOrd)

let upperkind = function
  | Type -> lang () == Haskell
  | Term -> false
  | Cons | Mod -> true

let kindcase_id k id =
  if upperkind k then uppercase_id id else lowercase_id id

(*s de Bruijn environments for programs *)

type env = Id.t list * Id.Set.t

(*s Generic renaming issues for local variable names. *)

let rec rename_id id avoid =
  if Id.Set.mem id avoid then rename_id (increment_subscript id) avoid else id

let rec rename_vars avoid = function
  | [] ->
      [], avoid
  | id :: idl when id == dummy_name ->
      (* we don't rename dummy binders *)
      let (idl', avoid') = rename_vars avoid idl in
      (id :: idl', avoid')
  | id :: idl ->
      let (idl, avoid) = rename_vars avoid idl in
      let id = rename_id (lowercase_id id) avoid in
      (id :: idl, Id.Set.add id avoid)

let rename_tvars avoid l =
  let rec rename avoid = function
    | [] -> [],avoid
    | id :: idl ->
        let id = rename_id (lowercase_id id) avoid in
        let idl, avoid = rename (Id.Set.add id avoid) idl in
        (id :: idl, avoid) in
  fst (rename avoid l)

let push_vars ids (db,avoid) =
  let ids',avoid' = rename_vars avoid ids in
  ids', (ids' @ db, avoid')

let get_db_name n (db,_) = List.nth db (pred n)

type phase = Pre | Impl | Intf

module DupOrd =
struct
  type t = ModPath.t * Id.t
  let compare (mp1, l1) (mp2, l2) =
    let c = Id.compare l1 l2 in
    if Int.equal c 0 then ModPath.compare mp1 mp2 else c
end

module DupMap = CMap.Make(DupOrd)

(* We might have built [global_reference] whose canonical part is
   inaccurate. We must hence compare only the user part,
   hence using a Hashtbl might be incorrect *)

(*s table indicating the visible horizon at a precise moment,
    i.e. the stack of structures we are inside.

  - The sequence of [mp] parts should have the following form:
  a [MPfile] at the beginning, and then more and more [MPdot]
  over this [MPfile], or [MPbound] when inside the type of a
  module parameter.

  - the [params] are the [MPbound] when [mp] is a functor,
    the innermost [MPbound] coming first in the list.

  - The [content] part is used to record all the names already
  seen at this level.
*)

type visible_layer = { mp : ModPath.t;
                       params : MBId.t list;
                       content : Id.t KMap.t; }

module State =
struct

type state = {
  global_ids : Id.Set.t;
  mod_index : int Id.Map.t;
  ref_renaming : string list Refmap'.t;
  mp_renaming : string list ModPath.Map.t;
  params_ren : MBId.Set.t; (* List of module parameters that we should alpha-rename *)
  duplicates : int * string DupMap.t; (* table of local module wrappers used to provide non-ambiguous names *)
}

type modular = {
  mutable mpfiles : DirPath.Set.t; (* List of external modules that will be opened initially *)
  mutable mpfiles_content : Id.t KMap.t DirPath.Map.t; (* table recording objects in the first level of all MPfile *)
}

let empty_modular () = {
  mpfiles = DirPath.Set.empty;
  mpfiles_content = DirPath.Map.empty;
}

type t = {
  table : Table.t;
  state : state ref;
  visibility : visible_layer ref list;
  modular : modular option;
  (* fields below are read-only *)
  library : bool;
  (*s Extraction modes: modular or monolithic, library or minimal ?

  Nota:
  - Recursive Extraction : monolithic, minimal
  - Separate Extraction : modular, minimal
  - Extraction Library : modular, library
  *)
  keywords : Id.Set.t;
  phase : phase;
}

let make_state kw = {
  global_ids = kw;
  mod_index = Id.Map.empty;
  ref_renaming = Refmap'.empty;
  mp_renaming = ModPath.Map.empty;
  params_ren = MBId.Set.empty;
  duplicates = (0, DupMap.empty);
}

let make ~modular ~library ~keywords () = {
  table = Table.make_table ();
  state = ref (make_state keywords);
  modular = if modular then Some (empty_modular ()) else None;
  library;
  keywords;
  phase = Impl;
  visibility = [];
}

let get_table s = s.table

let get_modular s = match s.modular with
| None -> false
| Some _ -> true

let get_modular_state s = s.modular

let get_library s = s.library

let get_keywords s = s.keywords

let get_phase s = s.phase

let set_phase s phase = { s with phase }

(* Reader-like *)

let with_visibility s mp mps k =
  let v = ref { mp = mp; params = mps; content = KMap.empty } in
  let ans = k { s with visibility = v :: s.visibility } in
  (* we save the 1st-level-content of MPfile for later use *)
  let () =
    if s.phase == Impl then match mp, s.modular with
    | MPfile dp, Some mdl ->
      mdl.mpfiles_content <- DirPath.Map.add dp !v.content mdl.mpfiles_content
    | (MPbound _ | MPdot _ | MPfile _), (None | Some _) -> ()
  in
  ans

let add_visible s ks l = match s.visibility with
| [] -> assert false
| v :: r -> v := { !v with content = KMap.add ks l !v.content }

let get_visible s =
  List.map (!) s.visibility

let get_visible_mps s =
  List.map (function v -> !v.mp) s.visibility

let get_top_visible_mp s = match s.visibility with
| [] -> assert false
| v :: _ -> !v.mp

(* Mutable primitives *)

let add_global_ids s id =
  let state = s.state.contents in
  s.state := { state with global_ids = Id.Set.add id state.global_ids }

let get_global_ids s =
  s.state.contents.global_ids

let add_mod_index s id i =
  let state = s.state.contents in
  s.state := { state with mod_index = Id.Map.add id i state.mod_index }

let get_mod_index s id =
  Id.Map.find id s.state.contents.mod_index

let add_ref_renaming s r l =
  let state = s.state.contents in
  s.state := { state with ref_renaming = Refmap'.add r l state.ref_renaming }

let get_ref_renaming s r =
  Refmap'.find r s.state.contents.ref_renaming

let get_mp_renaming s mp =
  ModPath.Map.find_opt mp s.state.contents.mp_renaming

let add_mp_renaming s mp l =
  let state = s.state.contents in
  s.state := { state with mp_renaming = ModPath.Map.add mp l state.mp_renaming }

let add_params_ren s mp =
  let state = s.state.contents in
  s.state := { state with params_ren = MBId.Set.add mp state.params_ren }

let mem_params_ren s mp =
  MBId.Set.mem mp s.state.contents.params_ren

let get_mpfiles s =
  s.mpfiles

let add_mpfiles s mp =
  s.mpfiles <- DirPath.Set.add mp s.mpfiles

let clear_mpfiles s =
  s.mpfiles <- DirPath.Set.empty

let add_duplicate s mp l =
  let state = s.state.contents in
  let (index, dups) = state.duplicates in
  let ren = uppercase_prefix () ^ "__" ^ string_of_int (index + 1) in
  let dups = DupMap.add (mp, l) ren dups in
  s.state := { state with duplicates = (index + 1, dups) }

let get_duplicate s mp l =
  DupMap.find_opt (mp, l) (snd s.state.contents.duplicates)

let get_mpfiles_content mdl mp = DirPath.Map.find mp mdl.mpfiles_content

(* Reset *)

let reset s =
  let () = assert (List.is_empty s.visibility) in
  let state = {
    global_ids = s.keywords;
    mod_index = Id.Map.empty;
    ref_renaming = Refmap'.empty;
    mp_renaming = ModPath.Map.empty;
    params_ren = MBId.Set.empty;
    duplicates = (0, DupMap.empty);
  } in
  (* don't reset modular files content *)
  let () = match s.modular with
  | None -> ()
  | Some mdl -> mdl.mpfiles <- DirPath.Set.empty
  in
  s.state := state

end

(*S Renamings of global objects. *)

(*s Tables of global renamings *)

let empty_env state () = [], State.get_global_ids state

let get_mpfiles_content s mp =
  try State.get_mpfiles_content s mp
  with Not_found -> failwith "get_mpfiles_content"

(*S Renaming functions *)

(* This function creates from [id] a correct uppercase/lowercase identifier.
   This is done by adding a [Rocq_] or [rocq_] prefix. To avoid potential clashes
   with previous [Rocq_id] variable, these prefixes are duplicated if already
   existing. *)

let modular_rename table k id =
  let s = ascii_of_id id in
  let prefix,is_ok =
    if upperkind k then uppercase_prefix () ^ "_",is_upper
    else lowercase_prefix () ^ "_",is_lower
  in
  if not (is_ok s) || Id.Set.mem id (State.get_keywords table) || begins_with s prefix
  then prefix ^ s
  else s

(*s For monolithic extraction, first-level modules might have to be renamed
    with unique numbers *)

let modfstlev_rename table id =
  try
    let n = State.get_mod_index table id in
    let () = State.add_mod_index table id (n+1) in
    let s = if n == 0 then "" else string_of_int (n-1) in
    uppercase_prefix ()^s^"_"^(ascii_of_id id)
  with Not_found ->
    let s = ascii_of_id id in
    if is_lower s || begins_with_CoqXX s then
      let () = State.add_mod_index table id 1 in
      uppercase_prefix () ^ "_" ^ s
    else
      let () = State.add_mod_index table id 0 in
      s

(*s Creating renaming for a [module_path] : first, the real function ... *)

let rec mp_renaming_fun table mp = match mp with
  | _ when not (State.get_modular table) && at_toplevel mp -> [""]
  | MPdot (mp,l) ->
      let lmp = mp_renaming table mp in
      let mp = match lmp with
      | [""] -> modfstlev_rename table l
      | _ -> modular_rename table Mod l
      in
      mp ::lmp
  | MPbound mbid ->
      let s = modular_rename table Mod (MBId.to_id mbid) in
      if not (State.mem_params_ren table mbid) then [s]
      else let i,_,_ = MBId.repr mbid in [s^"__"^string_of_int i]
  | MPfile f ->
      let mdl = match State.get_modular_state table with
      | None -> assert false (* see [at_toplevel] above *)
      | Some mdl -> mdl
      in
      let () = assert (State.get_phase table == Pre) in
      let current_mpfile = (List.last (State.get_visible table)).mp in
      let () = if not (ModPath.equal mp current_mpfile) then State.add_mpfiles mdl f in
      [string_of_modfile (State.get_table table) f]

(* ... and its version using a cache *)

and mp_renaming table x =
  if is_mp_bound (base_mp x) then mp_renaming_fun table x
  else match State.get_mp_renaming table x with
  | Some v -> v
  | None ->
    let ans = mp_renaming_fun table x in
    let () = State.add_mp_renaming table x ans in
    ans

(*s Renamings creation for a [global_reference]: we build its fully-qualified
    name in a [string list] form (head is the short name). *)

let ref_renaming_fun table (k,r) =
  let mp = modpath_of_r r in
  let l = mp_renaming table mp in
  let l = if lang () != Ocaml && not (State.get_modular table) then [""] else l in
  let s =
    let idg = safe_basename_of_global (State.get_table table) r in
    let app_suf s = match InfvInst.encode r.inst with
    | None -> s
    | Some suf -> s ^ "__" ^ suf
    in
    match l with
    | [""] -> (* this happens only at toplevel of the monolithic case *)
      let globs = State.get_global_ids table in
      let id = next_ident_away (kindcase_id k idg) globs in
      app_suf (Id.to_string id)
    | _ -> app_suf (modular_rename table k idg)
  in
  let () = State.add_global_ids table (Id.of_string s) in
  s::l

(* Cached version of the last function *)

let ref_renaming table ((k,r) as x) =
  try if is_mp_bound (base_mp (modpath_of_r r)) then raise Not_found; State.get_ref_renaming table r
  with Not_found -> let y = ref_renaming_fun table x in State.add_ref_renaming table r y; y

(* [visible_clash mp0 (k,s)] checks if [mp0-s] of kind [k]
   can be printed as [s] in the current context of visible
   modules. More precisely, we check if there exists a
   visible [mp] that contains [s].
   The verification stops if we encounter [mp=mp0]. *)

let rec clash mem mp0 ks = function
  | [] -> false
  | mp :: _ when ModPath.equal (MPfile mp) mp0 -> false
  | mp :: _ when mem mp ks -> true
  | _ :: mpl -> clash mem mp0 ks mpl

let mpfiles_clash mdl mp0 ks =
  clash (fun mp k -> KMap.mem k (get_mpfiles_content mdl mp)) mp0 ks
    (List.rev (DirPath.Set.elements (State.get_mpfiles mdl)))

let rec params_lookup table mp0 ks = function
  | [] -> false
  | param :: _ when ModPath.equal mp0 (MPbound param) -> true
  | param :: params ->
      let () = match ks with
      | (Mod, mp) when String.equal (List.hd (mp_renaming table (MPbound param))) mp -> State.add_params_ren table param
      | _ -> ()
      in
      params_lookup table mp0 ks params

let visible_clash table mp0 ks =
  let rec clash = function
    | [] -> false
    | v :: _ when ModPath.equal v.mp mp0 -> false
    | v :: vis ->
        let b = KMap.mem ks v.content in
        if b && not (is_mp_bound mp0) then true
        else begin
          let () = if b then match mp0 with
          | MPbound mbid -> State.add_params_ren table mbid
          | MPfile _ | MPdot _ -> assert false
          in
          if params_lookup table mp0 ks v.params then false
          else clash vis
        end
  in clash (State.get_visible table)

(* Same, but with verbose output (and mp0 shouldn't be a MPbound) *)

let visible_clash_dbg table mp0 ks =
  let rec clash = function
    | [] -> None
    | v :: _ when ModPath.equal v.mp mp0 -> None
    | v :: vis ->
        try Some (v.mp,KMap.find ks v.content)
        with Not_found ->
          if params_lookup table mp0 ks v.params then None
          else clash vis
  in clash (State.get_visible table)

(* After the 1st pass, we can decide which modules will be opened initially *)

let opened_libraries table =
  match State.get_modular_state table with
  | None -> DirPath.Set.empty
  | Some mdl ->
    let used_files = DirPath.Set.elements (State.get_mpfiles mdl) in
    let used_ks = List.map (fun dp -> Mod, string_of_modfile (State.get_table table) dp) used_files in
    (* By default, we open all used files. Ambiguities will be resolved later
       by using qualified names. Nonetheless, we don't open any file A that
       contains an immediate submodule A.B hiding another file B : otherwise,
       after such an open, there's no unambiguous way to refer to objects of B. *)
    let to_open =
      List.filter
        (fun dp ->
           not (List.exists (fun k -> KMap.mem k (get_mpfiles_content mdl dp)) used_ks))
        used_files
    in
    let () = State.clear_mpfiles mdl in
    let () = List.iter (fun mp -> State.add_mpfiles mdl mp) to_open in
    State.get_mpfiles mdl

(*s On-the-fly qualification issues for both monolithic or modular extraction. *)

(* [pp_ocaml_gen] below is a function that factorize the printing of both
   [global_reference] and module names for ocaml. When [k=Mod] then [olab=None],
   otherwise it contains the label of the reference to print.
   [rls] is the string list giving the qualified name, short name at the end. *)

(* In Rocq, we can qualify [M.t] even if we are inside [M], but in Ocaml we
   cannot do that. So, if [t] gets hidden and we need a long name for it,
   we duplicate the _definition_ of t in a Coq__XXX module, and similarly
   for a sub-module [M.N] *)

let pp_duplicate table k' prefix mp rls olab =
  let rls', lbl =
    if k' != Mod then
      (* Here rls=[s], the ref to print is <prefix>.<s>, and olab<>None *)
      rls, Option.get olab
    else
      (* Here rls=s::rls', we search the label for s inside mp *)
      List.tl rls, get_nth_label_mp (mp_length mp - mp_length prefix) mp
  in
  match State.get_duplicate table prefix lbl with
  | Some ren -> dottify (ren :: rls')
  | None ->
     assert (State.get_phase table == Pre); (* otherwise it's too late *)
     State.add_duplicate table prefix lbl; dottify rls

let fstlev_ks k = function
  | [] -> assert false
  | [s] -> k,s
  | s::_ -> Mod,s

(* [pp_ocaml_local] : [mp] has something in common with [top_visible ()]
   but isn't equal to it *)

let pp_ocaml_local table k prefix mp rls olab =
  (* what is the largest prefix of [mp] that belongs to [visible]? *)
  assert (k != Mod || not (ModPath.equal mp prefix)); (* mp as whole module isn't in itself *)
  let rls' = List.skipn (mp_length prefix) rls in
  let k's = fstlev_ks k rls' in
  (* Reference r / module path mp is of the form [<prefix>.s.<...>]. *)
  if not (visible_clash table prefix k's) then dottify rls'
  else pp_duplicate table (fst k's) prefix mp rls' olab

(* [pp_ocaml_bound] : [mp] starts with a [MPbound], and we are not inside
   (i.e. we are not printing the type of the module parameter) *)

let pp_ocaml_bound table base rls =
  (* clash with a MPbound will be detected and fixed by renaming this MPbound *)
  if State.get_phase table == Pre then ignore (visible_clash table base (Mod,List.hd rls));
  dottify rls

(* [pp_ocaml_extern] : [mp] isn't local, it is defined in another [MPfile]. *)

let pp_ocaml_extern table k base rls = match rls with
  | [] -> assert false
  | base_s :: rls' ->
      if match State.get_modular_state table with
      | None -> true (* Pseudo qualification with "" *)
      | Some mdl ->
        (List.is_empty rls')  (* Case of a file A.v used as a module later *)
        || (not (match base with MPfile dp -> DirPath.Set.mem dp (State.get_mpfiles mdl) | MPbound _ | MPdot _ -> false)) (* Module not opened *)
        || (mpfiles_clash mdl base (fstlev_ks k rls')) (* Conflict in opened files *)
        || (visible_clash table base (fstlev_ks k rls')) (* Local conflict *)
      then
        (* We need to fully qualify. Last clash situation is unsupported *)
        match visible_clash_dbg table base (Mod,base_s) with
          | None -> dottify rls
          | Some (mp,l) -> error_module_clash base (MPdot (mp,l))
      else
        (* Standard situation : object in an opened file *)
        dottify rls'

(* [pp_ocaml_gen] : choosing between [pp_ocaml_local] or [pp_ocaml_extern] *)

let pp_ocaml_gen table k mp rls olab =
  match common_prefix_from_list mp (State.get_visible_mps table) with
    | Some prefix -> pp_ocaml_local table k prefix mp rls olab
    | None ->
        let base = base_mp mp in
        if is_mp_bound base then pp_ocaml_bound table base rls
        else pp_ocaml_extern table k base rls

(* For Haskell, things are simpler: we have removed (almost) all structures *)

let pp_haskell_gen table k mp rls = match rls with
  | [] -> assert false
  | s::rls' ->
    let str = pseudo_qualify rls' in
    let str = if is_upper str && not (upperkind k) then ("_"^str) else str in
    if ModPath.equal (base_mp mp) (State.get_top_visible_mp table) then str else s^"."^str

(* Main name printing function for a reference *)

let pp_global_with_key table k key r =
  let ls = ref_renaming table (k,r) in
  assert (List.length ls > 1);
  let s = List.hd ls in
  let mp,l = KerName.repr key in
  if ModPath.equal mp (State.get_top_visible_mp table) then
    (* simplest situation: definition of r (or use in the same context) *)
    (* we update the visible environment *)
    let () = State.add_visible table (k, s) l in
    unquote s
  else
    let rls = List.rev ls in (* for what come next it's easier this way *)
    match lang () with
      | Scheme -> unquote s (* no modular Scheme extraction... *)
      | JSON -> dottify (List.map unquote rls)
      | Haskell -> if State.get_modular table then pp_haskell_gen table k mp rls else s
      | Ocaml -> pp_ocaml_gen table k mp rls (Some l)

let pp_global table k r =
  pp_global_with_key table k (repr_of_r r) r

(* Main name printing function for declaring a reference *)

let pp_global_name table k r =
  let ls = ref_renaming table (k,r) in
  assert (List.length ls > 1);
  List.hd ls

(* The next function is used only in Ocaml extraction...*)

let pp_module table mp =
  let ls = mp_renaming table mp in
  match mp with
    | MPdot (mp0,l) when ModPath.equal mp0 (State.get_top_visible_mp table) ->
        (* simplest situation: definition of mp (or use in the same context) *)
        (* we update the visible environment *)
        let s = List.hd ls in
        let () = State.add_visible table (Mod, s) l in
        s
    | _ -> pp_ocaml_gen table Mod mp (List.rev ls) None

(** Special hack for constants of type Ascii.ascii : if an
    [Extract Inductive ascii => char] has been declared, then
    the constants are directly turned into chars *)

let ascii_type_name = "core.ascii.type"
let ascii_constructor_name = "core.ascii.ascii"

let is_ascii_registered () =
  Rocqlib.has_ref ascii_type_name
  && Rocqlib.has_ref ascii_constructor_name

let ascii_type_ref () =
  (* FIXME: support sort poly? *)
  { glob = Rocqlib.lib_ref ascii_type_name; inst = InfvInst.empty }

let check_extract_ascii () =
  try
    let char_type = match lang () with
      | Ocaml -> "char"
      | Haskell -> "Prelude.Char"
      | _ -> raise Not_found
    in
    String.equal (find_custom @@ ascii_type_ref ()) (char_type)
  with Not_found -> false

let is_constructor r = match r.glob with GlobRef.ConstructRef _ -> true | _ -> false

let is_list_cons l =
 List.for_all (function MLcons (_, r, []) -> is_constructor r | _ -> false) l

let is_native_char = function
  | MLcons(_,gr,l) ->
    is_ascii_registered ()
    && Rocqlib.check_ref ascii_constructor_name gr.glob
    && check_extract_ascii ()
    && is_list_cons l
  | _ -> false

let get_constructor r = match r.glob with
| GlobRef.ConstructRef(_, j) -> j
| _ -> assert false

let get_native_char c =
  let rec cumul = function
    | [] -> 0
    | MLcons(_, r, [])::l -> (2 - get_constructor r) + 2 * (cumul l)
    | _ -> assert false
  in
  let l = match c with MLcons(_,_,l) -> l | _ -> assert false in
  Char.chr (cumul l)

let pp_native_char c = str ("'"^Char.escaped (get_native_char c)^"'")

(** Special hack for constants of type String.string : if an
    [Extract Inductive string => string] has been declared, then
    the constants are directly turned into string literals *)

let string_type_name = "core.string.type"
let empty_string_name = "core.string.empty"
let string_constructor_name = "core.string.string"

let is_string_registered () =
  Rocqlib.has_ref string_type_name
  && Rocqlib.has_ref empty_string_name
  && Rocqlib.has_ref string_constructor_name

let string_type_ref () =
  (* FIXME: support sort poly? *)
  { glob = Rocqlib.lib_ref string_type_name; inst = InfvInst.empty }

let check_extract_string () =
  try
    let string_type = match lang () with
      | Ocaml -> "string"
      | Haskell -> "Prelude.String"
      | _ -> raise Not_found
    in
    String.equal (find_custom @@ string_type_ref ()) string_type
  with Not_found -> false

(* The argument is known to be of type Strings.String.string.
   Check that it is built from constructors EmptyString and String
   with constant ascii arguments. *)

let rec is_native_string_rec empty_string_ref string_constructor_ref = function
  (* "EmptyString" constructor *)
  | MLcons(_, gr, []) -> Rocqlib.check_ref empty_string_ref gr.glob
  (* "String" constructor *)
  | MLcons(_, gr, [hd; tl]) ->
      Rocqlib.check_ref string_constructor_ref gr.glob
      && is_native_char hd
      && is_native_string_rec empty_string_ref string_constructor_ref tl
  (* others *)
  | _ -> false

(* Here we first check that the argument is the type registered as
   core.string.type and that extraction to native strings was
   requested.  Then we check every character via
   [is_native_string_rec]. *)

let is_string_constructor = function
| GlobRef.ConstructRef (ind, _) -> Rocqlib.check_ref string_type_name (GlobRef.IndRef ind)
| _ -> false

let is_native_string c =
  match c with
  | MLcons(_, gr, l) ->
      is_string_registered ()
      && is_string_constructor gr.glob
      && check_extract_string ()
      && is_native_string_rec empty_string_name string_constructor_name c
  | _ -> false

(* Extract the underlying string. *)

let get_native_string c =
  let buf = Buffer.create 64 in
  let rec get = function
    (* "EmptyString" constructor *)
    | MLcons(_, gr, []) when Rocqlib.check_ref empty_string_name gr.glob ->
        Buffer.contents buf
    (* "String" constructor *)
    | MLcons(_, gr, [hd; tl]) when Rocqlib.check_ref string_constructor_name gr.glob ->
        Buffer.add_char buf (get_native_char hd);
        get tl
    (* others *)
    | _ -> assert false
  in get c

(* Printing the underlying string. *)

let pp_native_string c =
  str ("\"" ^ String.escaped (get_native_string c) ^ "\"")

(* Registered sig type *)

let sig_type_name = "core.sig.type"
