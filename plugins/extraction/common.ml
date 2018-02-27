(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Libnames
open Globnames
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

[@@@ocaml.warning "-3"]       (* String.(un)capitalize_ascii since 4.03.0 GPR#124 *)
let capitalize = String.capitalize
let uncapitalize = String.uncapitalize
[@@@ocaml.warning "+3"]

let lowercase_id id = Id.of_string (uncapitalize (ascii_of_id id))
let uppercase_id id =
  let s = ascii_of_id id in
  assert (not (String.is_empty s));
  if s.[0] == '_' then Id.of_string ("Coq_"^s)
  else Id.of_string (capitalize s)

type kind = Term | Type | Cons | Mod

module KOrd =
struct
  type t = kind * string
  let compare (k1, s1) (k2, s2) =
    let c = Pervasives.compare k1 k2 (** OK *) in
    if c = 0 then String.compare s1 s2
    else c
end

module KMap = Map.Make(KOrd)

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

(*S Renamings of global objects. *)

(*s Tables of global renamings *)

let register_cleanup, do_cleanup =
  let funs = ref [] in
  (fun f -> funs:=f::!funs), (fun () -> List.iter (fun f -> f ()) !funs)

type phase = Pre | Impl | Intf

let set_phase, get_phase =
  let ph = ref Impl in ((:=) ph), (fun () -> !ph)

let set_keywords, get_keywords =
  let k = ref Id.Set.empty in
  ((:=) k), (fun () -> !k)

let add_global_ids, get_global_ids =
  let ids = ref Id.Set.empty in
  register_cleanup (fun () -> ids := get_keywords ());
  let add s = ids := Id.Set.add s !ids
  and get () = !ids
  in (add,get)

let empty_env () = [], get_global_ids ()

(* We might have built [global_reference] whose canonical part is
   inaccurate. We must hence compare only the user part,
   hence using a Hashtbl might be incorrect *)

let mktable_id autoclean =
  let m = ref Id.Map.empty in
  let clear () = m := Id.Map.empty in
  if autoclean then register_cleanup clear;
  (fun r v -> m := Id.Map.add r v !m), (fun r -> Id.Map.find r !m), clear

let mktable_ref autoclean =
  let m = ref Refmap'.empty in
  let clear () = m := Refmap'.empty in
  if autoclean then register_cleanup clear;
  (fun r v -> m := Refmap'.add r v !m), (fun r -> Refmap'.find r !m), clear

let mktable_modpath autoclean =
  let m = ref MPmap.empty in
  let clear () = m := MPmap.empty in
  if autoclean then register_cleanup clear;
  (fun r v -> m := MPmap.add r v !m), (fun r -> MPmap.find r !m), clear

(* A table recording objects in the first level of all MPfile *)

let add_mpfiles_content,get_mpfiles_content,clear_mpfiles_content =
  mktable_modpath false

let get_mpfiles_content mp =
  try get_mpfiles_content mp
  with Not_found -> failwith "get_mpfiles_content"

(*s The list of external modules that will be opened initially *)

let mpfiles_add, mpfiles_mem, mpfiles_list, mpfiles_clear =
  let m = ref MPset.empty in
  let add mp = m:=MPset.add mp !m
  and mem mp = MPset.mem mp !m
  and list () = MPset.elements !m
  and clear () = m:=MPset.empty
  in
  register_cleanup clear;
  (add,mem,list,clear)

(*s List of module parameters that we should alpha-rename *)

let params_ren_add, params_ren_mem =
  let m = ref MPset.empty in
  let add mp = m:=MPset.add mp !m
  and mem mp = MPset.mem mp !m
  and clear () = m:=MPset.empty
  in
  register_cleanup clear;
  (add,mem)

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
		       params : ModPath.t list;
		       mutable content : Label.t KMap.t; }

let pop_visible, push_visible, get_visible =
  let vis = ref [] in
  register_cleanup (fun () -> vis := []);
  let pop () =
    match !vis with
      | [] -> assert false
      | v :: vl ->
	  vis := vl;
	  (* we save the 1st-level-content of MPfile for later use *)
	  if get_phase () == Impl && modular () && is_modfile v.mp
	  then add_mpfiles_content v.mp v.content
  and push mp mps =
    vis := { mp = mp; params = mps; content = KMap.empty } :: !vis
  and get () = !vis
  in (pop,push,get)

let get_visible_mps () = List.map (function v -> v.mp) (get_visible ())
let top_visible () = match get_visible () with [] -> assert false | v::_ -> v
let top_visible_mp () = (top_visible ()).mp
let add_visible ks l =
  let visible = top_visible () in
  visible.content <- KMap.add ks l visible.content

(* table of local module wrappers used to provide non-ambiguous names *)

module DupOrd =
struct
  type t = ModPath.t * Label.t
  let compare (mp1, l1) (mp2, l2) =
    let c = Label.compare l1 l2 in
    if Int.equal c 0 then ModPath.compare mp1 mp2 else c
end

module DupMap = Map.Make(DupOrd)

let add_duplicate, get_duplicate =
  let index = ref 0 and dups = ref DupMap.empty in
  register_cleanup (fun () -> index := 0; dups := DupMap.empty);
  let add mp l =
     incr index;
     let ren = "Coq__" ^ string_of_int !index in
     dups := DupMap.add (mp,l) ren !dups
  and get mp l =
    try Some (DupMap.find (mp, l) !dups) with Not_found -> None
  in (add,get)

type reset_kind = AllButExternal | Everything

let reset_renaming_tables flag =
  do_cleanup ();
  if flag == Everything then clear_mpfiles_content ()

(*S Renaming functions *)

(* This function creates from [id] a correct uppercase/lowercase identifier.
   This is done by adding a [Coq_] or [coq_] prefix. To avoid potential clashes
   with previous [Coq_id] variable, these prefixes are duplicated if already
   existing. *)

let modular_rename k id =
  let s = ascii_of_id id in
  let prefix,is_ok = if upperkind k then "Coq_",is_upper else "coq_",is_lower
  in
  if not (is_ok s) || Id.Set.mem id (get_keywords ()) || begins_with s prefix
  then prefix ^ s
  else s

(*s For monolithic extraction, first-level modules might have to be renamed
    with unique numbers *)

let modfstlev_rename =
  let add_index,get_index,_ = mktable_id true in
  fun l ->
    let id = Label.to_id l in
    try
      let n = get_index id in
      add_index id (n+1);
      let s = if n == 0 then "" else string_of_int (n-1) in
      "Coq"^s^"_"^(ascii_of_id id)
    with Not_found ->
      let s = ascii_of_id id in
      if is_lower s || begins_with_CoqXX s then
	(add_index id 1; "Coq_"^s)
      else
	(add_index id 0; s)

(*s Creating renaming for a [module_path] : first, the real function ... *)

let rec mp_renaming_fun mp = match mp with
  | _ when not (modular ()) && at_toplevel mp -> [""]
  | MPdot (mp,l) ->
      let lmp = mp_renaming mp in
      let mp = match lmp with
      | [""] -> modfstlev_rename l
      | _ -> modular_rename Mod (Label.to_id l)
      in
      mp ::lmp
  | MPbound mbid ->
      let s = modular_rename Mod (MBId.to_id mbid) in
      if not (params_ren_mem mp) then [s]
      else let i,_,_ = MBId.repr mbid in [s^"__"^string_of_int i]
  | MPfile _ ->
      assert (modular ()); (* see [at_toplevel] above *)
      assert (get_phase () == Pre);
      let current_mpfile = (List.last (get_visible ())).mp in
      if not (ModPath.equal mp current_mpfile) then mpfiles_add mp;
      [string_of_modfile mp]

(* ... and its version using a cache *)

and mp_renaming =
  let add,get,_ = mktable_modpath true in
  fun x ->
    try if is_mp_bound (base_mp x) then raise Not_found; get x
    with Not_found -> let y = mp_renaming_fun x in add x y; y

(*s Renamings creation for a [global_reference]: we build its fully-qualified
    name in a [string list] form (head is the short name). *)

let ref_renaming_fun (k,r) =
  let mp = modpath_of_r r in
  let l = mp_renaming mp in
  let l = if lang () != Ocaml && not (modular ()) then [""] else l in
  let s =
    let idg = safe_basename_of_global r in
    match l with
    | [""] -> (* this happens only at toplevel of the monolithic case *)
      let globs = get_global_ids () in
      let id = next_ident_away (kindcase_id k idg) globs in
      Id.to_string id
    | _ -> modular_rename k idg
  in
  add_global_ids (Id.of_string s);
  s::l

(* Cached version of the last function *)

let ref_renaming =
  let add,get,_ = mktable_ref true in
  fun ((k,r) as x) ->
    try if is_mp_bound (base_mp (modpath_of_r r)) then raise Not_found; get r
    with Not_found -> let y = ref_renaming_fun x in add r y; y

(* [visible_clash mp0 (k,s)] checks if [mp0-s] of kind [k]
   can be printed as [s] in the current context of visible
   modules. More precisely, we check if there exists a
   visible [mp] that contains [s].
   The verification stops if we encounter [mp=mp0]. *)

let rec clash mem mp0 ks = function
  | [] -> false
  | mp :: _ when ModPath.equal mp mp0 -> false
  | mp :: _ when mem mp ks -> true
  | _ :: mpl -> clash mem mp0 ks mpl

let mpfiles_clash mp0 ks =
  clash (fun mp k -> KMap.mem k (get_mpfiles_content mp)) mp0 ks
    (List.rev (mpfiles_list ()))

let rec params_lookup mp0 ks = function
  | [] -> false
  | param :: _ when ModPath.equal mp0 param -> true
  | param :: params ->
      let () = match ks with
      | (Mod, mp) when String.equal (List.hd (mp_renaming param)) mp -> params_ren_add param
      | _ -> ()
      in
      params_lookup mp0 ks params

let visible_clash mp0 ks =
  let rec clash = function
    | [] -> false
    | v :: _ when ModPath.equal v.mp mp0 -> false
    | v :: vis ->
	let b = KMap.mem ks v.content in
	if b && not (is_mp_bound mp0) then true
	else begin
	  if b then params_ren_add mp0;
	  if params_lookup mp0 ks v.params then false
	  else clash vis
	end
  in clash (get_visible ())

(* Same, but with verbose output (and mp0 shouldn't be a MPbound) *)

let visible_clash_dbg mp0 ks =
  let rec clash = function
    | [] -> None
    | v :: _ when ModPath.equal v.mp mp0 -> None
    | v :: vis ->
	try Some (v.mp,KMap.find ks v.content)
	with Not_found ->
	  if params_lookup mp0 ks v.params then None
	  else clash vis
  in clash (get_visible ())

(* After the 1st pass, we can decide which modules will be opened initially *)

let opened_libraries () =
  if not (modular ()) then []
  else
    let used_files = mpfiles_list () in
    let used_ks = List.map (fun mp -> Mod,string_of_modfile mp) used_files in
    (* By default, we open all used files. Ambiguities will be resolved later
       by using qualified names. Nonetheless, we don't open any file A that
       contains an immediate submodule A.B hiding another file B : otherwise,
       after such an open, there's no unambiguous way to refer to objects of B. *)
    let to_open =
      List.filter
	(fun mp ->
	   not (List.exists (fun k -> KMap.mem k (get_mpfiles_content mp)) used_ks))
	used_files
    in
    mpfiles_clear ();
    List.iter mpfiles_add to_open;
    mpfiles_list ()

(*s On-the-fly qualification issues for both monolithic or modular extraction. *)

(* [pp_ocaml_gen] below is a function that factorize the printing of both
   [global_reference] and module names for ocaml. When [k=Mod] then [olab=None],
   otherwise it contains the label of the reference to print.
   [rls] is the string list giving the qualified name, short name at the end. *)

(* In Coq, we can qualify [M.t] even if we are inside [M], but in Ocaml we
   cannot do that. So, if [t] gets hidden and we need a long name for it,
   we duplicate the _definition_ of t in a Coq__XXX module, and similarly
   for a sub-module [M.N] *)

let pp_duplicate k' prefix mp rls olab =
  let rls', lbl =
    if k' != Mod then
      (* Here rls=[s], the ref to print is <prefix>.<s>, and olab<>None *)
      rls, Option.get olab
    else
      (* Here rls=s::rls', we search the label for s inside mp *)
      List.tl rls, get_nth_label_mp (mp_length mp - mp_length prefix) mp
  in
  match get_duplicate prefix lbl with
  | Some ren -> dottify (ren :: rls')
  | None ->
     assert (get_phase () == Pre); (* otherwise it's too late *)
     add_duplicate prefix lbl; dottify rls

let fstlev_ks k = function
  | [] -> assert false
  | [s] -> k,s
  | s::_ -> Mod,s

(* [pp_ocaml_local] : [mp] has something in common with [top_visible ()]
   but isn't equal to it *)

let pp_ocaml_local k prefix mp rls olab =
  (* what is the largest prefix of [mp] that belongs to [visible]? *)
  assert (k != Mod || not (ModPath.equal mp prefix)); (* mp as whole module isn't in itself *)
  let rls' = List.skipn (mp_length prefix) rls in
  let k's = fstlev_ks k rls' in
  (* Reference r / module path mp is of the form [<prefix>.s.<...>]. *)
  if not (visible_clash prefix k's) then dottify rls'
  else pp_duplicate (fst k's) prefix mp rls' olab

(* [pp_ocaml_bound] : [mp] starts with a [MPbound], and we are not inside
   (i.e. we are not printing the type of the module parameter) *)

let pp_ocaml_bound base rls =
  (* clash with a MPbound will be detected and fixed by renaming this MPbound *)
  if get_phase () == Pre then ignore (visible_clash base (Mod,List.hd rls));
  dottify rls

(* [pp_ocaml_extern] : [mp] isn't local, it is defined in another [MPfile]. *)

let pp_ocaml_extern k base rls = match rls with
  | [] -> assert false
  | base_s :: rls' ->
      if (not (modular ())) (* Pseudo qualification with "" *)
	|| (List.is_empty rls')  (* Case of a file A.v used as a module later *)
	|| (not (mpfiles_mem base)) (* Module not opened *)
	|| (mpfiles_clash base (fstlev_ks k rls')) (* Conflict in opened files *)
	|| (visible_clash base (fstlev_ks k rls')) (* Local conflict *)
      then
	(* We need to fully qualify. Last clash situation is unsupported *)
	match visible_clash_dbg base (Mod,base_s) with
	  | None -> dottify rls
	  | Some (mp,l) -> error_module_clash base (MPdot (mp,l))
      else
	(* Standard situation : object in an opened file *)
	dottify rls'

(* [pp_ocaml_gen] : choosing between [pp_ocaml_local] or [pp_ocaml_extern] *)

let pp_ocaml_gen k mp rls olab =
  match common_prefix_from_list mp (get_visible_mps ()) with
    | Some prefix -> pp_ocaml_local k prefix mp rls olab
    | None ->
	let base = base_mp mp in
	if is_mp_bound base then pp_ocaml_bound base rls
	else pp_ocaml_extern k base rls

(* For Haskell, things are simplier: we have removed (almost) all structures *)

let pp_haskell_gen k mp rls = match rls with
  | [] -> assert false
  | s::rls' ->
    let str = pseudo_qualify rls' in
    let str = if is_upper str && not (upperkind k) then ("_"^str) else str in
    if ModPath.equal (base_mp mp) (top_visible_mp ()) then str else s^"."^str

(* Main name printing function for a reference *)

let pp_global k r =
  let ls = ref_renaming (k,r) in
  assert (List.length ls > 1);
  let s = List.hd ls in
  let mp,_,l = repr_of_r r in
  if ModPath.equal mp (top_visible_mp ()) then
    (* simpliest situation: definition of r (or use in the same context) *)
    (* we update the visible environment *)
    (add_visible (k,s) l; unquote s)
  else
    let rls = List.rev ls in (* for what come next it's easier this way *)
    match lang () with
      | Scheme -> unquote s (* no modular Scheme extraction... *)
      | JSON -> dottify (List.map unquote rls)
      | Haskell -> if modular () then pp_haskell_gen k mp rls else s
      | Ocaml -> pp_ocaml_gen k mp rls (Some l)

(* The next function is used only in Ocaml extraction...*)

let pp_module mp =
  let ls = mp_renaming mp in
  match mp with
    | MPdot (mp0,l) when ModPath.equal mp0 (top_visible_mp ()) ->
	(* simpliest situation: definition of mp (or use in the same context) *)
	(* we update the visible environment *)
	let s = List.hd ls in
	add_visible (Mod,s) l; s
    | _ -> pp_ocaml_gen Mod mp (List.rev ls) None

(** Special hack for constants of type Ascii.ascii : if an
    [Extract Inductive ascii => char] has been declared, then
    the constants are directly turned into chars *)

let mk_ind path s =
  MutInd.make2 (MPfile (dirpath_of_string path)) (Label.make s)

let ind_ascii = mk_ind "Coq.Strings.Ascii" "ascii"

let check_extract_ascii () =
  try
    let char_type = match lang () with
      | Ocaml -> "char"
      | Haskell -> "Prelude.Char"
      | _ -> raise Not_found
    in
    String.equal (find_custom (IndRef (ind_ascii, 0))) (char_type)
  with Not_found -> false

let is_list_cons l =
 List.for_all (function MLcons (_,ConstructRef(_,_),[]) -> true | _ -> false) l

let is_native_char = function
  | MLcons(_,ConstructRef ((kn,0),1),l) ->
    MutInd.equal kn ind_ascii && check_extract_ascii () && is_list_cons l
  | _ -> false

let get_native_char c =
  let rec cumul = function
    | [] -> 0
    | MLcons(_,ConstructRef(_,j),[])::l -> (2-j) + 2 * (cumul l)
    | _ -> assert false
  in
  let l = match c with MLcons(_,_,l) -> l | _ -> assert false in
  Char.chr (cumul l)

let pp_native_char c = str ("'"^Char.escaped (get_native_char c)^"'")
