(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Names
open Term
open Declarations
open Nameops
open Libnames
open Table
open Miniml
open Mlutil
open Modutil
open Mod_subst

(*s Some pretty-print utility functions. *)

let pp_par par st = if par then str "(" ++ st ++ str ")" else st

let pp_apply st par args = match args with
  | [] -> st
  | _  -> hov 2 (pp_par par (st ++ spc () ++ prlist_with_sep spc identity args))

let pr_binding = function
  | [] -> mt ()
  | l  -> str " " ++ prlist_with_sep (fun () -> str " ") pr_id l

let fnl2 () = fnl () ++ fnl ()

let space_if = function true -> str " " | false -> mt ()

let sec_space_if = function true -> spc () | false -> mt ()

let is_digit = function
  | '0'..'9' -> true
  | _ -> false

let begins_with_CoqXX s =
  let n = String.length s in
  n >= 4 && s.[0] = 'C' && s.[1] = 'o' && s.[2] = 'q' &&
  let i = ref 3 in
  try while !i < n do
    if s.[!i] = '_' then i:=n (*Stop*)
    else if is_digit s.[!i] then incr i
    else raise Not_found
  done; true
  with Not_found -> false

let unquote s =
  if lang () <> Scheme then s
  else
    let s = String.copy s in
    for i=0 to String.length s - 1 do if s.[i] = '\'' then s.[i] <- '~' done;
    s

let rec dottify = function
  | [] -> assert false
  | [s] -> s
  | s::[""] -> s
  | s::l -> (dottify l)^"."^s

(*s Uppercase/lowercase renamings. *)

let is_upper s = match s.[0] with 'A' .. 'Z' -> true | _ -> false
let is_lower s = match s.[0] with 'a' .. 'z' | '_' -> true | _ -> false

let lowercase_id id = id_of_string (String.uncapitalize (string_of_id id))
let uppercase_id id = id_of_string (String.capitalize (string_of_id id))

type kind = Term | Type | Cons | Mod

let upperkind = function
  | Type -> lang () = Haskell
  | Term -> false
  | Cons | Mod -> true

let kindcase_id k id =
  if upperkind k then uppercase_id id else lowercase_id id

(*s de Bruijn environments for programs *)

type env = identifier list * Idset.t

(*s Generic renaming issues for local variable names. *)

let rec rename_id id avoid =
  if Idset.mem id avoid then rename_id (lift_ident id) avoid else id

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
      (id :: idl, Idset.add id avoid)

let rename_tvars avoid l =
  let rec rename avoid = function
    | [] -> [],avoid
    | id :: idl ->
	let id = rename_id (lowercase_id id) avoid in
	let idl, avoid = rename (Idset.add id avoid) idl in
	(id :: idl, avoid) in
  fst (rename avoid l)

let push_vars ids (db,avoid) =
  let ids',avoid' = rename_vars avoid ids in
  ids', (ids' @ db, avoid')

let get_db_name n (db,_) =
  let id = List.nth db (pred n) in
  if id = dummy_name then id_of_string "__" else id


(*S Renamings of global objects. *)

(*s Tables of global renamings *)

let register_cleanup, do_cleanup =
  let funs = ref [] in
  (fun f -> funs:=f::!funs), (fun () -> List.iter (fun f -> f ()) !funs)

type phase = Pre | Impl | Intf

let set_phase, get_phase =
  let ph = ref Impl in ((:=) ph), (fun () -> !ph)

let set_keywords, get_keywords =
  let k = ref Idset.empty in
  ((:=) k), (fun () -> !k)

let add_global_ids, get_global_ids =
  let ids = ref Idset.empty in
  register_cleanup (fun () -> ids := get_keywords ());
  let add s = ids := Idset.add s !ids
  and get () = !ids
  in (add,get)

let empty_env () = [], get_global_ids ()

let mktable autoclean =
  let h = Hashtbl.create 97 in
  if autoclean then register_cleanup (fun () -> Hashtbl.clear h);
  (Hashtbl.add h, Hashtbl.find h, fun () -> Hashtbl.clear h)

(* A table recording objects in the first level of all MPfile *)

let add_mpfiles_content,get_mpfiles_content,clear_mpfiles_content =
  mktable false

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

(*s table indicating the visible horizon at a precise moment,
    i.e. the stack of structures we are inside.

  - The sequence of [mp] parts should have the following form:
  [X.Y; X; A.B.C; A.B; A; ...], i.e. each addition should either
  be a [MPdot] over the last entry, or something new, mainly
  [MPself], or [MPfile] at the beginning.

  - The [content] part is used to recoard all the names already
  seen at this level.

  - The [subst] part is here mainly for printing signature
  (in which names are still short, i.e. relative to a [msid]).
*)

type visible_layer = { mp : module_path;
		       content : ((kind*string),unit) Hashtbl.t }

let pop_visible, push_visible, get_visible, subst_mp =
  let vis = ref [] and sub = ref [empty_subst] in
  register_cleanup (fun () -> vis := []; sub := [empty_subst]);
  let pop () =
    let v = List.hd !vis in
    (* we save the 1st-level-content of MPfile for later use *)
    if get_phase () = Impl && modular () && is_modfile v.mp
    then add_mpfiles_content v.mp v.content;
    vis := List.tl !vis;
    sub := List.tl !sub
  and push mp o =
    vis := { mp = mp; content = Hashtbl.create 97 } :: !vis;
    let s = List.hd !sub in
    let s = match o with None -> s | Some msid -> add_mp msid mp empty_delta_resolver s in
    sub := s :: !sub
  and get () = !vis
  and subst mp = subst_mp (List.hd !sub) mp
  in (pop,push,get,subst)

let get_visible_mps () = List.map (function v -> v.mp) (get_visible ())
let top_visible () = match get_visible () with [] -> assert false | v::_ -> v
let top_visible_mp () = (top_visible ()).mp
let add_visible ks = Hashtbl.add (top_visible ()).content ks ()

(* table of local module wrappers used to provide non-ambiguous names *)

let add_duplicate, check_duplicate =
  let index = ref 0 and dups = ref Gmap.empty in
  register_cleanup (fun () -> index := 0; dups := Gmap.empty);
  let add mp l =
     incr index;
     let ren = "Coq__" ^ string_of_int (!index) in
     dups := Gmap.add (mp,l) ren !dups
  and check mp l = Gmap.find (subst_mp mp, l) !dups
  in (add,check)

type reset_kind = AllButExternal | Everything

let reset_renaming_tables flag =
  do_cleanup ();
  if flag = Everything then clear_mpfiles_content ()

(*S Renaming functions *)

(* This function creates from [id] a correct uppercase/lowercase identifier.
   This is done by adding a [Coq_] or [coq_] prefix. To avoid potential clashes
   with previous [Coq_id] variable, these prefixes are duplicated if already
   existing. *)

let modular_rename k id =
  let s = string_of_id id in
  let prefix,is_ok =
    if upperkind k then "Coq_",is_upper else "coq_",is_lower
  in
  if not (is_ok s) ||
    (Idset.mem id (get_keywords ())) ||
    (String.length s >= 4 && String.sub s 0 4 = prefix)
  then prefix ^ s
  else s

(*s For monolithic extraction, first-level modules might have to be renamed
    with unique numbers *)

let modfstlev_rename =
  let add_prefixes,get_prefixes,_ = mktable true in
  fun l ->
    let coqid = id_of_string "Coq" in
    let id = id_of_label l in
    try
      let coqset = get_prefixes id in
      let nextcoq = next_ident_away coqid coqset in
      add_prefixes id (nextcoq::coqset);
      (string_of_id nextcoq)^"_"^(string_of_id id)
    with Not_found ->
      let s = string_of_id id in
      if is_lower s || begins_with_CoqXX s then
	(add_prefixes id [coqid]; "Coq_"^s)
      else
	(add_prefixes id []; s)

(*s Creating renaming for a [module_path] : first, the real function ... *)

let rec mp_renaming_fun mp = match mp with
  | _ when not (modular ()) && at_toplevel mp -> [""]
  | MPdot (mp,l) ->
      let lmp = mp_renaming mp in
      if lmp = [""] then (modfstlev_rename l)::lmp
      else (modular_rename Mod (id_of_label l))::lmp
  | MPbound mbid -> [modular_rename Mod (id_of_mbid mbid)]
  | MPfile _ when not (modular ()) -> assert false (* see [at_toplevel] above *)
  | MPfile _ ->
      assert (get_phase () = Pre);
      let current_mpfile = (list_last (get_visible ())).mp in
      if mp <> current_mpfile then mpfiles_add mp;
      [string_of_modfile mp]

(* ... and its version using a cache *)

and mp_renaming =
  let add,get,_ = mktable true in
  fun x ->  try get x with Not_found -> let y = mp_renaming_fun x in add x y; y

(*s Renamings creation for a [global_reference]: we build its fully-qualified
    name in a [string list] form (head is the short name). *)

let ref_renaming_fun (k,r) =
  let mp = subst_mp (modpath_of_r r) in
  let l = mp_renaming mp in
  let s =
    if l = [""] (* this happens only at toplevel of the monolithic case *)
    then
      let globs = Idset.elements (get_global_ids ()) in
      let id = next_ident_away (kindcase_id k (safe_basename_of_global r)) globs in
      string_of_id id
    else modular_rename k (safe_basename_of_global r)
  in
  add_global_ids (id_of_string s);
  s::l

(* Cached version of the last function *)

let ref_renaming =
  let add,get,_ = mktable true in
  fun x -> try get x with Not_found -> let y = ref_renaming_fun x in add x y; y

(* [visible_clash mp0 (k,s)] checks if [mp0-s] of kind [k]
   can be printed as [s] in the current context of visible
   modules. More precisely, we check if there exists a
   visible [mp] that contains [s].
   The verification stops if we encounter [mp=mp0]. *)

let rec clash mem mp0 ks = function
  | [] -> false
  | mp :: _ when mp = mp0 -> false
  | mp :: _ when mem mp ks -> true
  | _ :: mpl -> clash mem mp0 ks mpl

let mpfiles_clash mp0 ks =
  clash (fun mp -> Hashtbl.mem (get_mpfiles_content mp)) mp0 ks
    (List.rev (mpfiles_list ()))

let visible_clash mp0 ks =
  let rec clash = function
    | [] -> false
    | v :: _ when v.mp = mp0 -> false
    | v :: _ when Hashtbl.mem v.content ks -> true
    | _ :: vis -> clash vis
  in clash (get_visible ())

(* After the 1st pass, we can decide which modules will be opened initially *)

let opened_libraries () =
  if not (modular ()) then []
  else
    let used = mpfiles_list () in
    let rec check_elsewhere avoid = function
      | [] -> []
      | mp :: mpl ->
	  let clash s = Hashtbl.mem (get_mpfiles_content mp) (Mod,s) in
	  if List.exists clash avoid
	  then check_elsewhere avoid mpl
	  else mp :: check_elsewhere (string_of_modfile mp :: avoid) mpl
    in
    let opened = check_elsewhere [] used in
    mpfiles_clear ();
    List.iter mpfiles_add opened;
    opened

(*s On-the-fly qualification issues for both monolithic or modular extraction. *)

(* First, a function that factorize the printing of both [global_reference]
   and module names for ocaml. When [k=Mod] then [olab=None], otherwise it
   contains the label of the reference to print.
   Invariant: [List.length ls >= 2], simpler situations are handled elsewhere. *)

let pp_gen k mp ls olab =
  try (* what is the largest prefix of [mp] that belongs to [visible]? *)
    let prefix = common_prefix_from_list mp (get_visible_mps ()) in
    let delta = mp_length mp - mp_length prefix in
    assert (k <> Mod || mp <> prefix); (* mp as whole module isn't in itself *)
    let ls = list_firstn (delta + if k = Mod then 0 else 1) ls in
    let s,ls' = list_sep_last ls in
    (* Reference r / module path mp is of the form [<prefix>.s.<List.rev ls'>].
       Difficulty: in ocaml the prefix part cannot be used for
       qualification (we are inside it) and the rest of the long
       name may be hidden.
       Solution: we duplicate the _definition_ of r / mp in a Coq__XXX module *)
    let k' = if ls' = [] then k else Mod in
    if visible_clash prefix (k',s) then
      let front = if ls' = [] && k <> Mod then [s] else ls' in
      let lab = (* label associated with s *)
	if delta = 0 && k <> Mod then Option.get olab
	else get_nth_label_mp delta mp
      in
      try dottify (front @ [check_duplicate prefix lab])
      with Not_found ->
	assert (get_phase () = Pre); (* otherwise it's too late *)
	add_duplicate prefix lab; dottify ls
    else dottify ls
  with Not_found ->
    (* [mp] belongs to a closed module, not one of [visible]. *)
    let base = base_mp mp in
    let base_s,ls1 = list_sep_last ls in
    let s,ls2 = list_sep_last ls1 in
    (* [List.rev ls] is [base_s :: s :: List.rev ls2] *)
    let k' = if ls2 = [] then k else Mod in
    if modular () && (mpfiles_mem base) &&
      (not (mpfiles_clash base (k',s))) &&
      (not (visible_clash base (k',s)))
    then (* Standard situation of an object in another file: *)
      (* Thanks to the "open" of this file we remove its name *)
      dottify ls1
    else if visible_clash base (Mod,base_s) then
      error_module_clash base_s
    else dottify ls

let pp_global k r =
  let ls = ref_renaming (k,r) in
  assert (List.length ls > 1);
  let s = List.hd ls in
  let mp = subst_mp (modpath_of_r r) in
  if mp = top_visible_mp () then
    (* simpliest situation: definition of r (or use in the same context) *)
    (* we update the visible environment *)
    (add_visible (k,s); unquote s)
  else match lang () with
    | Scheme -> unquote s (* no modular Scheme extraction... *)
    | Haskell -> if modular () then dottify ls else s
	(* for the moment we always qualify in modular Haskell... *)
    | Ocaml -> pp_gen k mp ls (Some (label_of_r r))

(* The next function is used only in Ocaml extraction...*)
let pp_module mp =
  let mp = subst_mp mp in
  let ls = mp_renaming mp in
  if List.length ls = 1 then dottify ls
  else match mp with
    | MPdot (mp0,_) when mp0 = top_visible_mp () ->
	(* simpliest situation: definition of mp (or use in the same context) *)
	(* we update the visible environment *)
	let s = List.hd ls in
	add_visible (Mod,s); s
    | _ -> pp_gen Mod mp ls None


