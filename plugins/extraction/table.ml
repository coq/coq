(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open ModPath
open Term
open Declarations
open Namegen
open Libobject
open Goptions
open Libnames
open Globnames
open CErrors
open Util
open Pp
open Miniml

(*s Extraction Blacklist of filenames not to use while extracting *)

let blacklist_table = Summary.ref Id.Set.empty ~name:"ExtrBlacklist"

(** Sets and maps for [global_reference] that use the "user" [kernel_name]
    instead of the canonical one *)

module GlobOrd =
struct
  type t = global
  let compare g1 g2 =
    let c = GlobRef.UserOrd.compare g1.glob g2.glob in
    if Int.equal c 0 then InfvInst.compare g1.inst g2.inst else c
end

module Refmap' = CMap.Make(GlobOrd)
module Refset' = Set.Make(GlobOrd)

(*S Utilities about [module_path] and [kernel_names] and [global_reference] *)

let occur_kn_in_ref kn r = let open GlobRef in match r.glob with
  | IndRef (kn',_)
  | ConstructRef ((kn',_),_) -> MutInd.UserOrd.equal kn kn'
  | ConstRef _ | VarRef _ -> false

(* Return the "canonical" name used for declaring a name *)

let repr_of_r r = let open GlobRef in match r.glob with
  | ConstRef kn -> Constant.user kn
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) -> MutInd.user kn
  | VarRef v -> Lib.make_kn v

let modpath_of_r r =
  KerName.modpath (repr_of_r r)

let label_of_r r =
  KerName.label (repr_of_r r)

let rec base_mp = function
  | MPdot (mp,l) -> base_mp mp
  | mp -> mp

let is_modfile = function
  | MPfile _ -> true
  | _ -> false

let raw_string_of_modfile = function
  | MPfile f -> String.capitalize_ascii (Id.to_string (List.hd (DirPath.repr f)))
  | _ -> assert false

let extraction_current_mp () = fst (Safe_typing.flatten_env (Global.safe_env ()))

let is_toplevel mp = ModPath.equal mp (extraction_current_mp ())

let at_toplevel mp =
  is_modfile mp || is_toplevel mp

let mp_length mp =
  let mp0 = extraction_current_mp () in
  let rec len = function
    | mp when ModPath.equal mp mp0 -> 1
    | MPdot (mp,_) -> 1 + len mp
    | _ -> 1
  in len mp

let rec prefixes_mp mp = match mp with
  | MPdot (mp',_) -> ModPath.Set.add mp (prefixes_mp mp')
  | _ -> ModPath.Set.singleton mp

let rec get_nth_label_mp n = function
  | MPdot (mp,l) -> if Int.equal n 1 then l else get_nth_label_mp (n-1) mp
  | _ -> failwith "get_nth_label: not enough MPdot"

let common_prefix_from_list mp0 mpl =
  let prefixes = prefixes_mp mp0 in
  let rec f = function
    | [] -> None
    | mp :: l -> if ModPath.Set.mem mp prefixes then Some mp else f l
  in f mpl

let rec parse_labels2 ll = function
  | MPdot (mp,l) -> parse_labels2 (l::ll) mp
  | mp -> mp,ll

let labels_of_ref r =
  let mp,l = KerName.repr (repr_of_r r) in
  parse_labels2 [l] mp


(*S The main table: constants, inductives, records, ... *)

(* This table is not registered within coq save/undo mechanism
   since we set its contents at each run of Extraction *)

(* We use [constant_body] (resp. [mutual_inductive_body]) as checksum
   to ensure that the table contents aren't outdated. *)

module InfvMap = Map.Make(InfvInst)

type table = {
  typedefs : (constant_body * ml_type) InfvMap.t Cmap.t;
  cst_types : (constant_body * ml_schema) InfvMap.t Cmap.t;
  inductives : (mutual_inductive_body * ml_ind) InfvMap.t Mindmap.t;
  inductive_kinds : inductive_kind InfvMap.t Mindmap.t;
  recursors : KerName.Set.t;
  (* recursors: we can use the equivalence between canonical and user constant names. *)
  projs : GlobRef.Set.t;
  (* projs: working modulo name equivalence is ok *)
  info_axioms : GlobRef.Set.t;
  log_axioms : GlobRef.Set.t;
  symbols : Id.t list GlobRef.Map.t;
  opaques:  GlobRef.Set.t;
  modfile_ids : Id.Set.t;
  modfile_mps : string DirPath.Map.t;
}

type t = table ref

let empty_table = {
  typedefs = Cmap.empty;
  cst_types = Cmap.empty;
  inductives = Mindmap.empty;
  inductive_kinds = Mindmap.empty;
  recursors = KerName.Set.empty;
  projs = GlobRef.Set.empty;
  info_axioms = GlobRef.Set.empty;
  log_axioms = GlobRef.Set.empty;
  symbols = GlobRef.Map.empty;
  opaques = GlobRef.Set.empty;
  modfile_ids = Id.Set.empty;
  modfile_mps = DirPath.Map.empty;
}

let make_table () = ref { empty_table with modfile_ids = Summary.Ref.get blacklist_table }

let add_typedef table kn inst cb t =
  let upd = function
  | None -> Some (InfvMap.singleton inst (cb, t))
  | Some map -> Some (InfvMap.add inst (cb, t) map)
  in
  table := { !table with typedefs = Cmap.update kn upd !table.typedefs }

let lookup_typedef table kn inst cb =
  try
    let (cb0, t) = InfvMap.find inst (Cmap.find kn !table.typedefs) in
    if cb0 == cb then Some t else None
  with Not_found -> None

let add_cst_type table kn inst cb s =
  let upd = function
  | None -> Some (InfvMap.singleton inst (cb, s))
  | Some map -> Some (InfvMap.add inst (cb, s) map)
  in
  table := { !table with cst_types = Cmap.update kn upd !table.cst_types }

let lookup_cst_type table kn inst cb =
  try
    let (cb0, s) = InfvMap.find inst (Cmap.find kn !table.cst_types) in
    if cb0 == cb then Some s else None
  with Not_found -> None

let add_ind table kn inst mib ml_ind =
  let upd = function
  | None -> Some (InfvMap.singleton inst (mib, ml_ind))
  | Some map -> Some (InfvMap.add inst (mib, ml_ind) map)
  in
  table := { !table with inductives = Mindmap.update kn upd !table.inductives }

let lookup_ind table kn inst mib =
  try
    let (mib0, ml_ind) = InfvMap.find inst (Mindmap.find kn !table.inductives) in
    if mib == mib0 then Some ml_ind
    else None
  with Not_found -> None

let add_inductive_kind table kn inst k =
  let upd = function
  | None -> Some (InfvMap.singleton inst k)
  | Some map -> Some (InfvMap.add inst k map)
  in
  table := { !table with inductive_kinds = Mindmap.update kn upd !table.inductive_kinds }

let is_coinductive table r =
  let kn = let open GlobRef in match r.glob with
    | ConstructRef ((kn,_),_) -> kn
    | IndRef (kn,_) -> kn
    | _ -> assert false
  in
  try InfvMap.find r.inst (Mindmap.find kn !table.inductive_kinds) == Coinductive
  with Not_found -> false

let is_coinductive_type table = function
  | Tglob (r,_) -> is_coinductive table r
  | _ -> false

let get_record_fields table r =
  let kn = let open GlobRef in match r.glob with
    | ConstructRef ((kn,_),_) -> kn
    | IndRef (kn,_) -> kn
    | _ -> assert false
  in
  try match InfvMap.find r.inst (Mindmap.find kn !table.inductive_kinds) with
    | Record f -> f
    | _ -> []
  with Not_found -> []

let record_fields_of_type table = function
  | Tglob (r,_) -> get_record_fields table r
  | _ -> []

let add_recursors table env ind =
  let kn = MutInd.canonical ind in
  let mk_kn id =
    KerName.make (KerName.modpath kn) id
  in
  let mib = Environ.lookup_mind ind env in
  Array.iter
    (fun mip ->
       let id = mip.mind_typename in
       let kn_rec = mk_kn (Nameops.add_suffix id "_rec")
       and kn_rect = mk_kn (Nameops.add_suffix id "_rect") in
       table := { !table with recursors = KerName.Set.add kn_rec (KerName.Set.add kn_rect !table.recursors) })
    mib.mind_packets

let is_recursor table r = match r.glob with
  | GlobRef.ConstRef c -> KerName.Set.mem (Constant.canonical c) !table.recursors
  | _ -> false

let add_projection table n kn ip = table := { !table with projs = GlobRef.Set.add (GlobRef.ConstRef kn) !table.projs }
let is_projection table r = GlobRef.Set.mem r.glob !table.projs

(*s Table of used axioms *)

let add_info_axiom table r = table := { !table with info_axioms = GlobRef.Set.add r !table.info_axioms }
let remove_info_axiom table r = table := { !table with info_axioms = GlobRef.Set.remove r !table.info_axioms }
let add_log_axiom table r = table := { !table with log_axioms = GlobRef.Set.add r !table.log_axioms }
let add_symbol table r = table := { !table with symbols = GlobRef.Map.update r (function Some l -> Some l | _ -> Some []) !table.symbols }
let add_symbol_rule table r l = table := { !table with symbols = GlobRef.Map.update r (function Some lst -> Some (l :: lst) | _ -> Some [l]) !table.symbols }

let add_opaque table r = table := { !table with opaques = GlobRef.Set.add r !table.opaques }
let remove_opaque table r = table := { !table with opaques = GlobRef.Set.remove r !table.opaques }

(*s Extraction modes: modular or monolithic, library or minimal ?

Nota:
 - Recursive Extraction : monolithic, minimal
 - Separate Extraction : modular, minimal
 - Extraction Library : modular, library
*)

(*s Printing. *)

(* The following functions work even on objects not in [Global.env ()].
   Warning: for inductive objects, this only works if an [extract_inductive]
   have been done earlier, otherwise we can only ask the Nametab about
   currently visible objects. *)

let safe_basename_of_globref_gen table r =
  let last_chance r (kn, pos) =
    try Nametab.basename_of_global r
    with Not_found ->
      let id = Id.to_string (MutInd.label kn) in
      Id.of_string (id ^ "_" ^ String.concat "_" (List.map string_of_int pos))
  in
  let unsafe_lookup_ind table kn = snd @@ snd (InfvMap.choose (Mindmap.find kn !table.inductives)) in
  let open GlobRef in
  match r with
    | ConstRef kn -> Constant.label kn
    | IndRef (kn,0) -> MutInd.label kn
    | IndRef (kn,i) ->
      begin match table with
      | None -> last_chance r (kn, [i])
      | Some table ->
        try (unsafe_lookup_ind table kn).ind_packets.(i).ip_typename
        with Not_found -> last_chance r (kn, [i])
      end
    | ConstructRef ((kn,i),j) ->
      begin match table with
      | None -> last_chance r (kn, [i; j])
      | Some table ->
        try (unsafe_lookup_ind table kn).ind_packets.(i).ip_consnames.(j-1)
        with Not_found -> last_chance r (kn, [i])
      end
    | VarRef v -> v

let safe_basename_of_global table r = safe_basename_of_globref_gen (Some table) r.glob

let string_of_globref r  =
 try string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty r)
 with Not_found -> Id.to_string (safe_basename_of_globref_gen None r)

let safe_pr_globref r = str (string_of_globref r)

let safe_pr_global r = safe_pr_globref r.glob

(* idem, but with qualification, and only for constants. *)

let safe_pr_long_global r =
  try Printer.pr_global r.glob
  with Not_found -> match r.glob with
    | GlobRef.ConstRef kn ->
        let mp,l = KerName.repr (Constant.user kn) in
        str ((ModPath.to_string mp)^"."^(Id.to_string l))
    | _ -> assert false

let pr_long_mp mp =
  let sp = Nametab.path_of_module mp in
  Libnames.pr_path sp

let pr_long_global ref = pr_path (Nametab.path_of_global ref)

(*S Warning and Error messages. *)

let err ?loc s = user_err ?loc s

let warn_extraction_axiom_to_realize =
  CWarnings.create ~name:"extraction-axiom-to-realize" ~category:CWarnings.CoreCategories.extraction
         (fun axioms ->
          let s = if Int.equal (List.length axioms) 1 then "axiom" else "axioms" in
          strbrk ("The following "^s^" must be realized in the extracted code:")
                   ++ hov 1 (spc () ++ prlist_with_sep spc safe_pr_globref axioms)
                   ++ str "." ++ fnl ())

let warn_extraction_logical_axiom =
  CWarnings.create ~name:"extraction-logical-axiom" ~category:CWarnings.CoreCategories.extraction
         (fun axioms ->
          let s =
            if Int.equal (List.length axioms) 1 then "axiom was" else "axioms were"
          in
          (strbrk ("The following logical "^s^" encountered:") ++
             hov 1 (spc () ++ prlist_with_sep spc safe_pr_globref axioms ++ str ".\n")
           ++ strbrk "Having invalid logical axiom in the environment when extracting"
           ++ spc () ++ strbrk "may lead to incorrect or non-terminating ML terms." ++
             fnl ()))

let warn_extraction_symbols =
  let pp_symb_with_rules (symb, rules) =
    safe_pr_globref symb ++
    if List.is_empty rules then str " (no rules)" else
    str ":" ++ spc() ++ prlist_with_sep spc Id.print rules
  in
  CWarnings.create ~name:"extraction-symbols" ~category:CWarnings.CoreCategories.extraction
    (fun symbols ->
      strbrk ("The following symbols and rules were encountered:") ++ fnl () ++
      prlist_with_sep fnl pp_symb_with_rules symbols ++ fnl () ++
      strbrk "The symbols must be realized such that the rewrite rules apply," ++ spc () ++
      strbrk "or extraction may lead to incorrect or non-terminating ML terms." ++
      fnl ())

let warning_axioms table =
  let info_axioms = GlobRef.Set.elements !table.info_axioms in
  if not (List.is_empty info_axioms) then
    warn_extraction_axiom_to_realize info_axioms;
  let log_axioms = GlobRef.Set.elements !table.log_axioms in
  if not (List.is_empty log_axioms) then
    warn_extraction_logical_axiom log_axioms;
  let symbols = GlobRef.Map.bindings !table.symbols in
  if not (List.is_empty symbols) then
    warn_extraction_symbols symbols

let warn_extraction_opaque_accessed =
  CWarnings.create ~name:"extraction-opaque-accessed" ~category:CWarnings.CoreCategories.extraction
    (fun lst -> strbrk "The extraction is currently set to bypass opacity, " ++
                  strbrk "the following opaque constant bodies have been accessed :" ++
                  lst ++ str "." ++ fnl ())

let warn_extraction_opaque_as_axiom =
  CWarnings.create ~name:"extraction-opaque-as-axiom" ~category:CWarnings.CoreCategories.extraction
    (fun lst -> strbrk "The extraction now honors the opacity constraints by default, " ++
         strbrk "the following opaque constants have been extracted as axioms :" ++
         lst ++ str "." ++ fnl () ++
         strbrk "If necessary, use \"Set Extraction AccessOpaque\" to change this."
         ++ fnl ())

let warning_opaques table accessed =
  let opaques = GlobRef.Set.elements !table.opaques in
  if not (List.is_empty opaques) then
    let lst = hov 1 (spc () ++ prlist_with_sep spc safe_pr_globref opaques) in
    if accessed then warn_extraction_opaque_accessed lst
    else warn_extraction_opaque_as_axiom lst

let warning_ambiguous_name =
  CWarnings.create ~name:"extraction-ambiguous-name" ~category:CWarnings.CoreCategories.extraction
    ~quickfix:(fun ~loc (_,mp,r) -> List.map (Quickfix.make ~loc) [pr_long_mp mp;pr_long_global r])
    (fun (q,mp,r) ->
       strbrk "The name " ++ pr_qualid q ++ strbrk " is ambiguous, " ++
       strbrk "do you mean module " ++
       pr_long_mp mp ++
       strbrk " or object " ++
       pr_long_global r ++ str " ?" ++ fnl () ++
       strbrk "First choice is assumed, for the second one please use " ++
       strbrk "fully qualified name." ++ fnl ())

let error_axiom_scheme ?loc r i =
  err ?loc (str "The type scheme axiom " ++ spc () ++
       safe_pr_global r ++ spc () ++ str "needs " ++ int i ++
       str " type variable(s).")

let check_inside_section () =
  if Lib.sections_are_opened () then
    err (str "You can't do that within a section." ++ fnl () ++
         str "Close it and try again.")

let warn_extraction_reserved_identifier =
  CWarnings.create ~name:"extraction-reserved-identifier" ~category:CWarnings.CoreCategories.extraction
    (fun s -> strbrk ("The identifier "^s^
                " contains __ which is reserved for the extraction"))

let warning_id s = warn_extraction_reserved_identifier s

let error_constant ?loc r =
  err ?loc (safe_pr_global r ++ str " is not a constant.")

let error_inductive ?loc r =
  err ?loc (safe_pr_global r ++ spc () ++ str "is not an inductive type.")

let error_nb_cons () =
  err (str "Not the right number of constructors.")

let error_module_clash mp1 mp2 =
  err (str "The Rocq modules " ++ pr_long_mp mp1 ++ str " and " ++
       pr_long_mp mp2 ++ str " have the same ML name.\n" ++
       str "This is not supported yet. Please do some renaming first.")

let error_no_module_expr mp =
  err (str "The module " ++ pr_long_mp mp
       ++ str " has no body, it probably comes from\n"
       ++ str "some Declare Module outside any Module Type.\n"
       ++ str "This situation is currently unsupported by the extraction.")

let error_singleton_become_prop ind =
  (* Should be fine, only used for printing and with template poly inductives *)
  let ind = { glob = IndRef ind; inst = InfvInst.empty } in
  err (str "The informative inductive type " ++ safe_pr_global ind ++
       str " has a Prop instance" ++ str "." ++ fnl () ++
       str "This happens when a sort-polymorphic singleton inductive type\n" ++
       str "has logical parameters, such as (I,I) : (True * True) : Prop.\n" ++
       str "Extraction cannot handle this situation yet.\n" ++
       str "Instead, use a sort-monomorphic type such as (True /\\ True)\n" ++
       str "or extract to Haskell.")

let error_unknown_module ?loc m =
  err ?loc (str "Module" ++ spc () ++ pr_qualid m ++ spc () ++ str "not found.")

type lang =
  | Ocaml | Haskell | Scheme | JSON
  | External of string

let lang_name = function
  | Ocaml -> "OCaml"
  | Haskell -> "Haskell"
  | Scheme -> "Scheme"
  | JSON -> "JSON"
  | External s -> s

let error_not_modular l =
  err (str "Modular extraction is not supported for " ++ str (lang_name l) ++ str "." ++ fnl () ++
       str "Use Recursive Extraction or Extraction \"file\" to extract into a single file instead.")

let error_not_visible r =
  err (safe_pr_global r ++ str " is not directly visible.\n" ++
       str "For example, it may be inside an applied functor.\n" ++
       str "Use Recursive Extraction to get the whole environment.")

let error_MPfile_as_mod mp b =
  let s1 = if b then "asked" else "required" in
  let s2 = if b then "extract some objects of this module or\n" else "" in
  err (str ("Extraction of file "^(raw_string_of_modfile mp)^
            ".v as a module is "^s1^".\n"^
            "Monolithic Extraction cannot deal with this situation.\n"^
            "Please "^s2^"use (Recursive) Extraction Library instead.\n"))

let argnames_of_global r =
  let env = Global.env () in
  let typ, _ = Typeops.type_of_global_in_context env r.glob in
  let rels,_ =
    decompose_prod (Reduction.whd_all env typ) in
  List.rev_map (fun x -> Context.binder_name (fst x)) rels

let msg_of_implicit = function
  | Kimplicit (r,i) ->
     let name = match (List.nth (argnames_of_global r) (i-1)) with
       | Anonymous -> ""
       | Name id -> "(" ^ Id.to_string id ^ ") "
     in
     (String.ordinal i)^" argument "^name^"of "^(string_of_globref r.glob)
  | Ktype | Kprop -> ""

let error_remaining_implicit k =
  let s = msg_of_implicit k in
  err (str ("An implicit occurs after extraction : "^s^".") ++ fnl () ++
       str "Please check your Extraction Implicit declarations." ++ fnl() ++
       str "You might also try Unset Extraction SafeImplicits to force" ++
       fnl() ++ str "the extraction of unsafe code and review it manually.")

let warn_extraction_remaining_implicit =
  CWarnings.create ~name:"extraction-remaining-implicit" ~category:CWarnings.CoreCategories.extraction
    (fun s -> strbrk ("At least an implicit occurs after extraction : "^s^".") ++ fnl () ++
     strbrk "Extraction SafeImplicits is unset, extracting nonetheless,"
     ++ strbrk "but this code is potentially unsafe, please review it manually.")

let warning_remaining_implicit k =
  let s = msg_of_implicit k in
  warn_extraction_remaining_implicit s

let check_loaded_modfile mp = match base_mp mp with
  | MPfile dp ->
      if not (Library.library_is_loaded dp) then begin
        match base_mp (extraction_current_mp ()) with
          | MPfile dp' when not (DirPath.equal dp dp') ->
            err (str "Please load library " ++ DirPath.print dp ++ str " first.")
          | _ -> ()
      end
  | _ -> ()

let info_file f =
  Flags.if_verbose Feedback.msg_info
    (str ("The file "^f^" has been created by extraction."))


(*S The Extraction auxiliary commands *)

(* The objects defined below should survive an arbitrary time,
   so we register them to coq save/undo mechanism. *)

let my_bool_option name value =
  let { Goptions.get } =
    declare_bool_option_and_ref
    ~key:["Extraction"; name]
    ~value
    ()
  in
  get

(*s Extraction Output Directory *)

let warn_using_current_directory =
  CWarnings.(create ~name:"extraction-default-directory" ~category:CoreCategories.extraction)
    (fun s ->
       Pp.(strbrk
             "Setting extraction output directory by default to \"" ++ str s ++ strbrk "\". Use \"" ++
           str "Set Extraction Output Directory" ++
           strbrk "\" or command line option \"-output-directory\" to " ++
           strbrk "set a different directory for extracted files to appear in."))

let output_directory_key = ["Extraction"; "Output"; "Directory"]

let { Goptions.get = output_directory } =
  declare_stringopt_option_and_ref ~stage:Summary.Stage.Interp ~value:None
    ~key:output_directory_key ()

let output_directory () =
  match output_directory (), !System.output_directory with
  | Some dir, _ | None, Some dir ->
      (* Ensure that the directory exists *)
      System.mkdir dir;
      dir
  | None, None ->
    let pwd = Sys.getcwd () in
    warn_using_current_directory pwd;
    (* Note: in case of error in the caller of output_directory, the effect of the setting will be undo *)
    set_string_option_value ~stage:Summary.Stage.Interp output_directory_key pwd;
    pwd

(*s Extraction AccessOpaque *)

let access_opaque = my_bool_option "AccessOpaque" true

(*s Extraction AutoInline *)

let auto_inline = my_bool_option "AutoInline" false

(*s Extraction TypeExpand *)

let type_expand = my_bool_option "TypeExpand" true

(*s Extraction KeepSingleton *)

let keep_singleton = my_bool_option "KeepSingleton" false

(*s Extraction Prefix *)

let { Goptions.get = prefix } =
  declare_interpreted_string_option_and_ref
    (fun s ->
      let () = if not (Unicode.is_basic_ascii s && Id.is_valid s) then
        user_err Pp.(str "Extraction prefix must be a valid ASCII identifier.")
      in
      String.capitalize_ascii s)
    Fun.id
    ~key:["Extraction"; "Prefix"]
    ~value:"Rocq"
    ()

(*s Extraction Optimize *)

type opt_flag =
    { opt_kill_dum : bool; (* 1 *)
      opt_fix_fun : bool;   (* 2 *)
      opt_case_iot : bool;  (* 4 *)
      opt_case_idr : bool;  (* 8 *)
      opt_case_idg : bool;  (* 16 *)
      opt_case_cst : bool;  (* 32 *)
      opt_case_fun : bool;  (* 64 *)
      opt_case_app : bool;  (* 128 *)
      opt_let_app : bool;   (* 256 *)
      opt_lin_let : bool;   (* 512 *)
      opt_lin_beta : bool } (* 1024 *)

let kth_digit n k = not (Int.equal (n land (1 lsl k)) 0)

let flag_of_int n =
    { opt_kill_dum = kth_digit n 0;
      opt_fix_fun = kth_digit n 1;
      opt_case_iot = kth_digit n 2;
      opt_case_idr = kth_digit n 3;
      opt_case_idg = kth_digit n 4;
      opt_case_cst = kth_digit n 5;
      opt_case_fun = kth_digit n 6;
      opt_case_app = kth_digit n 7;
      opt_let_app = kth_digit n 8;
      opt_lin_let = kth_digit n 9;
      opt_lin_beta = kth_digit n 10 }

(* For the moment, we allow by default everything except :
   - the type-unsafe optimization [opt_case_idg], which anyway
     cannot be activated currently (cf [Mlutil.branch_as_fun])
   - the linear let and beta reduction [opt_lin_let] and [opt_lin_beta]
     (may lead to complexity blow-up, subsumed by finer reductions
      when inlining recursors).
*)

let int_flag_init = 1 + 2 + 4 + 8 (*+ 16*) + 32 + 64 + 128 + 256 (*+ 512 + 1024*)

let int_flag_ref = ref int_flag_init
let opt_flag_ref = ref (flag_of_int int_flag_init)

let chg_flag n = int_flag_ref := n; opt_flag_ref := flag_of_int n

let optims () = !opt_flag_ref

let () = declare_option ~kind:BoolKind
    ~no_summary:true (* synchronization handled by Extraction Flag *)
    {optstage = Summary.Stage.Interp;
     optdepr = None;
     optkey = ["Extraction"; "Optimize"];
     optread = (fun () -> not (Int.equal !int_flag_ref 0));
     optwrite = (fun b -> chg_flag (if b then int_flag_init else 0))}

let () = declare_int_option
    { optstage = Summary.Stage.Interp;
      optdepr = None;
      optkey = ["Extraction";"Flag"];
      optread = (fun _ -> Some !int_flag_ref);
      optwrite = (function
        | None -> chg_flag 0
        | Some i -> chg_flag (max i 0))}

(* This option controls whether "dummy lambda" are removed when a
   toplevel constant is defined. *)
let { Goptions.get = conservative_types } =
  declare_bool_option_and_ref
    ~key:["Extraction"; "Conservative"; "Types"]
    ~value:false
    ()

(* Allows to print a comment at the beginning of the output files *)
let { Goptions.get = file_comment } =
  declare_string_option_and_ref
    ~key:["Extraction"; "File"; "Comment"]
    ~value:""
    ()

(*s Extraction Lang *)

let lang_ref = Summary.ref Ocaml ~name:"ExtrLang"

let lang () =
  let open Summary.Ref in
  !lang_ref

let extr_lang : lang -> obj =
  let open Summary.Ref in
  declare_object @@ superglobal_object_nodischarge "Extraction Lang"
    ~cache:(fun l -> lang_ref := l)
    ~subst:None

let extraction_language x = Lib.add_leaf (extr_lang x)

(*s Extraction Inline/NoInline *)

let empty_inline_table = (Refset'.empty,Refset'.empty)

let inline_table = Summary.ref empty_inline_table ~name:"ExtrInline"

let to_inline r =
  let open Summary.Ref in
  Refset'.mem r (fst !inline_table)

(* Extension for supporting foreign function call extraction. *)

let empty_foreign_set = Refset'.empty

let foreign_set = Summary.ref empty_foreign_set ~name:"ExtrForeign"

let to_foreign r =
  let open Summary.Ref in
  Refset'.mem r !foreign_set

(* End of Extension for supporting foreign function call extraction. *)

(* Extension for supporting callback registration extraction. *)

(* A map from qualid to string opt (alias) *)
let empty_callback_map = Refmap'.empty

let callback_map = Summary.ref empty_callback_map ~name:"ExtrCallback"

(* End of Extension for supporting callback registration extraction. *)

let to_keep r =
  let open Summary.Ref in
  Refset'.mem r (snd !inline_table)

let add_inline_entries b l =
  let open Summary.Ref in
  let f b = if b then Refset'.add else Refset'.remove in
  let i,k = !inline_table in
  inline_table :=
  (List.fold_right (f b) l i),
  (List.fold_right (f (not b)) l k)

let add_foreign_entries l =
  let open Summary.Ref in
  foreign_set := List.fold_right (Refset'.add) l !foreign_set

(* Adds the qualid_ref and alias opt to the callback_map. *)
let add_callback_entry alias_opt qualid_ref =
  let open Summary.Ref in
  callback_map := Refmap'.add qualid_ref alias_opt !callback_map

(* Registration of operations for rollback. *)

let subst_global s g = { glob = fst (subst_global s g.glob); inst = g.inst }

let inline_extraction : bool * global list -> obj =
  declare_object @@ superglobal_object "Extraction Inline"
    ~cache:(fun (b,l) -> add_inline_entries b l)
    ~subst:(Some (fun (s,(b,l)) -> (b,(List.map (fun x -> subst_global s x) l))))
    ~discharge:(fun x -> Some x)

let foreign_extraction : global list -> obj =
  declare_object @@ superglobal_object "Extraction Foreign"
    ~cache:(fun l -> add_foreign_entries l)
    ~subst:(Some (fun (s,l) -> (List.map (fun x -> subst_global s x) l)))
    ~discharge:(fun x -> Some x)

let callback_extraction : string option * global -> obj =
  declare_object @@ superglobal_object "Extraction Callback"
    ~cache:(fun (alias, x) -> add_callback_entry alias x)
    ~subst:(Some (fun (s,(alias, x)) -> (alias, subst_global s x)))
    ~discharge:(fun x -> Some x)



(* Grammar entries. *)

let mono_global_with_alias qid =
  let gr = Smartlocate.global_with_alias qid in
  let env = Global.env () in
  let inst = Environ.universes_of_global env gr in
  List.map (fun inst -> { glob = gr; inst }) (InfvInst.generate env inst)

let extraction_inline b l =
  let refs = List.map_append mono_global_with_alias l in
  List.iter
    (fun r -> match r.glob with
       | GlobRef.ConstRef _ -> ()
       | _ -> error_constant r) refs;
  Lib.add_leaf (inline_extraction (b,refs))

(* Printing part *)

let print_extraction_inline () =
  let open Summary.Ref in
  let (i,n)= !inline_table in
  let i'= Refset'.filter (function { glob = GlobRef.ConstRef _ } -> true | _ -> false) i in
    (str "Extraction Inline:" ++ fnl () ++
     Refset'.fold
       (fun r p ->
          (p ++ str "  " ++ safe_pr_long_global r ++ fnl ())) i' (mt ()) ++
     str "Extraction NoInline:" ++ fnl () ++
     Refset'.fold
       (fun r p ->
          (p ++ str "  " ++ safe_pr_long_global r ++ fnl ())) n (mt ()))

(* Reset part *)

let reset_inline : unit -> obj =
  let open Summary.Ref in
  declare_object @@ superglobal_object_nodischarge "Reset Extraction Inline"
    ~cache:(fun () -> inline_table := empty_inline_table)
    ~subst:None

let reset_foreign : unit -> obj =
  let open Summary.Ref in
  declare_object @@ superglobal_object_nodischarge "Reset Extraction Foreign"
    ~cache:(fun () -> foreign_set := empty_foreign_set)
    ~subst:None

let reset_callback : unit -> obj =
  let open Summary.Ref in
  declare_object @@ superglobal_object_nodischarge "Reset Extraction Callback"
    ~cache:(fun () -> callback_map := empty_callback_map)
    ~subst:None

let reset_extraction_inline () = Lib.add_leaf (reset_inline ())

let reset_extraction_foreign () = Lib.add_leaf (reset_foreign ())

let reset_extraction_callback () = Lib.add_leaf (reset_callback ())

(*s Extraction Implicit *)

let safe_implicit = my_bool_option "SafeImplicits" true

let err_or_warn_remaining_implicit k =
  if safe_implicit () then
    error_remaining_implicit k
  else
    warning_remaining_implicit k

type int_or_id = ArgInt of int | ArgId of Id.t

let implicits_table = Summary.ref Refmap'.empty ~name:"ExtrImplicit"

let implicits_of_global r =
  let open Summary.Ref in
  try Refmap'.find r !implicits_table with Not_found -> Int.Set.empty

let add_implicits r l =
  let open Summary.Ref in
  let names = argnames_of_global r in
  let n = List.length names in
  let add_arg s = function
    | ArgInt i ->
        if 1 <= i && i <= n then Int.Set.add i s
        else err (int i ++ str " is not a valid argument number for " ++
                  safe_pr_global r)
    | ArgId id ->
       try
         let i = List.index Name.equal (Name id) names in
         Int.Set.add i s
       with Not_found ->
         err (str "No argument " ++ Id.print id ++ str " for " ++
              safe_pr_global r)
  in
  let ints = List.fold_left add_arg Int.Set.empty l in
  implicits_table := Refmap'.add r ints !implicits_table

(* Registration of operations for rollback. *)

let implicit_extraction : global * int_or_id list -> obj =
  declare_object @@ superglobal_object_nodischarge "Extraction Implicit"
    ~cache:(fun (r,l) -> add_implicits r l)
    ~subst:(Some (fun (s,(r,l)) -> (subst_global s r, l)))

(* Grammar entries. *)

let extraction_implicit r l =
  check_inside_section ();
  let r = mono_global_with_alias r in
  List.iter (fun r -> Lib.add_leaf (implicit_extraction (r, l))) r

let string_of_modfile table mp =
  try DirPath.Map.find mp !table.modfile_mps
  with Not_found ->
    let id = Id.of_string (raw_string_of_modfile (MPfile mp)) in
    let id' = next_ident_away id !table.modfile_ids in
    let s' = Id.to_string id' in
    table := { !table with
      modfile_ids = Id.Set.add id' !table.modfile_ids;
      modfile_mps = DirPath.Map.add mp s' !table.modfile_mps;
    };
    s'

(* same as [string_of_modfile], but preserves the capital/uncapital 1st char *)

let file_of_modfile table dp =
  let s0 = Id.to_string (List.hd (DirPath.repr dp)) in
  String.mapi (fun i c -> if i = 0 then s0.[0] else c) (string_of_modfile table dp)

let add_blacklist_entries l =
  let open Summary.Ref in
  blacklist_table :=
    List.fold_right (fun s -> Id.Set.add (Id.of_string (String.capitalize_ascii s)))
      l !blacklist_table

(* Registration of operations for rollback. *)

let blacklist_extraction : string list -> obj =
  declare_object @@ superglobal_object_nodischarge "Extraction Blacklist"
    ~cache:add_blacklist_entries
    ~subst:None

(* Grammar entries. *)

let extraction_blacklist l =
  let l = List.rev l in
  Lib.add_leaf (blacklist_extraction l)

(* Printing part *)

let print_extraction_blacklist () =
  let open Summary.Ref in
  prlist_with_sep fnl Id.print (Id.Set.elements !blacklist_table)

(* Reset part *)

let reset_blacklist : unit -> obj =
  let open Summary.Ref in
  declare_object @@ superglobal_object_nodischarge "Reset Extraction Blacklist"
    ~cache:(fun ()-> blacklist_table := Id.Set.empty)
    ~subst:None

let reset_extraction_blacklist () = Lib.add_leaf (reset_blacklist ())

(*s Extract Constant/Inductive. *)

(* UGLY HACK: to be defined in [extraction.ml] *)
let (use_type_scheme_nb_args, type_scheme_nb_args_hook) = Hook.make ()

let customs = Summary.ref Refmap'.empty ~name:"ExtrCustom"

let add_custom r ids s =
  let open Summary.Ref in
  customs := Refmap'.add r (ids,s) !customs

let is_custom r =
  let open Summary.Ref in
  Refmap'.mem r !customs

let is_inline_custom r = (is_custom r) && (to_inline r)

let is_foreign_custom r = (is_custom r) && (to_foreign r)

let find_callback r =
  let open Summary.Ref in
  Refmap'.find r !callback_map

let find_custom r =
  let open Summary.Ref in
  snd (Refmap'.find r !customs)

let find_type_custom r =
  let open Summary.Ref in
  Refmap'.find r !customs

let custom_matchs = Summary.ref Refmap'.empty ~name:"ExtrCustomMatchs"

let add_custom_match r s =
  let open Summary.Ref in
  custom_matchs := Refmap'.add r s !custom_matchs

let indref_of_match pv =
  if Array.is_empty pv then raise Not_found;
  let (_,pat,_) = pv.(0) in
  match pat with
    | Pusual { glob = GlobRef.ConstructRef (ip,_); inst } -> { glob = GlobRef.IndRef ip; inst }
    | Pcons ({ glob = GlobRef.ConstructRef (ip,_); inst }, _) -> { glob = GlobRef.IndRef ip; inst }
    | _ -> raise Not_found

let is_custom_match pv =
  let open Summary.Ref in
  try Refmap'.mem (indref_of_match pv) !custom_matchs
  with Not_found -> false

let find_custom_match pv =
  let open Summary.Ref in
  Refmap'.find (indref_of_match pv) !custom_matchs

(* Printing entries *)

let print_constref_extractions ref_set val_lookup_f section_str =
  let i'= Refset'.filter (function { glob = GlobRef.ConstRef _ } -> true | _ -> false) ref_set in
      (str section_str ++ fnl () ++
       Refset'.fold
         (fun r p ->
            (p ++ str "  " ++ safe_pr_long_global r ++ str " => \"" ++ str (val_lookup_f r) ++ str "\"" ++ fnl ())) i' (mt ())
       )

let print_extraction_foreign () =
  let open Summary.Ref in
  print_constref_extractions !foreign_set (find_custom) "Extraction Foreign Constant:"

let print_extraction_callback () =
  let open Summary.Ref in
  let keys = Refmap'.domain !callback_map in
  print_constref_extractions keys (fun r ->
    match find_callback r with
     | None   -> "no custom alias"
     | Some s -> s) "Extraction Callbacks for Constants:"

(* Registration of operations for rollback. *)

let in_customs : global * string list * string -> obj =
  declare_object @@ superglobal_object_nodischarge "ML extractions"
    ~cache:(fun (r,ids,s) -> add_custom r ids s)
    ~subst:(Some (fun (s,(r,ids,str)) -> (subst_global s r, ids, str)))

let in_custom_matchs : global * string -> obj =
  declare_object @@ superglobal_object_nodischarge "ML extractions custom matches"
    ~cache:(fun (r,s) -> add_custom_match r s)
    ~subst:(Some (fun (subs,(r,s)) -> (subst_global subs r, s)))

(* Grammar entries. *)

let extract_callback optstr x =
  if lang () != Ocaml then
      CErrors.user_err (Pp.str "Extract Callback is supported only for OCaml extraction.");

  let refs = mono_global_with_alias x in
  List.iter begin fun qualid_ref ->
  match qualid_ref.glob with
      (* Add the alias and qualid_ref to callback extraction.*)
    | GlobRef.ConstRef _ -> Lib.add_leaf (callback_extraction (optstr, qualid_ref))
    | _                  -> error_constant ?loc:x.CAst.loc qualid_ref
  end refs

let extract_constant_generic r ids s arity_handler (is_redef, redef_msg) extr_type =
  check_inside_section ();
  let g = mono_global_with_alias r in
  List.iter begin fun g -> match g.glob with
    | GlobRef.ConstRef kn ->
        let env = Global.env () in
        (* FIXME: substitute ground instance *)
        let typ, _ = Typeops.type_of_global_in_context env (GlobRef.ConstRef kn) in
        let typ = Reduction.whd_all env typ in
        if Reduction.is_arity env typ then arity_handler env typ g;
        if is_redef g then
          CErrors.user_err ((str "The term ") ++ safe_pr_long_global g ++ (str " is already defined as ")
            ++ (str redef_msg) ++ (str " custom constant."));
        Lib.add_leaf (extr_type g);
        Lib.add_leaf (in_customs (g,ids,s));
    | _ -> error_constant ?loc:r.CAst.loc g
  end g

let extract_constant_inline inline r ids s =
  let arity_handler env typ g =
    let nargs = Hook.get use_type_scheme_nb_args env typ in
    if not (Int.equal (List.length ids) nargs) then error_axiom_scheme ?loc:r.CAst.loc g nargs
  in
  extract_constant_generic r ids s (arity_handler) (is_foreign_custom, "foreign") (fun g -> inline_extraction (inline,[g]))

(* const_name : qualid -> replacement : string*)
let extract_constant_foreign r s =
  if lang () != Ocaml then
      CErrors.user_err (Pp.str "Extract Foreign Constant is supported only for OCaml extraction.");
  let arity_handler env typ g =
      CErrors.user_err (Pp.str "Extract Foreign Constant is supported only for functions.")
  in
  extract_constant_generic r [] s (arity_handler) (is_inline_custom, "inline") (fun g -> foreign_extraction [g])


let extract_inductive r s l optstr =
  check_inside_section ();
  let g = mono_global_with_alias r in
  List.iter begin fun g ->
  Dumpglob.add_glob ?loc:r.CAst.loc g.glob;
  match g.glob with
    | GlobRef.IndRef ((kn,i) as ip) ->
        let mib = Global.lookup_mind kn in
        let n = Array.length mib.mind_packets.(i).mind_consnames in
        if not (Int.equal n (List.length l)) then error_nb_cons ();
        Lib.add_leaf (inline_extraction (true,[g]));
        Lib.add_leaf (in_customs (g,[],s));
        Option.iter (fun s -> Lib.add_leaf (in_custom_matchs (g,s)))
          optstr;
        List.iteri
          (fun j s ->
             let g = { glob = GlobRef.ConstructRef (ip,succ j); inst = g.inst } in
             Lib.add_leaf (inline_extraction (true,[g]));
             Lib.add_leaf (in_customs (g,[],s))) l
    | _ -> error_inductive ?loc:r.CAst.loc g
  end g
