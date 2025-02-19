(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Pp
open CErrors
open CAst
open Util
open Names
open Printer
open Goptions
open Libnames
open Vernacexpr
open Locality
open Attributes
open Synterp

module NamedDecl = Context.Named.Declaration

(* Utility functions, at some point they should all disappear and
   instead enviroment/state selection should be done at the Vernac DSL
   level. *)

let get_current_or_global_context ~pstate =
  match pstate with
  | None -> let env = Global.env () in Evd.(from_env env, env)
  | Some p -> Declare.Proof.get_current_context p

let get_goal_or_global_context ~pstate glnum =
  match pstate with
  | None -> let env = Global.env () in Evd.(from_env env, env)
  | Some p -> Declare.Proof.get_goal_context p glnum

let cl_of_qualid = function
  | FunClass -> Coercionops.CL_FUN
  | SortClass -> Coercionops.CL_SORT
  | RefClass r -> ComCoercion.class_of_global (Smartlocate.smart_global ~head:true r)

let scope_class_of_qualid qid =
  Notation.scope_class_of_class (cl_of_qualid qid)

(** Standard attributes for definition-like commands. *)
module DefAttributes = struct
  type t = {
    scope : definition_scope;
    locality : bool option;
    polymorphic : bool;
    program : bool;
    user_warns : Globnames.extended_global_reference UserWarn.with_qf option;
    canonical_instance : bool;
    typing_flags : Declarations.typing_flags option;
    using : Vernacexpr.section_subset_expr option;
    reversible : bool;
    clearbody: bool option;
  }
  (* [locality] is used for [vernac_definition_hook],
     the raw Local/Global attribute is also used to generate [scope].
     [locality] can't be computed back from [scope]
     because [Let Coercion] outside section generates [locality = None]
     but [scope = Global ImportNeedQualified]
     (which is otherwise associated with [locality = Some true]).

     Since [Let] (ie discharge = DoDischarge) does not allow explicit locality
     we could alternatively decide to change the default locality
     of the coercion from out-of-section [Let Coercion].
  *)

  let importability_of_bool = function
    | true -> ImportNeedQualified
    | false -> ImportDefaultBehavior

  let warn_declaration_outside_section =
    CWarnings.create ~name:"declaration-outside-section"
      ~category:CWarnings.CoreCategories.vernacular
      ~default:CWarnings.AsError
      Pp.(fun (unexpected_thing, replacement) ->
          strbrk "Use of " ++ str unexpected_thing
          ++ strbrk " outside sections behaves as " ++ str replacement ++ str ".")

  let scope_of_locality locality_flag discharge deprecated_thing replacement : definition_scope =
    let open Vernacexpr in
    match locality_flag, discharge with
    | Some b, NoDischarge -> Global (importability_of_bool b)
    | None, NoDischarge -> Global ImportDefaultBehavior
    | None, DoDischarge when not (Lib.sections_are_opened ()) ->
      (* If a Let/Variable is defined outside a section, then we consider it as a local definition *)
      warn_declaration_outside_section (deprecated_thing, replacement);
      Global ImportNeedQualified
    | None, DoDischarge -> Discharge
    | Some true, DoDischarge -> CErrors.user_err Pp.(str "Local not allowed in this case")
    | Some false, DoDischarge -> CErrors.user_err Pp.(str "Global not allowed in this case")

  open Attributes
  open Attributes.Notations

  let clearbody = bool_attribute ~name:"clearbody"

  (* [XXX] EJGA: coercion is unused here *)
  let def_attributes_gen ?(coercion=false) ?(discharge=NoDischarge,"","") () =
    let discharge, deprecated_thing, replacement = discharge in
    let clearbody = match discharge with DoDischarge -> clearbody | NoDischarge -> return None in
    (locality ++ user_warns_with_use_globref_instead ++ polymorphic ++ program ++
               canonical_instance ++ typing_flags ++ using ++
               reversible ++ clearbody) >>= fun ((((((((locality, user_warns), polymorphic), program),
           canonical_instance), typing_flags), using),
           reversible), clearbody) ->
      let using = Option.map Proof_using.using_from_string using in
      let reversible = Option.default false reversible in
      let () = if Option.has_some clearbody && not (Lib.sections_are_opened())
        then CErrors.user_err Pp.(str "Cannot use attribute clearbody outside sections.")
      in
      let scope = scope_of_locality locality discharge deprecated_thing replacement in
      return { scope; locality; polymorphic; program; user_warns; canonical_instance; typing_flags; using; reversible; clearbody }

  let parse ?coercion ?discharge f =
    Attributes.parse (def_attributes_gen ?coercion ?discharge ()) f

  let def_attributes = def_attributes_gen ()

end

let with_def_attributes ?coercion ?discharge ~atts f =
  let atts = DefAttributes.parse ?coercion ?discharge atts in
  if atts.DefAttributes.program then Declare.Obls.check_program_libraries ();
  f ~atts

let with_section_locality ~atts f =
  let local = Attributes.(parse locality atts) in
  let section_local = make_section_locality local in
  f ~section_local

(*******************)
(* "Show" commands *)

let show_proof ~pstate =
  (* spiwack: this would probably be cooler with a bit of polishing. *)
  try
    let pstate = Option.get pstate in
    let p = Declare.Proof.get pstate in
    let sigma, _ = Declare.Proof.get_current_context pstate in
    let pprf = Proof.partial_proof p in
    (* In the absence of an environment explicitly attached to the
       proof and on top of which side effects of the proof would be pushed, ,
       we take the global environment which in practise should be a
       superset of the initial environment in which the proof was
       started *)
    let env = Global.env() in
    Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf
  (* We print nothing if there are no goals left *)
  with
  | Proof.NoSuchGoal _
  | Option.IsNone ->
    user_err (str "No goals to show.")

let show_top_evars ~proof =
  (* spiwack: new as of Feb. 2010: shows goal evars in addition to non-goal evars. *)
  let Proof.{goals; sigma} = Proof.data proof in
  let shelf = Evd.shelf sigma in
  let given_up = Evar.Set.elements @@ Evd.given_up sigma in
  pr_evars_int sigma ~shelf ~given_up 1 (Evd.undefined_map sigma)

let show_universes ~proof =
  let Proof.{goals;sigma} = Proof.data proof in
  let ctx = Evd.universe_context_set (Evd.minimize_universes sigma) in
  UState.pr (Evd.ustate sigma) ++ fnl () ++
  v 1 (str "Normalized constraints:" ++ cut() ++
       Univ.pr_universe_context_set (Termops.pr_evd_level sigma) ctx)

(* Simulate the Intro(s) tactic *)
let show_intro ~proof all =
  let open EConstr in
  let Proof.{goals;sigma} = Proof.data proof in
  if not (List.is_empty goals) then begin
    let evi = Evd.find_undefined sigma (List.hd goals) in
    let env = Evd.evar_filtered_env (Global.env ()) evi in
    let l,_= decompose_prod_decls sigma (Termops.strip_outer_cast sigma (Evd.evar_concl evi)) in
    if all then
      let lid = Tactics.find_intro_names env sigma l in
      hov 0 (prlist_with_sep  spc Id.print lid)
    else if not (List.is_empty l) then
      let n = List.last l in
      Id.print (List.hd (Tactics.find_intro_names env sigma [n]))
    else mt ()
  end else mt ()

(** Textual display of a generic "match" template *)

let show_match id =
  let patterns =
    try ComInductive.make_cases (Nametab.global_inductive id)
    with Not_found -> user_err Pp.(str "Unknown inductive type.")
  in
  let pr_branch l =
    str "| " ++ hov 1 (prlist_with_sep spc str l) ++ str " =>"
  in
  v 1 (str "match # with" ++ fnl () ++
       prlist_with_sep fnl pr_branch patterns ++ fnl () ++ str "end" ++ fnl ())

(* "Print" commands *)

let print_loadpath dir =
  let l = Loadpath.get_load_paths () in
  let l = match dir with
  | None -> l
  | Some dir ->
    let filter p = is_dirpath_prefix_of dir (Loadpath.logical p) in
    List.filter filter l
  in
  str "Logical Path / Physical path:" ++ fnl () ++
    prlist_with_sep fnl Loadpath.pp l

let print_libraries () =
  let loaded = Library.loaded_libraries () in
  str"Loaded library files: " ++
  pr_vertical_list DirPath.print loaded


let print_module qid =
  match Nametab.locate_module qid with
  | mp -> Printmod.print_module ~with_body:true mp
  | exception Not_found -> user_err (str"Unknown Module " ++ pr_qualid qid ++ str".")

let print_modtype qid =
  try
    let kn = Nametab.locate_modtype qid in
    Printmod.print_modtype kn
  with Not_found ->
    (* Is there a module of this name ? If yes we display its type *)
    try
      let mp = Nametab.locate_module qid in
      Printmod.print_module ~with_body:false mp
    with Not_found ->
      user_err (str"Unknown Module Type or Module " ++ pr_qualid qid ++ str".")

let print_namespace ~pstate ns =
  let ns = List.rev (Names.DirPath.repr ns) in
  (* [match_dirpath], [match_modulpath] are helpers for [matches]
     which checks whether a constant is in the namespace [ns]. *)
  let rec match_dirpath ns = function
    | [] -> Some ns
    | id::dir ->
        begin match match_dirpath ns dir with
        | Some [] as y -> y
        | Some (a::ns') ->
            if Names.Id.equal a id then Some ns'
            else None
        | None -> None
        end
  in
  let rec match_modulepath ns = function
    | MPbound _ -> None (* Not a proper namespace. *)
    | MPfile dir -> match_dirpath ns (Names.DirPath.repr dir)
    | MPdot (mp,lbl) ->
        let id = Names.Label.to_id lbl in
        begin match match_modulepath ns mp with
        | Some [] as y -> y
        | Some (a::ns') ->
            if Names.Id.equal a id then Some ns'
            else None
        | None -> None
        end
  in
  (* [qualified_minus n mp] returns a list of qualifiers representing
     [mp] except the [n] first (in the concrete syntax order).  The
     idea is that if [mp] matches [ns], then [qualified_minus mp
     (length ns)] will be the correct representation of [mp] assuming
     [ns] is imported. *)
  (* precondition: [mp] matches some namespace of length [n] *)
  let qualified_minus n mp =
    let rec list_of_modulepath = function
      | MPbound _ -> assert false (* MPbound never matches *)
      | MPfile dir -> Names.DirPath.repr dir
      | MPdot (mp,lbl) -> (Names.Label.to_id lbl)::(list_of_modulepath mp)
    in
    snd (Util.List.chop n (List.rev (list_of_modulepath mp)))
  in
  let print_list pr l = prlist_with_sep (fun () -> str".") pr l in
  let print_kn kn =
    let (mp,lbl) = Names.KerName.repr kn in
    let qn = (qualified_minus (List.length ns) mp)@[Names.Label.to_id lbl] in
    print_list Id.print qn
  in
  let print_constant ~pstate k body =
    (* FIXME: universes *)
    let t = body.Declarations.const_type in
    let sigma, env = get_current_or_global_context ~pstate in
    print_kn k ++ str":" ++ spc() ++ Printer.pr_type_env env sigma t
  in
  let matches mp = match match_modulepath ns mp with
  | Some [] -> true
  | _ -> false in
  let constants_in_namespace =
    Environ.fold_constants (fun c body acc ->
        let kn = Constant.user c in
        if matches (KerName.modpath kn)
        then acc++fnl()++hov 2 (print_constant ~pstate kn body)
        else acc)
      (Global.env ()) (str"")
  in
  (print_list Id.print ns)++str":"++fnl()++constants_in_namespace

let print_strategy r =
  let open Conv_oracle in
  let pr_level = function
  | Expand -> str "expand"
  | Level 0 -> str "transparent"
  | Level n -> str "level" ++ spc() ++ int n
  | Opaque -> str "opaque"
  in
  let pr_strategy (ref, lvl) = pr_global ref ++ str " : " ++ pr_level lvl in
  let oracle = Environ.oracle (Global.env ()) in
  match r with
  | None ->
    let fold key lvl (vacc, cacc, pacc) = match key with
    | Conv_oracle.EvalVarRef id -> ((GlobRef.VarRef id, lvl) :: vacc, cacc, pacc)
    | Conv_oracle.EvalConstRef cst -> (vacc, (GlobRef.ConstRef cst, lvl) :: cacc, pacc)
    | Conv_oracle.EvalProjectionRef p -> (vacc, cacc, (GlobRef.ConstRef (Projection.Repr.constant p), lvl) :: pacc)
    in
    let var_lvl, cst_lvl, prj_lvl = fold_strategy fold oracle ([], [], []) in
    let var_msg =
      if List.is_empty var_lvl then mt ()
      else str "Variable strategies" ++ fnl () ++
        hov 0 (prlist_with_sep fnl pr_strategy var_lvl) ++ fnl ()
    in
    let cst_msg =
      if List.is_empty cst_lvl then mt ()
      else str "Constant strategies" ++ fnl () ++
        hov 0 (prlist_with_sep fnl pr_strategy cst_lvl)
    in
    let prj_msg =
      if List.is_empty prj_lvl then mt ()
      else str "Projection strategies" ++ fnl () ++
        hov 0 (prlist_with_sep fnl pr_strategy prj_lvl)
    in
    var_msg ++ cst_msg ++ prj_msg
  | Some r ->
    let r = Smartlocate.smart_global r in
    let key = let open GlobRef in match r with
    | VarRef id -> Evaluable.EvalVarRef id
    | ConstRef cst -> Evaluable.EvalConstRef cst
    | IndRef _ | ConstructRef _ -> user_err Pp.(str "The reference is not unfoldable.")
    in
    let lvl = get_strategy oracle (Evaluable.to_kevaluable key) in
    pr_strategy (r, lvl)

let print_registered () =
  let pr_lib_ref (s,r) =
    pr_global r ++ str " registered as " ++ str s
  in
  hov 0 (prlist_with_sep fnl pr_lib_ref @@ Rocqlib.get_lib_refs ())

let print_registered_schemes () =
  let schemes = DeclareScheme.all_schemes() in
  let pr_one_scheme ind (kind, c) =
    pr_global (ConstRef c) ++ str " registered as " ++ str kind ++ str " for " ++ pr_global (IndRef ind)
  in
  let pr_schemes_of_ind (ind, schemes) =
    prlist_with_sep fnl (pr_one_scheme ind) (CString.Map.bindings schemes)
  in
  hov 0 (prlist_with_sep fnl pr_schemes_of_ind (Indmap.bindings schemes))

let dump_universes output g =
  let open Univ in
  let dump_arc u = function
    | UGraph.Node ltle ->
      Univ.Level.Map.iter (fun v strict ->
          let typ = if strict then Lt else Le in
          output typ u v) ltle;
    | UGraph.Alias v ->
      output Eq u v
  in
  Univ.Level.Map.iter dump_arc g

let dump_universes_gen prl g s =
  let fulls = System.get_output_path s in
  System.mkdir (Filename.dirname fulls);
  let output = open_out fulls in
  let output_constraint, close =
    if Filename.check_suffix s ".dot" || Filename.check_suffix s ".gv" then begin
      (* the lazy unit is to handle errors while printing the first line *)
      let init = lazy (Printf.fprintf output "digraph universes {\n") in
      begin fun kind left right ->
        let () = Lazy.force init in
        match kind with
          | Univ.Lt ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=bold];\n" right left
          | Univ.Le ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=solid];\n" right left
          | Univ.Eq ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=dashed];\n" left right
      end, begin fun () ->
        if Lazy.is_val init then Printf.fprintf output "}\n";
        close_out output
      end
    end else begin
      begin fun kind left right ->
        let kind = match kind with
          | Univ.Lt -> "<"
          | Univ.Le -> "<="
          | Univ.Eq -> "="
        in
        Printf.fprintf output "%s %s %s ;\n" left kind right
      end, (fun () -> close_out output)
    end
  in
  let output_constraint k l r = output_constraint k (prl l) (prl r) in
  try
    dump_universes output_constraint g;
    close ();
    str "Universes written to file \"" ++ str s ++ str "\"."
  with reraise ->
    let reraise = Exninfo.capture reraise in
    close ();
    Exninfo.iraise reraise

let universe_subgraph kept univ =
  let open Univ in
  let parse = function
    | NamedUniv q ->
      begin try Level.make (Nametab.locate_universe q)
      with Not_found ->
        CErrors.user_err ?loc:q.loc Pp.(str "Undeclared universe " ++ pr_qualid q ++ str".")
      end
    | RawUniv { CAst.v = s; loc } ->
      let parts = String.split_on_char '.' s in
      let () = if CList.is_empty parts then CErrors.user_err ?loc Pp.(str "Invalid raw universe.") in
      let i, dp = List.sep_last parts in
      let dp = Libnames.dirpath_of_string (String.concat "." dp) in
      let i = match int_of_string_opt i with
        | Some i -> i
        | None -> CErrors.user_err ?loc Pp.(str "Invalid raw universe.")
      in
      let u = UGlobal.make dp "" i in
      let u = Level.make u in
      begin match UGraph.check_declared_universes univ (Level.Set.singleton u) with
      | Ok () -> u
      | Error _ -> CErrors.user_err ?loc Pp.(str "Undeclared universe " ++ Level.raw_pr u ++ str".")
      end
  in
  let kept = List.fold_left (fun kept q -> Level.Set.add (parse q) kept) Level.Set.empty kept in
  let csts = UGraph.constraints_for ~kept univ in
  let add u newgraph =
    let strict = UGraph.check_constraint univ (Level.set,Lt,u) in
    UGraph.add_universe u ~strict newgraph
  in
  let univ = Level.Set.fold add kept UGraph.initial_universes in
  UGraph.merge_constraints csts univ

let sort_universes g =
  let open Univ in
  let rec normalize u = match Level.Map.find u g with
  | UGraph.Alias u -> normalize u
  | UGraph.Node _ -> u
  in
  let get_next u = match Level.Map.find u g with
  | UGraph.Alias u -> assert false (* nodes are normalized *)
  | UGraph.Node ltle -> ltle
  in
  (* Compute the longest chain of Lt constraints from Set to any universe *)
  let rec traverse accu todo = match todo with
  | [] -> accu
  | (u, n) :: todo ->
    let () = assert (Level.equal (normalize u) u) in
    let n = match Level.Map.find u accu with
    | m -> if m < n then Some n else None
    | exception Not_found -> Some n
    in
    match n with
    | None -> traverse accu todo
    | Some n ->
      let accu = Level.Map.add u n accu in
      let next = get_next u in
      let fold v lt todo =
        let v = normalize v in
        if lt then (v, n + 1) :: todo else (v, n) :: todo
      in
      let todo = Level.Map.fold fold next todo in
      traverse accu todo
  in
  (* Only contains normalized nodes *)
  let levels = traverse Level.Map.empty [normalize Level.set, 0] in
  let max_level = Level.Map.fold (fun _ n accu -> max n accu) levels 0 in
  let dummy_mp = Names.DirPath.make [Names.Id.of_string "Type"] in
  let ulevels = Array.init max_level (fun i -> Level.(make (UGlobal.make dummy_mp "" i))) in
  (* Add the normal universes *)
  let fold (cur, ans) u =
    let ans = Level.Map.add cur (UGraph.Node (Level.Map.singleton u true)) ans in
    (u, ans)
  in
  let _, ans = Array.fold_left fold (Level.set, Level.Map.empty) ulevels in
  let ulevels = Array.cons Level.set ulevels in
  (* Add alias pointers *)
  let fold u _ ans =
    if Level.is_set u then ans
    else
      let n = Level.Map.find (normalize u) levels in
      Level.Map.add u (UGraph.Alias ulevels.(n)) ans
  in
  Level.Map.fold fold g ans

type constraint_source = GlobRef of GlobRef.t | Library of DirPath.t

(* The [edges] fields give the edges of the graph.
   For [u <= v] and [u < v] we have [u |-> v |-> gref, k],
   for [u = v] we have both directions.

   When there are edges with different constraint types between the
   same univs (eg [u < v] and [u <= v]) we keep the strictest one
   (either [<] or [=], NB we can't get both at the same time).
*)
type constraint_sources = {
  edges : (constraint_source * Univ.constraint_type) Univ.Level.Map.t Univ.Level.Map.t;
}

let empty_sources = { edges = Univ.Level.Map.empty }

let mk_sources () =
  let open Univ in
  let srcs = DeclareUniv.constraint_sources () in
  let pick_stricter_constraint (_,k as v) (_,k' as v') =
    match k, k' with
    | Le, Lt | Le, Eq -> v'
    | Lt, Le | Eq, Le -> v
    | Le, Le | Lt, Lt | Eq, Eq ->
      (* same: prefer [v]
         (the older refs are encountered last, and fallback libraries first) *)
      v
    | Lt, Eq | Eq, Lt ->
      (* XXX don't assert in case of type in type? *)
      assert false
  in
  let add_edge_unidirectional (u,k,v) ref edges =
    Level.Map.update u (fun uedges ->
        let uedges = Option.default Level.Map.empty uedges in
        Some (Level.Map.update v (function
            | None -> Some (ref, k)
            | Some v' -> Some (pick_stricter_constraint (ref, k) v'))
            uedges))
      edges
  in
  let add_edge (u,k,v as cst) ref edges =
    let edges = add_edge_unidirectional cst ref edges in
    if k = Eq then add_edge_unidirectional (v,k,u) ref edges else edges
  in
  let edges = Level.Map.empty in
  let edges =
    let libs = Library.loaded_libraries () in
    List.fold_left (fun edges dp ->
        let _, csts = Safe_typing.univs_of_library @@ Library.library_compiled dp in
        Constraints.fold (fun cst edges -> add_edge cst (Library dp) edges)
          csts edges)
      edges libs
  in
  let edges =
    List.fold_left (fun edges (ref,csts) ->
        Constraints.fold (fun cst edges -> add_edge cst (GlobRef ref) edges)
          csts edges)
      edges srcs
  in
  {
    edges;
  }

exception Found of (Univ.constraint_type * Univ.Level.t * constraint_source) list

(* We are looking for a path from [source] to [target].
   If [k] is [Lt] the path must contain at least one [Lt].
   If [k] is [Eq] the path must contain no [Lt].

   [visited] is a map which for each level we have visited says if the
   path had enough [Lt] (always true if the original [k] is [Le] or [Eq]).
*)
let search src ~target k ~source =
  let module UMap = Univ.Level.Map in
  let rec loop visited todo next_todo =
    match todo, next_todo with
    | [], [] -> ()
    | _, _ :: _ -> loop visited next_todo []
    | (source,k,revpath)::todo, _ ->
      let is_visited = match UMap.find_opt source visited with
        | None -> false
        | Some has_enough_lt ->
          if has_enough_lt then true
          else (* original k was [Lt], if current k is also [Lt] we have no new info on this path *)
            k = Univ.Lt
      in
      if is_visited then loop visited todo next_todo
      else
        let visited = UMap.add source (k <> Univ.Lt) visited in
        let visited, next_todo =
          UMap.fold (fun u (ref,k') (visited,next_todo) ->
              if k = Univ.Eq && k' = Univ.Lt then
                (* no point searching for a loop involving [u]  *)
                (UMap.add u true visited, next_todo)
              else
                let next_k = if k = Univ.Lt && k' = Univ.Lt then Univ.Le
                  else k
                in
                let revpath = (k',u,ref) :: revpath in
                if Univ.Level.equal u target && next_k <> Univ.Lt
                then raise (Found revpath)
                else (visited, (u, next_k, revpath) :: next_todo))
            (Option.default UMap.empty (UMap.find_opt source src.edges))
            (visited,next_todo)
        in
        loop visited todo next_todo
  in
  try loop UMap.empty [source,k,[]] []; None
  with Found l -> Some (List.rev l)

let search src (u,k,v) =
  let path = search src ~source:u k ~target:v in
  match path with
  | None -> None
  | Some path ->
    if k = Univ.Eq && not (List.for_all (fun (k',_,_) -> k' = Univ.Eq) path) then
      let path' = search src ~source:v k ~target:u in
      begin match path' with
      | None -> None
      | Some path' -> Some (path @ path')
      end
    else Some path

let find_source (u,k,v as cst) src =
  if Univ.Level.is_set u && k = Univ.Lt then []
  else Option.default [] (search src cst)

let pr_constraint_source = function
  | GlobRef ref -> begin try pr_global ref
      with Not_found ->
        (* global in a module type or functor *)
        GlobRef.print ref
    end
  | Library dp -> str "library " ++ pr_qualid (Nametab.shortest_qualid_of_module (MPfile dp))

let pr_source_path prl u src =
  if CList.is_empty src then mt()
  else
    let pr_rel = function
      | Univ.Eq -> str"=" | Lt -> str"<" | Le -> str"<="
    in
    let pr_one (k,v,ref) =
      spc() ++
      h (pr_rel k ++ surround (str "from " ++ pr_constraint_source ref) ++
         spc() ++ prl v)
    in
    spc() ++ surround (str"because" ++ spc() ++ prl u ++ prlist_with_sep mt pr_one src)

let pr_pmap sep pr map =
  let cmp (u,_) (v,_) = Univ.Level.compare u v in
  Pp.prlist_with_sep sep pr (List.sort cmp (Univ.Level.Map.bindings map))

let pr_arc srcs prl = let open Pp in
  function
  | u, UGraph.Node ltle ->
    if Univ.Level.Map.is_empty ltle then mt ()
    else
      prl u ++ str " " ++
      v 0
        (pr_pmap spc (fun (v, strict) ->
             let k = if strict then Univ.Lt else Univ.Le in
             let src = find_source (u,k,v) srcs in
             hov 2 ((if strict then str "< " else str "<= ") ++ prl v ++ pr_source_path prl u src))
            ltle) ++
      fnl ()
  | u, UGraph.Alias v ->
    let src = find_source (u,Eq,v) srcs in
    prl u  ++ str " = " ++ prl v ++ pr_source_path prl u src ++ fnl ()

let pr_universes srcs prl g = pr_pmap Pp.mt (pr_arc srcs prl) g

let print_universes { sort; subgraph; with_sources; file; } =
  let univ = Global.universes () in
  let univ = match subgraph with
    | None -> univ
    | Some g -> universe_subgraph g univ
  in
  let univ = UGraph.repr univ in
  let univ = if sort then sort_universes univ else univ in
  let pr_remaining =
    if Global.is_joined_environment () then mt ()
    else str"There may remain asynchronous universe constraints"
  in
  let prl = UnivNames.pr_level_with_global_universes in
  begin match file with
  | None ->
    let with_sources = match with_sources, subgraph with
      | Some b, _ -> b
      | _, None -> false
      | _, Some _ -> true
    in
    let srcs = if with_sources then mk_sources () else empty_sources in
    pr_universes srcs prl univ ++ pr_remaining
  | Some s -> dump_universes_gen (fun u -> Pp.string_of_ppcmds (prl u)) univ s
  end

(*********************)
(* "Locate" commands *)

let locate_file f =
  let file = Flags.silently Loadpath.locate_file f in
  str file

let msg_found_library (fulldir, file) =
  if Library.library_is_loaded fulldir then
    hov 0 (DirPath.print fulldir ++ strbrk " has been loaded from file " ++ str file)
  else
    hov 0 (DirPath.print fulldir ++ strbrk " is bound to file " ++ str file)

let print_located_library qid =
  let open Loadpath in
  match locate_qualified_library qid with
  | Ok lib -> msg_found_library lib
  | Error LibUnmappedDir -> raise (UnmappedLibrary (None, qid))
  | Error LibNotFound    -> raise (NotFoundLibrary (None, qid))

let smart_global r =
  let gr = Smartlocate.smart_global r in
  Dumpglob.add_glob ?loc:r.loc gr;
  gr

let qualid_global id = smart_global (make ?loc:id.loc @@ Constrexpr.AN id)

(**********)
(* Syntax *)

let vernac_declare_scope ~module_local sc =
  Metasyntax.declare_scope module_local sc

let vernac_delimiters ~module_local sc action =
  match action with
  | Some lr -> Metasyntax.add_delimiters module_local sc lr
  | None -> Metasyntax.remove_delimiters module_local sc

let vernac_bind_scope ~atts sc cll =
  let module_local, where = Attributes.(parse Notations.(module_locality ++ bind_scope_where) atts) in
  Metasyntax.add_class_scope module_local sc where (List.map scope_class_of_qualid cll)

let vernac_open_close_scope ~section_local (to_open,s) =
  Metasyntax.open_close_scope section_local ~to_open s

let interp_enable_notation_rule on ntn interp flags scope =
  let open Notation in
  let rule = Option.map (function
    | Inl ntn -> Inl (interpret_notation_string ntn)
    | Inr (vars,qid) -> Inr qid) ntn in
  let rec parse_notation_enable_flags all query = function
    | [] -> all, query
    | EnableNotationEntry CAst.{loc;v=entry} :: flags ->
      (match entry with InCustomEntry s when not (Egramrocq.exists_custom_entry s) -> user_err ?loc (str "Unknown custom entry.") | _ -> ());
      parse_notation_enable_flags all { query with notation_entry_pattern = entry :: query.notation_entry_pattern } flags
    | EnableNotationOnly use :: flags ->
      parse_notation_enable_flags all { query with use_pattern = use } flags
    | EnableNotationAll :: flags -> parse_notation_enable_flags true query flags in
  let interp = Option.map (fun c ->
      let vars, recvars =
        match ntn with
        | None ->
          (* We expect the right-hand side to mention "_" in place of proper variables *)
          (* Or should we instead deactivate the check of free variables? *)
          ([], [])
        | Some (Inl ntn) -> let {recvars; mainvars} = decompose_raw_notation ntn in (mainvars, recvars)
        | Some (Inr (vars,qid)) -> (vars, [])
      in
      let ninterp_var_type = Id.Map.of_list (List.map (fun x -> (x, Notation_term.NtnInternTypeAny None)) vars) in
      let ninterp_rec_vars = Id.Map.of_list recvars in
      let nenv = Notation_term.{ ninterp_var_type; ninterp_rec_vars } in
      let (_acvars, ac, _reversibility) = Constrintern.interp_notation_constr (Global.env ()) nenv c in
      ([], ac)) interp in
  let default_notation_enable_pattern = {
    notation_entry_pattern = [];
    interp_rule_key_pattern = rule;
    use_pattern = ParsingAndPrinting;
    scope_pattern = scope;
    interpretation_pattern = interp;
    }
  in
  let all, notation_pattern =
    parse_notation_enable_flags false default_notation_enable_pattern flags in
  on, all, notation_pattern

let vernac_enable_notation ~module_local on rule interp flags scope =
  let () = match rule, interp, scope with
    | None, None, None -> user_err (str "No notation provided.") | _ -> () in
  let on, all, notation_pattern = interp_enable_notation_rule on rule interp flags scope in
  Metasyntax.declare_notation_toggle module_local ~on ~all notation_pattern

(***********)
(* Gallina *)

let check_name_freshness locality {CAst.loc;v=id} : unit =
  (* We check existence here: it's a bit late at Qed time *)
  if Termops.is_section_variable (Global.env ()) id ||
     locality <> Discharge && Nametab.exists_cci (Lib.make_path id) ||
     locality <> Discharge && Nametab.exists_cci (Lib.make_path_except_section id)
  then
    user_err ?loc  (Id.print id ++ str " already exists.")

let vernac_definition_hook ~canonical_instance ~local ~poly ~reversible = let open Decls in function
| Coercion ->
  Some (ComCoercion.add_coercion_hook ~reversible)
| CanonicalStructure ->
  Some (Declare.Hook.(make (fun { S.dref } -> Canonical.declare_canonical_structure ?local dref)))
| SubClass ->
  Some (ComCoercion.add_subclass_hook ~poly ~reversible)
| Definition when canonical_instance ->
  Some (Declare.Hook.(make (fun { S.dref } -> Canonical.declare_canonical_structure ?local dref)))
| Let when canonical_instance ->
  Some (Declare.Hook.(make (fun { S.dref } -> Canonical.declare_canonical_structure dref)))
| _ -> None

let default_thm_id = Id.of_string "Unnamed_thm"

let fresh_name_for_anonymous_theorem () =
  Namegen.next_global_ident_away default_thm_id Id.Set.empty

let vernac_definition_name lid local =
  let lid =
    match lid with
    | { v = Name.Anonymous; loc } ->
         CAst.make ?loc (fresh_name_for_anonymous_theorem ())
    | { v = Name.Name n; loc } -> CAst.make ?loc n in
  check_name_freshness local lid;
  let () =
    if Dumpglob.dump () then
    match local with
    | Discharge -> Dumpglob.dump_definition lid true "var"
    | Global _ -> Dumpglob.dump_definition lid false "def"
  in
  lid.v

let vernac_definition_interactive ~atts (discharge, kind) (lid, udecl) bl t =
  let open DefAttributes in
  let scope, local, poly, program_mode, user_warns, typing_flags, using, clearbody =
    atts.scope, atts.locality, atts.polymorphic, atts.program, atts.user_warns, atts.typing_flags, atts.using, atts.clearbody in
  let canonical_instance, reversible = atts.canonical_instance, atts.reversible in
  let hook = vernac_definition_hook ~canonical_instance ~local ~poly ~reversible kind in
  let name = vernac_definition_name lid scope in
  ComDefinition.do_definition_interactive ?loc:lid.loc ~typing_flags ~program_mode ~name ~poly ~scope ?clearbody:atts.clearbody
    ~kind:(Decls.IsDefinition kind) ?user_warns ?using:atts.using ?hook udecl bl t

let vernac_definition ~atts ~pm (discharge, kind) (lid, udecl) bl red_option c typ_opt =
  let open DefAttributes in
  let scope, local, poly, program_mode, user_warns, typing_flags, using, clearbody =
     atts.scope, atts.locality, atts.polymorphic, atts.program, atts.user_warns, atts.typing_flags, atts.using, atts.clearbody in
  let canonical_instance, reversible = atts.canonical_instance, atts.reversible in
  let hook = vernac_definition_hook ~canonical_instance ~local ~poly kind ~reversible in
  let name = vernac_definition_name lid scope in
  let red_option = match red_option with
    | None -> None
    | Some r ->
      let env = Global.env () in
      let sigma = Evd.from_env env in
      Some (snd (Redexpr.interp_redexp_no_ltac env sigma r)) in
  if program_mode then
    let kind = Decls.IsDefinition kind in
    ComDefinition.do_definition_program ?loc:lid.loc ~pm ~name
      ?clearbody ~poly ?typing_flags ~scope ~kind
      ?user_warns ?using udecl bl red_option c typ_opt ?hook
  else
    let () =
      ComDefinition.do_definition ~name ?loc:lid.loc
        ?clearbody ~poly ?typing_flags ~scope ~kind
        ?user_warns ?using udecl bl red_option c typ_opt ?hook in
    pm

(* NB: pstate argument to use combinators easily *)
let vernac_start_proof ~atts kind l =
  let open DefAttributes in
  if Dumpglob.dump () then
    List.iter (fun ((id, _), _) -> Dumpglob.dump_definition id false "prf") l;
  let scope, local, poly, program_mode, user_warns, typing_flags, using, clearbody =
    atts.scope, atts.locality, atts.polymorphic, atts.program, atts.user_warns, atts.typing_flags, atts.using, atts.clearbody in
  List.iter (fun ((id, _), _) -> check_name_freshness scope id) l;
  match l with
  | [] -> assert false
  | [({v=name; loc},udecl),(bl,typ)] ->
    ComDefinition.do_definition_interactive ?loc
      ~typing_flags ~program_mode ~name ~poly ?clearbody ~scope
      ~kind:(Decls.IsProof kind) ?user_warns ?using udecl bl typ
  | ((lid,_),_) :: _ ->
    let fix = List.map (fun ((fname, univs), (binders, rtype)) ->
        { fname; binders; rtype; body_def = None; univs; notations = []}) l in
    let pm, proof =
      ComFixpoint.do_mutually_recursive ~program_mode ~use_inference_hook:program_mode
        ~scope ?clearbody ~kind:(Decls.IsProof kind) ~poly ?typing_flags
        ?user_warns ?using (CUnknownRecOrder, fix) in
    assert (Option.is_empty pm);
    Option.get proof

let vernac_end_proof ~lemma ~pm = let open Vernacexpr in function
  | Admitted ->
    Declare.Proof.save_admitted ~pm ~proof:lemma
  | Proved (opaque,idopt) ->
    let pm, _ = Declare.Proof.save ~pm ~proof:lemma ~opaque ~idopt
    in pm

let vernac_abort ~lemma:_ ~pm = pm

let vernac_exact_proof ~lemma ~pm c =
  (* spiwack: for simplicity I do not enforce that "Proof proof_term" is
     called only at the beginning of a proof. *)
  let lemma, status = Declare.Proof.by (Tactics.exact_proof c) lemma in
  let pm, _ = Declare.Proof.save ~pm ~proof:lemma ~opaque:Opaque ~idopt:None in
  if not status then Feedback.feedback Feedback.AddedAxiom;
  pm

let vernac_assumption ~atts kind l inline =
  let open DefAttributes in
  let scope, poly, program_mode, using, user_warns =
    atts.scope, atts.polymorphic, atts.program, atts.using, atts.user_warns in
  if Option.has_some using then
    Attributes.unsupported_attributes [CAst.make ("using",VernacFlagEmpty)];
  ComAssumption.do_assumptions ~poly ~program_mode ~scope ~kind ?user_warns ~inline l

let { Goptions.get = is_polymorphic_inductive_cumulativity } =
  declare_bool_option_and_ref
    ~key:["Polymorphic";"Inductive";"Cumulativity"]
    ~value:false
    ()

let polymorphic_cumulative =
  let error_poly_context () =
    user_err
      Pp.(str "The cumulative attribute can only be used in a polymorphic context.");
  in
  let open Attributes in
  let open Notations in
  (* EJGA: this seems redudant with code in attributes.ml *)
  qualify_attribute "universes"
    (bool_attribute ~name:"polymorphic"
     ++ bool_attribute ~name:"cumulative")
  >>= fun (poly,cumul) ->
  match poly, cumul with
  | Some poly, Some cumul ->
     (* Case of Polymorphic|Monomorphic Cumulative|NonCumulative Inductive
        and #[ universes(polymorphic|monomorphic,cumulative|noncumulative) ] Inductive *)
     if poly then return (true, cumul)
     else error_poly_context ()
  | Some poly, None ->
     (* Case of Polymorphic|Monomorphic Inductive
        and #[ universes(polymorphic|monomorphic) ] Inductive *)
     if poly then return (true, is_polymorphic_inductive_cumulativity ())
     else return (false, false)
  | None, Some cumul ->
     (* Case of Cumulative|NonCumulative Inductive *)
     if is_universe_polymorphism () then return (true, cumul)
     else error_poly_context ()
  | None, None ->
     (* Case of Inductive *)
     if is_universe_polymorphism () then
       return (true, is_polymorphic_inductive_cumulativity ())
     else
       return (false, false)

let { Goptions.get = get_uniform_inductive_parameters } =
  Goptions.declare_bool_option_and_ref
    ~key:["Uniform"; "Inductive"; "Parameters"]
    ~value:false
    ()

let should_treat_as_uniform () =
  if get_uniform_inductive_parameters ()
  then ComInductive.UniformParameters
  else ComInductive.NonUniformParameters

(* [XXX] EGJA: several arguments not used here *)
let vernac_record records =
  let map ((is_coercion, name), binders, sort, nameopt, cfs, ido) =
    let idbuild = match nameopt with
    | None -> CAst.map (Nameops.add_prefix "Build_") name
    | Some lid -> lid
    in
    let default_inhabitant_id = Option.map (fun CAst.{v=id} -> id) ido in
    Record.Ast.{ name; is_coercion; binders; cfs; idbuild; sort; default_inhabitant_id }
  in
  let records = List.map map records in
  records

let extract_inductive_udecl (indl:(inductive_expr * notation_declaration list) list) =
  match indl with
  | [] -> assert false
  | (((coe,(id,udecl)),b,c,d),e) :: rest ->
    let rest = List.map (fun (((coe,(id,udecl)),b,c,d),e) ->
        if Option.has_some udecl
        then user_err Pp.(strbrk "Universe binders must be on the first inductive of the block.")
        else (((coe,id),b,c,d),e))
        rest
    in
    udecl, (((coe,id),b,c,d),e) :: rest

let finite_of_kind = let open Declarations in function
  | Inductive_kw -> Finite
  | CoInductive -> CoFinite
  | Variant | Record | Structure | Class _ -> BiFinite

let private_ind =
  let open Attributes in
  let open Notations in
  attribute_of_list
    [ "matching"
    , single_key_parser ~name:"Private (matching) inductive type" ~key:"matching" ()
    ]
  |> qualify_attribute "private"
  >>= function
  | Some () -> return true
  | None -> return false

(** Flag governing use of primitive projections. Disabled by default. *)
let { Goptions.get = primitive_flag } =
  Goptions.declare_bool_option_and_ref
    ~key:["Primitive";"Projections"]
    ~value:false
    ()

let primitive_proj =
  let open Attributes in
  let open Notations in
  qualify_attribute "projections" (bool_attribute ~name:"primitive")
  >>= function
  | Some t -> return t
  | None -> return (primitive_flag ())

let mode_attr =
  let open Attributes in
  let open Notations in
  payload_attribute ?cat:None ~name:"mode" >>= function
  | None -> return None
  | Some mode -> return (Some (Hints.parse_modes mode))

module Preprocessed_Mind_decl = struct
  type flags = ComInductive.flags
  type record = {
    flags : flags;
    udecl : Constrexpr.cumul_univ_decl_expr option;
    primitive_proj : bool;
    kind : Vernacexpr.inductive_kind;
    records : Record.Ast.t list;
  }
  type inductive = {
    flags : flags;
    udecl : Constrexpr.cumul_univ_decl_expr option;
    typing_flags : Declarations.typing_flags option;
    private_ind : bool;
    uniform : ComInductive.uniform_inductive_flag;
    inductives : (Vernacexpr.one_inductive_expr * Vernacexpr.notation_declaration list) list;
  }
  type t =
    | Record of record
    | Inductive of inductive
end

let preprocess_defclass ~atts udecl (id, bl, c, l) =
  let poly, mode =
    Attributes.(parse Notations.(polymorphic ++ mode_attr) atts)
  in
  let flags = {
    (* flags which don't matter for definitional classes *)
    ComInductive.template=None; cumulative=false; finite=BiFinite;
    (* real flags *)
    poly; mode;
  }
  in
  let bl = match bl with
    | bl, None -> bl
    | _ -> CErrors.user_err Pp.(str "Definitional classes do not support the \"|\" syntax.")
  in
  if fst id = AddCoercion then
    user_err Pp.(str "Definitional classes do not support the \">\" syntax.");
  let ((attr, rf_coercion, rf_instance), (lid, ce)) = l in
  let rf_locality = match rf_coercion, rf_instance with
    | AddCoercion, _ | _, BackInstance -> parse option_locality attr
    | _ -> let () = unsupported_attributes attr in Goptions.OptDefault in
  let f = AssumExpr ((make ?loc:lid.loc @@ Name lid.v), [], ce),
          { rf_coercion ; rf_reversible = None ; rf_instance ; rf_priority = None ;
            rf_locality ; rf_notation = [] ; rf_canonical = true } in
  let recordl = [id, bl, c, None, [f], None] in
  let kind = Class true in
  let records = vernac_record recordl in
  Preprocessed_Mind_decl.(Record { flags; udecl; primitive_proj=false; kind; records })

let preprocess_record ~atts udecl kind indl =
  let () = match kind with
    | Variant ->
      user_err (str "The Variant keyword does not support syntax { ... }.")
    | Record | Structure | Class _ | Inductive_kw | CoInductive -> ()
  in
  let check_where ((_, _, _, _), wh) = match wh with
    | [] -> ()
    | _ :: _ ->
      user_err (str "\"where\" clause not supported for records.")
  in
  let () = List.iter check_where indl in
  let hint_mode_attr : Hints.hint_mode list option Attributes.attribute =
    match kind with
    | Class _ -> mode_attr
    | _ -> Notations.return None
  in
  let ((template, (poly, cumulative)), primitive_proj), mode =
    Attributes.(
      parse Notations.(
          template
          ++ polymorphic_cumulative
          ++ primitive_proj ++ hint_mode_attr)
        atts)
  in
  let finite = finite_of_kind kind in
  let flags = { ComInductive.template; cumulative; poly; finite; mode } in
  let parse_record_field_attr (x, f) =
    let attr =
      let rev = match f.rfu_coercion with
        | AddCoercion -> reversible
        | NoCoercion -> Notations.return None in
      let loc = match f.rfu_coercion, f.rfu_instance with
        | AddCoercion, _ | _, BackInstance -> option_locality
        | _ -> Notations.return Goptions.OptDefault in
      Notations.(rev ++ loc ++ canonical_field) in
    let (rf_reversible, rf_locality), rf_canonical = parse attr f.rfu_attrs in
    x,
    { rf_coercion = f.rfu_coercion;
      rf_reversible;
      rf_instance = f.rfu_instance;
      rf_priority = f.rfu_priority;
      rf_locality;
      rf_notation = f.rfu_notation;
      rf_canonical } in
  let unpack ((id, bl, c, decl), _) = match decl with
    | RecordDecl (oc, fs, ido) ->
      let bl = match bl with
        | bl, None -> bl
        | _ -> CErrors.user_err Pp.(str "Records do not support the \"|\" syntax.")
      in
      (id, bl, c, oc, List.map parse_record_field_attr fs, ido)
    | Constructors _ -> assert false (* ruled out above *)
  in
  let kind = match kind with Class _ -> Class false | _ -> kind in
  let recordl = List.map unpack indl in
  let records = vernac_record recordl in
  Preprocessed_Mind_decl.(Record { flags; udecl; primitive_proj; kind; records })

let preprocess_inductive ~atts udecl kind indl =
  let () = match kind with
    | (Record | Structure) ->
      user_err (str "The Record keyword is for types defined using the syntax { ... }.")
    | Class _ ->
      user_err (str "Inductive classes not supported.")
    | Variant | Inductive_kw | CoInductive -> ()
  in
  let check_name ((na, _, _, _), _) = match na with
    | (AddCoercion, _) ->
      user_err (str "Variant types do not handle the \"> Name\" \
                     syntax, which is reserved for records. Use the \":>\" \
                     syntax on constructors instead.")
    | _ -> ()
  in
  let () = List.iter check_name indl in
  let hint_mode_attr : Hints.hint_mode list option Attributes.attribute =
    match kind with
    | Class _ -> mode_attr
    | _ -> Notations.return None
  in
  let (((template, (poly, cumulative)), private_ind), typing_flags), mode =
    Attributes.(
      parse Notations.(
          template
          ++ polymorphic_cumulative
          ++ private_ind ++ typing_flags ++ hint_mode_attr)
        atts)
  in
  let finite = finite_of_kind kind in
  let flags = { ComInductive.template; cumulative; poly; finite; mode } in
  let unpack (((_, id) , bl, c, decl), ntn) = match decl with
    | Constructors l -> (id, bl, c, l), ntn
    | RecordDecl _ -> assert false (* ruled out above *)
  in
  let inductives = List.map unpack indl in
  let uniform = should_treat_as_uniform () in
  Preprocessed_Mind_decl.(Inductive { flags; udecl; typing_flags; private_ind; uniform; inductives })

let preprocess_inductive_decl ~atts kind indl =
  let udecl, indl = extract_inductive_udecl indl in
  let v = match kind, indl with
  | Class _, [ ( id , bl , c , Constructors [l]), [] ] ->
    preprocess_defclass ~atts udecl (id,bl,c,l)
  | _ ->
    if List.for_all (function
        | ((_ , _ , _ , RecordDecl _), _) -> true
        | _ -> false) indl
    then preprocess_record ~atts udecl kind indl
    else if List.for_all (function
        | ((_ , _ , _ , Constructors _), _) -> true
        | _ -> false) indl
    then preprocess_inductive ~atts udecl kind indl
    else user_err (str "Mixed record-inductive definitions are not allowed.")
  in
  indl, v

let dump_inductive indl_for_glob decl =
  let open Preprocessed_Mind_decl in
  if Dumpglob.dump () then begin
    List.iter (fun (((coe,lid), _, _, cstrs), _) ->
        match cstrs with
        | Constructors cstrs ->
          Dumpglob.dump_definition lid false "ind";
          List.iter (fun (_, (lid, _)) ->
              Dumpglob.dump_definition lid false "constr") cstrs
        | _ -> ())
      indl_for_glob;
    match decl with
    | Record { records } ->
      let dump_glob_proj (x, _) = match x with
        | Vernacexpr.(AssumExpr ({loc;v=Name id}, _, _) | DefExpr ({loc;v=Name id}, _, _, _)) ->
          Dumpglob.dump_definition (make ?loc id) false "proj"
        | _ -> () in
      records |> List.iter (fun { Record.Ast.cfs; name } ->
          let () = Dumpglob.dump_definition name false "rec" in
          List.iter dump_glob_proj cfs)
    | Inductive _ -> ()
  end

let vernac_inductive ~atts kind indl =
  let open Preprocessed_Mind_decl in
  let indl_for_glob, decl = preprocess_inductive_decl ~atts kind indl in
  dump_inductive indl_for_glob decl;
  match decl with
  | Record { flags; kind; udecl; primitive_proj; records } ->
    let _ : _ list =
      Record.definition_structure ~flags udecl kind ~primitive_proj records in
    ()
  | Inductive { flags; udecl; typing_flags; private_ind; uniform; inductives } ->
    ComInductive.do_mutual_inductive ~flags udecl inductives ?typing_flags ~private_ind ~uniform

let preprocess_inductive_decl ~atts kind indl =
  snd @@ preprocess_inductive_decl ~atts kind indl

let vernac_fixpoint_common ~atts l =
  if Dumpglob.dump () then
    List.iter (fun { fname } -> Dumpglob.dump_definition fname false "def") l;
  let scope = atts.DefAttributes.scope in
  List.iter (fun { fname } -> check_name_freshness scope fname) l;
  scope

let with_obligations program_mode f pm =
  if program_mode then
    f pm ~program_mode:true
  else
    let pm', proof = f None ~program_mode:false in
    assert (Option.is_empty pm');
    pm, proof

let vernac_fixpoint ~atts ~pm (rec_order,fixl) =
  let open DefAttributes in
  let scope = vernac_fixpoint_common ~atts fixl in
  let poly, typing_flags, program_mode, clearbody, using, user_warns =
    atts.polymorphic, atts.typing_flags, atts.program, atts.clearbody, atts.using, atts.user_warns in
  let () =
    if program_mode then
      (* XXX: Switch to the attribute system and match on ~atts *)
      let opens = List.exists (fun { body_def } -> Option.is_empty body_def) fixl in
      if opens then CErrors.user_err Pp.(str"Program Fixpoint requires a body.") in
  with_obligations program_mode
    (fun pm -> ComFixpoint.do_mutually_recursive ?pm ~scope ?clearbody ~kind:(IsDefinition Fixpoint) ~poly ?typing_flags ?user_warns ?using (CFixRecOrder rec_order, fixl))
    pm

let vernac_cofixpoint_common ~atts l =
  if Dumpglob.dump () then
    List.iter (fun { fname } -> Dumpglob.dump_definition fname false "def") l;
  let scope = atts.DefAttributes.scope in
  List.iter (fun { fname } -> check_name_freshness scope fname) l;
  scope

let vernac_cofixpoint ~pm ~atts cofixl =
  let open DefAttributes in
  let scope = vernac_cofixpoint_common ~atts cofixl in
  let poly, typing_flags, program_mode, clearbody, using, user_warns =
    atts.polymorphic, atts.typing_flags, atts.program, atts.clearbody, atts.using, atts.user_warns in
  let () =
    if program_mode then
      let opens = List.exists (fun { body_def } -> Option.is_empty body_def) cofixl in
      if opens then
        CErrors.user_err Pp.(str"Program CoFixpoint requires a body.") in
  with_obligations program_mode
    (fun pm -> ComFixpoint.do_mutually_recursive ?pm ~scope ?clearbody ~kind:(IsDefinition CoFixpoint) ~poly ?typing_flags ?user_warns ?using (CCoFixRecOrder, cofixl))
    pm

let vernac_scheme l =
  if Dumpglob.dump () then
    List.iter (fun (lid, sch) ->
      Option.iter (fun lid -> Dumpglob.dump_definition lid false "def") lid) l;
  Indschemes.do_scheme (Global.env ()) l

let vernac_scheme_equality ?locmap sch id =
  Indschemes.do_scheme_equality ?locmap sch id

(* [XXX] locmap unused here *)
let vernac_combined_scheme lid l ~locmap =
  (* XXX why does this take idents and not qualids *)
  let l = List.map (fun id -> match qualid_global (qualid_of_ident ?loc:id.loc id.v) with
      | ConstRef c -> c
      | _ -> CErrors.user_err ?loc:id.loc Pp.(Pputils.pr_lident  id ++ str " is not a constant."))
      l
  in
 Indschemes.do_combined_scheme lid l

let vernac_universe ~poly l =
  if poly && not (Lib.sections_are_opened ()) then
    user_err
                 (str"Polymorphic universes can only be declared inside sections, " ++
                  str "use Monomorphic Universe instead.");
  DeclareUniv.do_universe ~poly l

let vernac_constraint ~poly l =
  if poly && not (Lib.sections_are_opened ()) then
    user_err
                 (str"Polymorphic universe constraints can only be declared"
                  ++ str " inside sections, use Monomorphic Constraint instead.");
  DeclareUniv.do_constraint ~poly l

(**********************)
(* Modules            *)

let warn_not_importable = CWarnings.create ~name:"not-importable"
    Pp.(fun c -> str "Cannot import local constant "
                 ++ Printer.pr_constant (Global.env()) c
                 ++ str ", it will be ignored.")

let importable_extended_global_of_path ?loc path =
  match Nametab.extended_global_of_path path with
  | Globnames.TrueGlobal (GlobRef.ConstRef c) as ref ->
    if Declare.is_local_constant c then begin
      warn_not_importable ?loc c;
      None
    end
    else Some ref
  | ref -> Some ref

(* [XXX] n unused here *)
let add_subnames_of ?loc len n ns full_n ref =
  let open GlobRef in
  let add1 r ns = (len, Globnames.TrueGlobal r) :: ns in
  match ref with
  | Globnames.Abbrev _ | Globnames.TrueGlobal (ConstRef _ | ConstructRef _ | VarRef _) ->
    CErrors.user_err ?loc Pp.(str "Only inductive types can be used with Import (...).")
  | Globnames.TrueGlobal (IndRef (mind,i)) ->
    let open Declarations in
    let dp = Libnames.dirpath full_n in
    let mib = Global.lookup_mind mind in
    let mip = mib.mind_packets.(i) in
    let ns = add1 (IndRef (mind,i)) ns in
    let ns = Array.fold_left_i (fun j ns _ -> add1 (ConstructRef ((mind,i),j+1)) ns)
        ns mip.mind_consnames
    in
    List.fold_left (fun ns f ->
        let s = Indrec.elimination_suffix f in
        let n_elim = Id.of_string (Id.to_string mip.mind_typename ^ s) in
        match importable_extended_global_of_path ?loc (Libnames.make_path dp n_elim) with
        | exception Not_found -> ns
        | None -> ns
        | Some ref -> (len, ref) :: ns)
      ns Sorts.all_families

let interp_names m ns =
  let dp_m = Nametab.dirpath_of_module m in
  let ns =
    List.fold_left (fun ns (n,etc) ->
        let len, full_n =
          let dp_n,n = repr_qualid n in
          List.length (DirPath.repr dp_n), make_path (append_dirpath dp_m dp_n) n
        in
        let ref = try importable_extended_global_of_path ?loc:n.loc full_n
          with Not_found ->
            CErrors.user_err ?loc:n.loc
              Pp.(str "Cannot find name " ++ pr_qualid n ++ spc() ++
                  str "in module " ++ pr_qualid (Nametab.shortest_qualid_of_module m) ++ str ".")
        in
        (* TODO dumpglob? *)
        match ref with
        | Some ref ->
          let ns = (len,ref) :: ns in
          if etc then add_subnames_of ?loc:n.loc len n ns full_n ref else ns
        | None -> ns)
      [] ns
  in
  ns

let cache_name (len,n) =
  let open Globnames in
  let open GlobRef in
  match n with
  | Abbrev kn -> Abbreviation.import_abbreviation (len+1) (Nametab.path_of_abbreviation kn) kn
  | TrueGlobal (VarRef _) -> assert false
  | TrueGlobal (ConstRef c) when Declare.is_local_constant c ->
    (* Can happen through functor application *)
    warn_not_importable c
  | TrueGlobal gr ->
    Nametab.(push (Exactly (len+1)) (path_of_global gr) gr)

let cache_names ns = List.iter cache_name ns

let subst_names (subst,ns) = List.Smart.map (on_snd (Globnames.subst_extended_reference subst)) ns

let inExportNames = Libobject.declare_object
    (Libobject.global_object "EXPORTNAMES"
       ~cache:cache_names ~subst:(Some subst_names)
       ~discharge:(fun x -> Some x))

let import_names ~export m ns =
  let ns = interp_names m ns in
  match export with
  | Lib.Export -> Lib.add_leaf (inExportNames ns)
  | Lib.Import -> cache_names ns

let interp_import_cats cats =
  Option.cata
    (fun cats -> Libobject.make_filter ~finite:(not cats.negative) cats.import_cats)
    Libobject.unfiltered
    cats

(* Assumes cats is irrelevant if f is ImportNames *)
let import_module_with_filter ~export cats m f =
  match f with
  | ImportAll ->
    Declaremods.Interp.import_module cats ~export m
  | ImportNames ns -> import_names ~export m ns

let check_no_filter_when_using_cats l =
  List.iter (function
      | _, ImportAll -> ()
      | q, ImportNames _ ->
        CErrors.user_err ?loc:q.loc
          Pp.(str "Cannot combine importing by categories and importing by names."))
    l

let vernac_import (export, cats) mpl =
  let import_mod (CAst.{v = mp; loc},f) =
    try
      let () = Dumpglob.dump_modref ?loc mp "mod" in
      let () = if Modops.is_functor @@ Mod_declarations.mod_type (Global.lookup_module mp)
        then CErrors.user_err ?loc Pp.(str "Cannot import functor " ++ str (ModPath.to_string mp) ++ str".")
      in
      import_module_with_filter ~export cats mp f
    with Not_found ->
        CErrors.user_err ?loc Pp.(str "Cannot find module " ++ str (ModPath.to_string mp) ++ str ".")
  in
  List.iter import_mod mpl

let vernac_declare_module export {loc;v=id} binders_ast mty_ast =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  let mp = Declaremods.Interp.declare_module id binders_ast (Declaremods.Enforce mty_ast) [] in
  Dumpglob.dump_moddef ?loc mp "mod";
  Flags.if_verbose Feedback.msg_info (str "Module " ++ Id.print id ++ str " is declared");
  Option.iter (fun export -> vernac_import export [CAst.make ?loc mp, ImportAll]) export

let vernac_define_module export {loc;v=id} binders_ast argsexport mty_ast_o mexpr_ast_l =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  match mexpr_ast_l with
    | [] ->
       let mp = Declaremods.Interp.start_module export id binders_ast mty_ast_o in
       Dumpglob.dump_moddef ?loc mp "mod";
       Flags.if_verbose Feedback.msg_info
         (str "Interactive Module " ++ Id.print id ++ str " started");
       List.iter
         (fun (export,mp) -> vernac_import export [CAst.make mp, ImportAll])
         argsexport
    | _::_ ->
       let mp =
         Declaremods.Interp.declare_module
           id binders_ast mty_ast_o mexpr_ast_l
       in
       Dumpglob.dump_moddef ?loc mp "mod";
       Flags.if_verbose Feedback.msg_info
         (str "Module " ++ Id.print id ++ str " is defined");
       Option.iter (fun export -> vernac_import export [CAst.make ?loc mp, ImportAll])
         export

let vernac_end_module export {loc;v=id} =
  let mp = Declaremods.Interp.end_module () in
  Dumpglob.dump_modref ?loc mp "mod";
  Flags.if_verbose Feedback.msg_info (str "Module " ++ Id.print id ++ str " is defined");
  Option.iter (fun (export,filter) ->
      Declaremods.Interp.import_module filter ~export mp)
    export

let vernac_declare_module_type {loc;v=id} binders_ast argsexport mty_sign mty_ast_l =
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");

  match mty_ast_l with
    | [] ->
       let mp = Declaremods.Interp.start_modtype id binders_ast mty_sign in
       Dumpglob.dump_moddef ?loc mp "modtype";
       Flags.if_verbose Feedback.msg_info
         (str "Interactive Module Type " ++ Id.print id ++ str " started");
       List.iter
         (fun (export,mp) -> vernac_import export [CAst.make ?loc mp, ImportAll])
         argsexport

    | _ :: _ ->
        let mp = Declaremods.Interp.declare_modtype id binders_ast mty_sign mty_ast_l in
        Dumpglob.dump_moddef ?loc mp "modtype";
        Flags.if_verbose Feedback.msg_info
          (str "Module Type " ++ Id.print id ++ str " is defined")


let vernac_end_modtype {loc;v=id} =
  let mp = Declaremods.Interp.end_modtype () in
  Dumpglob.dump_modref ?loc mp "modtype";
  Flags.if_verbose Feedback.msg_info (str "Module Type " ++ Id.print id ++ str " is defined")

let vernac_include l = Declaremods.Interp.declare_include l

(**********************)
(* Gallina extensions *)

(* Sections *)

let vernac_begin_section ~poly {v=id} =
  Lib.Interp.open_section id;
  (* If there was no polymorphism attribute this just sets the option
     to its current value ie noop. *)
  set_bool_option_value_gen ~locality:OptLocal ["Universe"; "Polymorphism"] poly

let vernac_end_section {CAst.loc; v} =
  Declaremods.Interp.close_section ()

let vernac_name_sec_hyp {v=id} set = Proof_using.name_set id set

(* Dispatcher of the "End" command *)
let msg_of_subsection ss id =
  let kind =
    match ss with
    | Lib.OpenedModule (false,_,_,_) -> "module"
    | Lib.OpenedModule (true,_,_,_) -> "module type"
    | Lib.OpenedSection _ -> "section"
    | _ -> "unknown"
  in
  Pp.str kind ++ spc () ++ Id.print id

let vernac_end_segment ~pm ~proof ({v=id; loc} as lid) =
  let ss = Lib.Interp.find_opening_node ?loc id in
  let what_for = msg_of_subsection ss lid.v in
  if Option.has_some proof then
    CErrors.user_err (Pp.str "Command not supported (Open proofs remain)");
  Declare.Obls.check_solved_obligations ~pm ~what_for;
  match ss with
  | Lib.OpenedModule (false,export,_,_) -> vernac_end_module export lid
  | Lib.OpenedModule (true,_,_,_) -> vernac_end_modtype lid
  | Lib.OpenedSection _ -> vernac_end_section lid
  | _ -> assert false

let vernac_end_segment lid =
  let open Vernactypes in
  typed_vernac { ignore_state with prog=Pop; proof=ReadOpt; }
    (fun {proof; prog} ->
       let () = vernac_end_segment ~pm:prog ~proof lid in
       no_state)

let vernac_begin_segment ~interactive f =
  let open Vernactypes in
  let proof = Proof.(if interactive then Reject else Ignore) in
  let prog = Prog.(if interactive then Push else Ignore) in
  typed_vernac { ignore_state with prog; proof; }
    (fun (_:no_state) ->
       let () = f () in
       no_state)

(* Libraries *)

let warn_require_in_section =
  CWarnings.create ~name:"require-in-section" ~category:CWarnings.CoreCategories.fragile
    (fun () -> strbrk "Use of “Require” inside a section is fragile." ++ spc() ++
               strbrk "It is not recommended to use this functionality in finished proof scripts.")

let vernac_require_interp needed modrefl export qidl =
  if Lib.sections_are_opened () then warn_require_in_section ();
  let () = match export with
    | None -> List.iter (function
        | _, ImportAll -> ()
        | {CAst.loc}, ImportNames _ ->
          CErrors.user_err ?loc Pp.(str "Used an import filter without importing."))
        qidl
    | Some (_,cats) -> if Option.has_some cats then check_no_filter_when_using_cats qidl
  in
  if Dumpglob.dump () then
    List.iter2 (fun ({CAst.loc},_) dp -> Dumpglob.dump_libref ?loc dp "lib") qidl modrefl;
  (* Load *)
  Library.require_library_from_dirpath needed;
  (* Import*)
  Option.iter (fun (export,cats) ->
      let cats = interp_import_cats cats in
      List.iter2 (fun m (_,f) ->
          import_module_with_filter ~export cats (MPfile m) f)
        modrefl qidl)
    export

let vernac_require ~intern from export qidl =
  let needed, modrefl = Synterp.synterp_require ~intern from export qidl in
  vernac_require_interp needed modrefl export qidl

(* Coercions and canonical structures *)

let vernac_canonical ~local r =
  Canonical.declare_canonical_structure ?local (smart_global r)

let vernac_coercion ~atts ref qidst =
  let ref' = smart_global ref in
  match qidst with
  | Some (qids, qidt) ->
     let local, reversible =
       Attributes.parse Notations.(locality ++ reversible) atts in
     let local = enforce_locality local in
     let reversible = Option.default false reversible in
     let target = cl_of_qualid qidt in
     let source = cl_of_qualid qids in
     ComCoercion.try_add_new_coercion_with_target ref' ~local ~reversible
       ~source ~target;
     Flags.if_verbose Feedback.msg_info (pr_global ref' ++ str " is now a coercion")
  | None ->
     match Attributes.parse reversible atts with
     | None -> user_err (str "Expected `: Sourceclass >-> Targetclass`.")
     | Some reversible -> ComCoercion.change_reverse ref' ~reversible

let vernac_identity_coercion ~atts id qids qidt =
  let local, poly = Attributes.(parse Notations.(locality ++ polymorphic) atts) in
  let local = enforce_locality local in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  ComCoercion.try_add_new_identity_coercion id ~local ~poly ~source ~target

(* Type classes *)

let vernac_instance_program ~atts ~pm name bl t props info =
  Dumpglob.dump_constraint (fst name) false "inst";
  let locality, poly =
    Attributes.(parse (Notations.(hint_locality ++ polymorphic))) atts
  in
  let pm, _id = Classes.new_instance_program ~pm ~locality ~poly name bl t props info in
  pm

let vernac_instance_interactive ~atts name bl t info props =
  Dumpglob.dump_constraint (fst name) false "inst";
  let locality, poly =
    Attributes.(parse (Notations.(hint_locality ++ polymorphic))) atts
  in
  let _id, pstate =
    Classes.new_instance_interactive ~locality ~poly name bl t info props in
  pstate

let vernac_instance ~atts name bl t props info =
  Dumpglob.dump_constraint (fst name) false "inst";
  let locality, poly =
    Attributes.(parse (Notations.(hint_locality ++ polymorphic))) atts
  in
  let _id : Id.t =
    Classes.new_instance ~locality ~poly name bl t props info in
  ()

let vernac_declare_instance ~atts id bl inst pri =
  Dumpglob.dump_definition (fst id) false "inst";
  let (program, locality), poly =
    Attributes.(parse (Notations.(program ++ hint_locality ++ polymorphic))) atts
  in
  Classes.declare_new_instance ~program_mode:program ~locality ~poly id bl inst pri

let vernac_context ~atts ctx =
  let program_mode, poly = Attributes.(parse (Notations.(program ++ polymorphic))) atts in
  ComAssumption.do_context ~program_mode ~poly ctx

let vernac_existing_instance ~atts insts =
  let locality = Attributes.parse hint_locality atts in
  List.iter (fun (id, info) ->
      let g = qualid_global id in
      Classes.existing_instance ?loc:id.loc locality g (Some info)) insts

let vernac_existing_class id =
  Record.declare_existing_class (qualid_global id)

(***********)
(* Solving *)

let command_focus = Proof.new_focus_kind "command_focus"
let focus_command_cond = Proof.no_cond command_focus

let vernac_set_end_tac pstate tac =
  let env = Genintern.empty_glob_sign ~strict:true (Global.env ()) in
  let _, tac = Genintern.generic_intern env tac in
  (* TO DO verifier s'il faut pas mettre exist s | TacId s ici*)
  Declare.Proof.set_endline_tactic tac pstate

(************)
(* Commands *)

let vernac_create_hintdb ~module_local id b =
  Hints.create_hint_db module_local id TransparentState.full b

let warn_implicit_core_hint_db =
  CWarnings.create ~name:"implicit-core-hint-db" ~category:Deprecation.Version.v8_10
         (fun () -> strbrk "Adding and removing hints in the core database implicitly is deprecated. "
             ++ strbrk"Please specify a hint database.")

let vernac_remove_hints ~atts dbnames ids =
  let locality = Attributes.(parse hint_locality atts) in
  let dbnames =
    if List.is_empty dbnames then
      (warn_implicit_core_hint_db (); ["core"])
    else dbnames
  in
  Hints.remove_hints ~locality dbnames (List.map Smartlocate.global_with_alias ids)

let vernac_hints ~atts dbnames h =
  let dbnames =
    if List.is_empty dbnames then
      (warn_implicit_core_hint_db (); ["core"])
    else dbnames
  in
  let locality, poly = Attributes.(parse Notations.(hint_locality ++ polymorphic) atts) in
  Hints.add_hints ~locality dbnames (ComHints.interp_hints ~poly h)

let vernac_abbreviation ~atts lid x only_parsing =
  let module_local, user_warns = Attributes.(parse Notations.(module_locality ++ user_warns_with_use_globref_instead) atts) in
  Dumpglob.dump_definition lid false "abbrev";
  Metasyntax.add_abbreviation ~local:module_local user_warns (Global.env()) lid.v x only_parsing

let default_env () = {
  Notation_term.ninterp_var_type = Id.Map.empty;
  ninterp_rec_vars = Id.Map.empty;
}

let vernac_reserve bl =
  let sb_decl = (fun (idl,c) ->
    let env = Global.env() in
    let sigma = Evd.from_env env in
    let t,ctx = Constrintern.interp_type env sigma c in
    let t = Flags.without_option Detyping.print_universes (fun () ->
        Detyping.detype Detyping.Now env (Evd.from_ctx ctx) t)
        ()
    in
    let t,_ = Notation_ops.notation_constr_of_glob_constr (default_env ()) t in
    Reserve.declare_reserved_type idl t)
  in List.iter sb_decl bl

let vernac_generalizable ~local =
  let local = Option.default true local in
  Implicit_quantifiers.declare_generalizable ~local

let allow_sprop_opt_name = ["Allow";"StrictProp"]

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = allow_sprop_opt_name;
      optread  = (fun () -> Global.sprop_allowed());
      optwrite = Global.set_allow_sprop }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Silent"];
      optread  = (fun () -> !Flags.quiet);
      optwrite = ((:=) Flags.quiet) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Implicit";"Arguments"];
      optread  = Impargs.is_implicit_args;
      optwrite = Impargs.make_implicit_args }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Strict";"Implicit"];
      optread  = Impargs.is_strict_implicit_args;
      optwrite = Impargs.make_strict_implicit_args }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Strongly";"Strict";"Implicit"];
      optread  = Impargs.is_strongly_strict_implicit_args;
      optwrite = Impargs.make_strongly_strict_implicit_args }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Contextual";"Implicit"];
      optread  = Impargs.is_contextual_implicit_args;
      optwrite = Impargs.make_contextual_implicit_args }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Reversible";"Pattern";"Implicit"];
      optread  = Impargs.is_reversible_pattern_implicit_args;
      optwrite = Impargs.make_reversible_pattern_implicit_args }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Maximal";"Implicit";"Insertion"];
      optread  = Impargs.is_maximal_implicit_args;
      optwrite = Impargs.make_maximal_implicit_args }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Coercions"];
      optread  = (fun () -> !Constrextern.print_coercions);
      optwrite = (fun b ->  Constrextern.print_coercions := b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Parentheses"];
      optread  = (fun () -> !Constrextern.print_parentheses);
      optwrite = (fun b ->  Constrextern.print_parentheses := b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Implicit"];
      optread  = (fun () -> !Constrextern.print_implicits);
      optwrite = (fun b ->  Constrextern.print_implicits := b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Implicit";"Defensive"];
      optread  = (fun () -> !Constrextern.print_implicits_defensive);
      optwrite = (fun b ->  Constrextern.print_implicits_defensive := b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Projections"];
      optread  = (fun () -> !Constrextern.print_projections);
      optwrite = (fun b ->  Constrextern.print_projections := b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Raw";"Literals"];
      optread  = (fun () -> !Constrextern.print_raw_literal);
      optwrite = (fun b ->  Constrextern.print_raw_literal := b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"All"];
      optread  = (fun () -> !Flags.raw_print);
      optwrite = (fun b -> Flags.raw_print := b) }

let () =
  declare_int_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Inline";"Level"];
      optread  = (fun () -> Some (Flags.get_inline_level ()));
      optwrite = (fun o ->
                   let lev = Option.default Flags.default_inline_level o in
                   Flags.set_inline_level lev) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Kernel"; "Term"; "Sharing"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.share_reduction);
      optwrite = Global.set_share_reduction }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Compact";"Contexts"];
      optread  = (fun () -> Printer.get_compact_context());
      optwrite = (fun b -> Printer.set_compact_context b) }

let () =
  declare_int_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Depth"];
      optread  = Topfmt.get_depth_boxes;
      optwrite = Topfmt.set_depth_boxes }

let () =
  declare_int_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Width"];
      optread  = Topfmt.get_margin;
      optwrite = Topfmt.set_margin }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Universes"];
      optread  = (fun () -> !Constrextern.print_universes);
      optwrite = (fun b -> Constrextern.print_universes:=b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Dump";"Bytecode"];
      optread  = (fun () -> !Vmbytegen.dump_bytecode);
      optwrite = (:=) Vmbytegen.dump_bytecode }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Dump";"Lambda"];
      optread  = (fun () -> !Vmlambda.dump_lambda);
      optwrite = (:=) Vmlambda.dump_lambda }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Parsing";"Explicit"];
      optread  = (fun () -> !Constrintern.parsing_explicit);
      optwrite = (fun b ->  Constrintern.parsing_explicit := b) }

let () =
  let preprocess flags =
    CWarnings.check_unknown_warnings flags;
    CWarnings.normalize_flags_string flags
  in
  declare_append_only_option ~preprocess ~sep:","
    { optstage = Summary.Stage.Synterp;
      optdepr  = None;
      optkey   = ["Warnings"];
      optread  = CWarnings.get_flags;
      optwrite = CWarnings.set_flags }

let () =
  declare_append_only_option ~sep:","
    { optstage = Summary.Stage.Synterp;
      optdepr  = None;
      optkey   = ["Debug"];
      optread  = CDebug.get_flags;
      optwrite = CDebug.set_flags }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Guard"; "Checking"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.check_guarded);
      optwrite = (fun b -> Global.set_check_guarded b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Positivity"; "Checking"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.check_positive);
      optwrite = (fun b -> Global.set_check_positive b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Universe"; "Checking"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.check_universes);
      optwrite = (fun b -> Global.set_check_universes b) }

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Definitional"; "UIP"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.allow_uip);
      optwrite = (fun b -> Global.set_typing_flags
                     {(Global.typing_flags ()) with Declarations.allow_uip = b})
    }

let vernac_set_strategy ~local l =
  let local = Option.default false local in
  let glob_ref r =
    match smart_global r with
      | GlobRef.ConstRef sp ->
          begin
            match Structures.PrimitiveProjections.find_opt sp with
            | None -> Evaluable.EvalConstRef sp
            | Some p -> Evaluable.EvalProjectionRef p
          end
      | GlobRef.VarRef id -> Evaluable.EvalVarRef id
      | _ -> user_err Pp.(str
          "Cannot set an inductive type or a constructor as transparent.") in
  let l = List.map (fun (lev,ql) -> (lev,List.map glob_ref ql)) l in
  Redexpr.set_strategy local l

let vernac_set_opacity ~on_proj_constant ~local (v,l) =
  let local = Option.default true local in
  let glob_ref r =
    match smart_global r with
      | GlobRef.ConstRef sp ->
          begin
            match Structures.PrimitiveProjections.find_opt sp with
            | None when on_proj_constant -> user_err Pp.(str
                "Only compatibility constant opacity can be set this way.")
            | None -> Evaluable.EvalConstRef sp
            | Some _ when on_proj_constant -> Evaluable.EvalConstRef sp
            | Some p -> Evaluable.EvalProjectionRef p
          end
      | GlobRef.VarRef id -> Evaluable.EvalVarRef id
      | _ -> user_err Pp.(str
          "Cannot set an inductive type or a constructor as transparent.") in
  let l = List.map glob_ref l in
  Redexpr.set_strategy local [v,l]

let get_current_context_of_args ~pstate =
  match pstate with
  | None -> fun _ ->
    let env = Global.env () in Evd.(from_env env, env)
  | Some lemma ->
    function
    | Some n -> Declare.Proof.get_goal_context lemma n
    | None -> Declare.Proof.get_current_context lemma

let query_command_selector ?loc = function
  | None -> None
  | Some (Goal_select.SelectNth n) -> Some n
  | _ -> user_err ?loc
      (str "Query commands only support the single numbered goal selector.")

let check_may_eval env sigma redexp rc =
  let gc = Constrintern.intern_unknown_if_term_or_type env sigma rc in
  let sigma, c = Pretyping.understand_tcc env sigma gc in
  let sigma = Evarconv.solve_unif_constraints_with_heuristics env sigma in
  Evarconv.check_problems_are_solved env sigma;
  let sigma = Evd.minimize_universes sigma in
  let (qs, us), csts = Evd.sort_context_set sigma in
  let { Environ.uj_val=c; uj_type=ty; } =
    if Evarutil.has_undefined_evars sigma c
    || List.exists (Context.Named.Declaration.exists (Evarutil.has_undefined_evars sigma))
         (EConstr.named_context env)
    then
      Evarutil.j_nf_evar sigma (Retyping.get_judgment_of env sigma c)
    else
      let env = Evarutil.nf_env_evar sigma env in
      let env = Environ.push_qualities qs env in
      let env = Environ.push_context_set (us,csts) env in
      let c = EConstr.to_constr sigma c in
      (* OK to call kernel which does not support evars *)
      Environ.on_judgment EConstr.of_constr (Arguments_renaming.rename_typing env c)
  in
  let sigma, c = match redexp with
    | None -> sigma, c
    | Some r ->
      let sigma, r = Redexpr.interp_redexp_no_ltac env sigma r in
      let r, _ = Redexpr.reduction_of_red_expr env r in
      let sigma, c = r env sigma c in
      sigma, c
  in
  let pp =
    let evars_of_term c = Evarutil.undefined_evars_of_term sigma c in
    let l = Evar.Set.union (evars_of_term c) (evars_of_term ty) in
    let j = { Environ.uj_val = c; uj_type = Reductionops.nf_betaiota env sigma ty } in
    Prettyp.print_judgment env sigma j ++
    pr_ne_evar_set (fnl () ++ str "where" ++ fnl ()) (mt ()) sigma l
  in
  let hdr = if Option.has_some redexp then str "     = " else mt() in
  hdr ++ pp ++ Printer.pr_universe_ctx_set sigma (us,csts)

let vernac_check_may_eval ~pstate redexp glopt rc =
  let glopt = query_command_selector glopt in
  let sigma, env = get_current_context_of_args ~pstate glopt in
  check_may_eval env sigma redexp rc

let vernac_declare_reduction ~local s r =
  let local = Option.default false local in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Redexpr.declare_red_expr local s (snd (Redexpr.interp_redexp_no_ltac env sigma r))

  (* The same but avoiding the current goal context if any *)
let vernac_global_check c =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let c = Constrintern.intern_constr env sigma c in
  let sigma, c = Pretyping.understand_tcc ~flags:Pretyping.all_and_fail_flags env sigma c in
  let sigma = Evd.collapse_sort_variables sigma in
  let senv = Global.safe_env() in
  let uctx = Evd.universe_context_set sigma in
  let senv = Safe_typing.push_context_set ~strict:false uctx senv in
  let c = EConstr.to_constr sigma c in
  let j = Safe_typing.typing senv c in
  Prettyp.print_safe_judgment j ++
  pr_universe_ctx_set sigma uctx


(* Printing "About" information of a hypothesis of the current goal.
   We only print the type and a small statement to this comes from the
   goal. Precondition: there must be at least one current goal. *)
let print_about_hyp_globs ~pstate ?loc ref_or_by_not udecl glopt =
  let exception NoHyp in
  let open Context.Named.Declaration in
  try
    (* Fallback early to globals *)
    let pstate = match pstate with
      | None -> raise Not_found
      | Some pstate -> pstate
    in
    (* FIXME error on non None udecl if we find the hyp. *)
    let glnumopt = query_command_selector ?loc glopt in
    let pf = Declare.Proof.get pstate in
    let Proof.{goals; sigma} = Proof.data pf in
    let ev, id =
      let open Constrexpr in
      match glnumopt, ref_or_by_not.v with
      | None,AN qid when qualid_is_ident qid -> (* goal number not given, catch any failure *)
        (match List.nth_opt goals 0 with
         | None -> raise NoHyp
         | Some goal -> goal), qualid_basename qid
      | Some n,AN qid when qualid_is_ident qid ->  (* goal number given, catch if wong *)
        (match List.nth_opt goals (n - 1) with
         | None  -> user_err ?loc
                      (str "No such goal: " ++ int n ++ str ".")
         | Some goal -> goal), qualid_basename qid
      | _ , _ -> raise NoHyp in
    let hyps = Evd.evar_filtered_context (Evd.find_undefined sigma ev) in
    let decl = Context.Named.lookup id hyps in
    let natureofid = match decl with
                     | LocalAssum _ -> "Hypothesis"
                     | LocalDef (_,bdy,_) ->"Constant (let in)" in
    let sigma, env = Declare.Proof.get_current_context pstate in
    v 0 (Id.print id ++ str":" ++ pr_econstr_env env sigma (NamedDecl.get_type decl) ++ fnl() ++ fnl()
         ++ str natureofid ++ str " of the goal context.")
  with (* fallback to globals *)
    | NoHyp | Not_found ->
    let sigma, env = get_current_or_global_context ~pstate in
    Prettyp.print_about env sigma ref_or_by_not udecl

let vernac_print =
  let no_state f =
    Vernactypes.(typed_vernac_gen ignore_state (fun _ -> no_state, f ()))
  in
  let with_pstate f =
    let f {Vernactypes.proof} =
      Vernactypes.no_state, f ~pstate:proof
    in
    Vernactypes.(typed_vernac_gen { ignore_state with proof = ReadOpt } f)
  in
  let with_proof_env f = with_pstate (fun ~pstate ->
      let sigma, env = get_current_or_global_context ~pstate in
      f env sigma)
  in
  let with_proof_env_and_opaques f =
    let open Vernactypes in
    let f {proof; opaque_access} =
      let sigma, env = get_current_or_global_context ~pstate:proof in
      no_state, f ~opaque_access env sigma
    in
    typed_vernac_gen { ignore_state with proof = ReadOpt; opaque_access = Access } f
  in
  function
  | PrintTypingFlags -> with_proof_env @@ fun env _sigma -> pr_typing_flags (Environ.typing_flags env)
  | PrintTables -> no_state print_tables
  | PrintFullContext -> with_proof_env Prettyp.print_full_context_typ
  | PrintSectionContext qid -> with_proof_env @@ fun env sigma ->
    Prettyp.print_sec_context_typ env sigma qid
  | PrintInspect n -> with_proof_env @@ fun env sigma ->
    Prettyp.inspect env sigma n
  | PrintGrammar ent -> no_state @@ fun () -> Metasyntax.pr_grammar ent
  | PrintCustomGrammar ent -> no_state @@ fun () -> Metasyntax.pr_custom_grammar ent
  | PrintKeywords -> no_state Metasyntax.pr_keywords
  | PrintLoadPath dir -> (* For compatibility ? *) no_state @@ fun () -> print_loadpath dir
  | PrintLibraries -> no_state print_libraries
  | PrintModule qid -> no_state @@ fun () -> print_module qid
  | PrintModuleType qid -> no_state @@ fun () -> print_modtype qid
  | PrintNamespace ns -> with_pstate @@ print_namespace ns
  | PrintMLLoadPath -> no_state @@ fun () ->
    let paths = Findlib.search_path () in
    v 0 (prlist_with_sep cut str paths )
  | PrintMLModules -> no_state Mltop.print_ml_modules
  | PrintDebugGC -> no_state Mltop.print_gc
  | PrintName (qid,udecl) -> with_proof_env_and_opaques @@ fun ~opaque_access env sigma ->
    Prettyp.print_name opaque_access env sigma qid udecl
  | PrintGraph -> no_state Prettyp.print_graph
  | PrintClasses -> no_state Prettyp.print_classes
  | PrintTypeclasses -> no_state Prettyp.print_typeclasses
  | PrintInstances c -> no_state @@ fun () -> Prettyp.print_instances (smart_global c)
  | PrintCoercions -> no_state Prettyp.print_coercions
  | PrintNotation (entry, ntnstr) -> with_proof_env @@ fun env sigma ->
    Prettyp.print_notation env sigma entry ntnstr
  | PrintCoercionPaths (cls,clt) -> no_state @@ fun () ->
    Prettyp.print_coercion_paths (cl_of_qualid cls) (cl_of_qualid clt)
  | PrintCanonicalConversions qids -> with_proof_env @@ fun env sigma ->
    let grefs = List.map Smartlocate.smart_global qids in
    Prettyp.print_canonical_projections env sigma grefs
  | PrintUniverses prunivs -> no_state @@ fun ()->
    print_universes prunivs
  | PrintHint r -> with_proof_env @@ fun env sigma ->
    Hints.pr_hint_ref env sigma (smart_global r)
  | PrintHintGoal -> with_pstate @@ fun ~pstate ->
    begin match pstate with
    | Some pstate ->
      let pf = Declare.Proof.get pstate in
      Hints.pr_applicable_hint pf
    | None ->
      str "No proof in progress"
    end
  | PrintHintDbName s -> with_proof_env @@ fun env sigma ->
    Hints.pr_hint_db_by_name env sigma s
  | PrintHintDb -> with_proof_env @@ fun env sigma ->
    Hints.pr_searchtable env sigma
  | PrintScopes -> with_proof_env @@ fun env sigma ->
    Notation.pr_scopes (Constrextern.without_symbols (pr_glob_constr_env env sigma))
  | PrintScope s -> with_proof_env @@ fun env sigma ->
    Notation.pr_scope (Constrextern.without_symbols (pr_glob_constr_env env sigma)) s
  | PrintVisibility s -> with_proof_env @@ fun env sigma ->
    Notation.pr_visibility (Constrextern.without_symbols (pr_glob_constr_env env sigma)) s
  | PrintAbout (ref_or_by_not,udecl,glnumopt) -> with_pstate @@
    print_about_hyp_globs ref_or_by_not udecl glnumopt
  | PrintImplicit qid -> with_proof_env @@ fun env _sigma ->
    Prettyp.print_impargs env (smart_global qid)
  | PrintAssumptions (o,t,r) -> with_proof_env_and_opaques @@ fun ~opaque_access env sigma ->
    (* Prints all the axioms and section variables used by a term *)
    let gr = smart_global r in
    let cstr, _ = UnivGen.fresh_global_instance env gr in
    let st = Conv_oracle.get_transp_state (Environ.oracle env) in
    let nassums =
      Assumptions.assumptions opaque_access st ~add_opaque:o ~add_transparent:t gr cstr in
    Printer.pr_assumptionset env sigma nassums
  | PrintStrategy r -> no_state @@ fun () -> print_strategy r
  | PrintRegistered -> no_state print_registered
  | PrintRegisteredSchemes -> no_state print_registered_schemes

let vernac_search ~pstate ~atts s gopt r =
  let open ComSearch in
  let gopt = query_command_selector gopt in
  let sigma, env =
    match gopt with
    (* 1st goal by default if it exists, otherwise no goal at all *)
    | None -> begin
        try get_goal_or_global_context ~pstate 1
        with Proof.NoSuchGoal _ -> let env = Global.env () in Evd.from_env env, env
      end
    (* if goal selector is given and wrong, then let exceptions be raised. *)
    | Some g -> get_goal_or_global_context ~pstate g
  in
  interp_search env sigma s r

let vernac_locate ~pstate query =
  let open Constrexpr in
  let sigma, env = get_current_or_global_context ~pstate in
  match query with
  | LocateAny {v=AN qid}  -> Prettyp.print_located_qualid env qid
  | LocateTerm {v=AN qid} -> Prettyp.print_located_term env qid
  | LocateAny {v=ByNotation (ntn, sc)} (* TODO : handle Ltac notations *)
  | LocateTerm {v=ByNotation (ntn, sc)} ->
    Notation.locate_notation
      (Constrextern.without_symbols (pr_glob_constr_env env sigma)) ntn sc
  | LocateLibrary qid -> print_located_library qid
  | LocateModule qid -> Prettyp.print_located_module env qid
  | LocateOther (s, qid) -> Prettyp.print_located_other env s qid
  | LocateFile f -> locate_file f

let warn_unknown_scheme_kind = CWarnings.create ~name:"unknown-scheme-kind"
    Pp.(fun sk -> str "Unknown scheme kind " ++ Libnames.pr_qualid sk ++ str ".")

let vernac_register ~atts qid r =
  let gr = Smartlocate.global_with_alias qid in
  match r with
  | RegisterInline ->
    unsupported_attributes atts;
    begin match gr with
    | GlobRef.ConstRef c -> Global.register_inline c
    | _ -> CErrors.user_err ?loc:qid.loc (Pp.str "Register Inline: expecting a constant.")
    end
  | RegisterCoqlib n ->
    let ns, id = Libnames.repr_qualid n in
    if DirPath.equal (dirpath_of_string "kernel") ns then begin
      unsupported_attributes atts;
      if Lib.sections_are_opened () then
        user_err Pp.(str "Registering a kernel type is not allowed in sections.");
      let CPrimitives.PIE pind = match Id.to_string id with
        | "ind_bool" -> CPrimitives.(PIE PIT_bool)
        | "ind_carry" -> CPrimitives.(PIE PIT_carry)
        | "ind_pair" -> CPrimitives.(PIE PIT_pair)
        | "ind_cmp" -> CPrimitives.(PIE PIT_cmp)
        | "ind_f_cmp" -> CPrimitives.(PIE PIT_f_cmp)
        | "ind_f_class" -> CPrimitives.(PIE PIT_f_class)
        | k -> CErrors.user_err ?loc:n.loc Pp.(str "Register: unknown identifier “" ++ str k ++ str "” in the \"kernel\" namespace.")
      in
      match gr with
      | GlobRef.IndRef ind -> Global.register_inductive ind pind
      | _ -> CErrors.user_err ?loc:qid.loc (Pp.str "Register in kernel: expecting an inductive type.")
    end
    else
      let local = Attributes.parse hint_locality_default_superglobal atts in
      Rocqlib.register_ref local (Libnames.string_of_qualid n) gr
  | RegisterScheme { inductive; scheme_kind } ->
    let local = Attributes.parse hint_locality_default_superglobal atts in
    let gr = match gr with
      | ConstRef c -> c
      | _ -> CErrors.user_err ?loc:qid.loc Pp.(str "Register Scheme: expecing a constant.")
    in
    let scheme_kind_s = Libnames.string_of_qualid scheme_kind in
    let () = if not (Ind_tables.is_declared_scheme_object scheme_kind_s) then
        warn_unknown_scheme_kind ?loc:scheme_kind.loc scheme_kind
    in
    let ind = Smartlocate.global_inductive_with_alias inductive in
    Dumpglob.add_glob ?loc:inductive.loc (IndRef ind);
    DeclareScheme.declare_scheme local scheme_kind_s (ind,gr)

let vernac_library_attributes atts =
  if Global.is_curmod_library () && not (Lib.sections_are_opened ()) then
    let user_warns = Attributes.parse user_warns atts in
    let user_warns = Option.default UserWarn.empty user_warns in
    Lib.Synterp.declare_info user_warns
  else
    user_err (Pp.str "A library attribute should be at toplevel of the library.")

(********************)
(* Proof management *)

let vernac_focus ~pstate gln =
  Declare.Proof.map ~f:(fun p ->
    match gln with
      | None -> Proof.focus focus_command_cond () 1 p
      | Some 0 ->
         user_err Pp.(str "Invalid goal number: 0. Goal numbering starts with 1.")
      | Some n ->
         Proof.focus focus_command_cond () n p)
    pstate

  (* Unfocuses one step in the focus stack. *)
let vernac_unfocus ~pstate =
  Declare.Proof.map
    ~f:(fun p -> Proof.unfocus command_focus p ())
    pstate

(* Checks that a proof is fully unfocused. Raises an error if not. *)
let vernac_unfocused ~pstate =
  let p = Declare.Proof.get pstate in
  if Proof.unfocused p then
    str"The proof is indeed fully unfocused."
  else
    user_err Pp.(str "The proof is not fully unfocused.")

(* "{" focuses on the first goal, "n: {" focuses on the n-th goal
    "}" unfocuses, provided that the proof of the goal has been completed.
*)
let subproof_kind = Proof.new_focus_kind "subproof"
let subproof_cond = Proof.done_cond subproof_kind

let vernac_subproof gln ~pstate =
  Declare.Proof.map ~f:(fun p ->
    match gln with
    | None -> Proof.focus subproof_cond () 1 p
    | Some (Goal_select.SelectNth n) -> Proof.focus subproof_cond () n p
    | Some (Goal_select.SelectId id) -> Proof.focus_id subproof_cond () id p
    | _ -> user_err
             (str "Brackets do not support multi-goal selectors."))
    pstate

let vernac_end_subproof ~pstate =
  Declare.Proof.map ~f:(fun p ->
      Proof.unfocus subproof_kind p ())
    pstate

let vernac_bullet (bullet : Proof_bullet.t) ~pstate =
  Declare.Proof.map ~f:(fun p ->
    Proof_bullet.put p bullet) pstate

(* Stack is needed due to show proof names, should deprecate / remove
   and take pstate *)
let vernac_show ~pstate =
  match pstate with
  (* Show functions that don't require a proof state *)
  | None ->
    begin function
      | ShowProof -> show_proof ~pstate:None
      | ShowMatch id -> show_match id
      | _ ->
        user_err (str "This command requires an open proof.")
    end
  (* Show functions that require a proof state *)
  | Some pstate ->
    let proof = Declare.Proof.get pstate in
    begin function
    | ShowGoal goalref ->
      begin match goalref with
        | OpenSubgoals -> pr_open_subgoals proof
        | NthGoal n -> pr_nth_open_subgoal ~proof n
        | GoalId id -> pr_goal_by_id ~proof id
      end
    | ShowExistentials -> show_top_evars ~proof
    | ShowUniverses -> show_universes ~proof
    (* Deprecate *)
    | ShowProofNames ->
      Id.print (Declare.Proof.get_name pstate)
    | ShowIntros all -> show_intro ~proof all
    | ShowProof -> show_proof ~pstate:(Some pstate)
    | ShowMatch id -> show_match id
    end

let vernac_check_guard ~pstate =
  Declare.Proof.control_only_guard pstate;
  str "The condition holds up to here."

let vernac_validate_proof ~pstate =
  let pts = Declare.Proof.get pstate in
  let { Proof.entry; Proof.sigma } = Proof.data pts in
  let hyps, pfterm, pftyp = List.hd (Proofview.initial_goals entry) in
  (* XXX can the initial hyps contain something broken? For now assume they're correct.
     NB: in the "Lemma foo args : bla." case the args are part of the
     term and intro'd after the proof is opened. Only the section
     variables are in the hyps. *)
  let env = Environ.reset_with_named_context hyps (Global.env ()) in
  let sigma = Evarconv.solve_unif_constraints_with_heuristics env sigma in
  let sigma' = Typing.check env sigma pfterm pftyp in
  let evar_issues =
    (* Use Evar.Map.merge as a kind of for_all2 *)
    Evar.Map.merge (fun e orig now -> match orig, now with
        | None, None -> assert false
        | Some _, Some _ -> None (* assume same *)
        | Some evi, None ->
          let EvarInfo evi' = Evd.find sigma' e in
          let body = match Evd.evar_body evi' with
            | Evar_empty -> assert false
            | Evar_defined body -> body
          in
          Some
            Pp.(str "Evar " ++ Printer.pr_evar sigma (e, evi)
                ++ spc() ++ str "was inferred by unification to be" ++ spc()
                ++ pr_econstr_env (Evd.evar_env env evi') sigma' body)
        | None, Some _ -> (* ignore new evar *)
          assert (not (Evd.is_defined sigma e));
          None
      )
      (Evd.undefined_map sigma)
      (Evd.undefined_map sigma')
  in
  (* TODO check ustate *)

  if Evar.Map.is_empty evar_issues then
    str "No issues found."
  else prlist_with_sep fnl snd (Evar.Map.bindings evar_issues)

let vernac_proof pstate tac using =
  let is_let = match Declare.Proof.definition_scope pstate with
    | Discharge -> true
    | Global _ -> false
  in
  let using = if not is_let then Option.append using (Proof_using.get_default_proof_using ())
    else
      let () = if Option.has_some using
        then CErrors.user_err Pp.(str "Let does not support Proof using.")
      in
      None
  in
  let tacs = if Option.is_empty tac then "tac:no" else "tac:yes" in
  let usings = if Option.is_empty using then "using:no" else "using:yes" in
  Aux_file.record_in_aux_at "VernacProof" (tacs^" "^usings);
  let pstate = Option.fold_left vernac_set_end_tac pstate tac in
  let set_proof_using ps using = Declare.Proof.set_proof_using ps using |> snd in
  let pstate = Option.fold_left set_proof_using pstate using in
  pstate

let translate_vernac_synterp ?loc ~atts v = let open Vernactypes in match v with
  | EVernacNotation { local; decl } ->
    vtdefault(fun () -> Metasyntax.add_notation_interpretation ~local (Global.env()) decl)

  | EVernacDefineModule (export,lid,bl,argsexport,mtys,mexprl) ->
    let i () =
      unsupported_attributes atts;
      vernac_define_module export lid bl argsexport mtys mexprl in
    (* XXX: We should investigate if eventually this should be made
       VtNoProof in all cases. *)
    vernac_begin_segment ~interactive:(List.is_empty mexprl) i

  | EVernacDeclareModuleType (lid,bl,argsexport,mtys,exprl) ->
    vernac_begin_segment ~interactive:(List.is_empty exprl) (fun () ->
        unsupported_attributes atts;
        vernac_declare_module_type lid bl argsexport mtys exprl)

  (* Modules *)
  | EVernacDeclareModule (export,lid,bl,mty) ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_declare_module export lid bl mty)

  | EVernacInclude in_asts ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_include in_asts)

  (* Gallina extensions *)
  | EVernacBeginSection lid ->
    vernac_begin_segment ~interactive:true (fun () ->
        vernac_begin_section ~poly:(only_polymorphism atts) lid)

  | EVernacEndSegment lid ->
    unsupported_attributes atts;
    vernac_end_segment lid

  | EVernacRequire (needed, modrefl, export, qidl) ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_require_interp needed modrefl export qidl)
  | EVernacImport (export,mpl) ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_import export mpl)

  | EVernacSetOption { export; key; value } ->
    vtdefault(fun () ->
    let atts = if export then CAst.make ?loc ("export", VernacFlagEmpty) :: atts else atts in
    Vernacoptions.vernac_set_option ~locality:(parse option_locality atts) ~stage:Summary.Stage.Interp key value)

  | EVernacNoop ->
    vtdefault(fun () -> ())

  | EVernacLoad _ ->
    anomaly (str "type_vernac")

  (* Extensions *)
  | EVernacExtend f -> f

let translate_pure_vernac ?loc ~atts v = let open Vernactypes in match v with
  | VernacAbortAll
  | VernacRestart
  | VernacUndo _
  | VernacUndoTo _
  | VernacResetName _
  | VernacResetInitial
  | VernacBack _ ->
    anomaly (str "type_vernac")

  (* Syntax *)
  | VernacDeclareScope sc ->
    vtdefault(fun () -> with_module_locality ~atts vernac_declare_scope sc)
  | VernacDelimiters (sc,lr) ->
    vtdefault(fun () -> with_module_locality ~atts vernac_delimiters sc lr)
  | VernacBindScope (sc,rl) ->
    vtdefault(fun () -> vernac_bind_scope ~atts sc rl)
  | VernacOpenCloseScope (b, s) ->
    vtdefault(fun () -> with_section_locality ~atts vernac_open_close_scope (b,s))
  | VernacEnableNotation (on,rule,interp,flags,scope) ->
    vtdefault(fun () -> with_module_locality ~atts vernac_enable_notation on rule interp flags scope)

  (* Gallina *)

  | VernacDefinition ((discharge,kind as dkind),lid,DefineBody (bl,red_option,c,typ)) ->
    let coercion = match kind with Decls.Coercion -> true | _ -> false in
    vtmodifyprogram (fun ~pm ->
      with_def_attributes ~coercion ~discharge:(discharge, "\"Let\"", "\"#[local] Definition\"") ~atts
       vernac_definition ~pm dkind lid bl red_option c typ)
  | VernacDefinition ((discharge,kind as dkind),lid,ProveBody(bl,typ)) ->
    let coercion = match kind with Decls.Coercion -> true | _ -> false in
    vtopenproof(fun () ->
      with_def_attributes ~coercion ~discharge:(discharge, "\"Let\"", "\"#[local] Definition\"") ~atts
       vernac_definition_interactive dkind lid bl typ)

  | VernacStartTheoremProof (k,l) ->
    vtopenproof(fun () -> with_def_attributes ~atts vernac_start_proof k l)
  | VernacExactProof c ->
    vtcloseproof (fun ~lemma ->
        unsupported_attributes atts;
        vernac_exact_proof ~lemma c)

  | VernacAssumption ((discharge,kind),nl,l) ->
    vtdefault(fun () ->
        with_def_attributes ~atts
          ~discharge:(discharge,
                      "\"Variable\" or \"Hypothesis\"",
                      "\"#[local] Parameter\" or \"#[local] Axiom\"")
          vernac_assumption kind l nl)

  | VernacSymbol l ->
    vtdefault (fun () ->
      let unfold_fix, poly =
        Attributes.(parse Notations.(unfold_fix ++ polymorphic)) atts
      in
        ComRewriteRule.do_symbols ~poly ~unfold_fix l)

  | VernacInductive (finite, l) ->
    vtdefault(fun () -> vernac_inductive ~atts finite l)

  | VernacFixpoint (discharge, l) ->
    let opens = List.exists (fun { body_def } -> Option.is_empty body_def) (snd l) in
    let discharge = discharge, "\"Let Fixpoint\"", "\"#[local] Fixpoint\"" in
    (if opens then
      vtopenproof (fun () ->
        let pm, proof = with_def_attributes ~discharge ~atts (vernac_fixpoint ~pm:None) l in
        assert (Option.is_empty pm);
        Option.get proof)
    else
      vtmodifyprogram (fun ~pm ->
        let pm, proof = with_def_attributes ~discharge ~atts (vernac_fixpoint ~pm:(Some pm)) l in
        assert (Option.is_empty proof);
        Option.get pm))

  | VernacCoFixpoint (discharge, l) ->
    let opens = List.exists (fun { body_def } -> Option.is_empty body_def) l in
    let discharge = discharge,  "\"Let CoFixpoint\"", "\"#[local] CoFixpoint\"" in
    (if opens then
      vtopenproof (fun () ->
        let pm, proof = with_def_attributes ~discharge ~atts (vernac_cofixpoint ~pm:None) l in
        assert (Option.is_empty pm);
        Option.get proof)
    else
      vtmodifyprogram (fun ~pm ->
        let pm, proof = with_def_attributes ~discharge ~atts (vernac_cofixpoint ~pm:(Some pm)) l in
        assert (Option.is_empty proof);
        Option.get pm))

  | VernacScheme l ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_scheme l)
  | VernacSchemeEquality (sch,id) ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_scheme_equality sch id ~locmap:(Ind_tables.Locmap.default loc))
  | VernacCombinedScheme (id, l) ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_combined_scheme id l ~locmap:(Ind_tables.Locmap.default loc))
  | VernacUniverse l ->
    vtdefault(fun () -> vernac_universe ~poly:(only_polymorphism atts) l)

  | VernacConstraint l ->
    vtdefault(fun () -> vernac_constraint ~poly:(only_polymorphism atts) l)

  | VernacAddRewRule (id, c) ->
    vtdefault (fun () ->
        unsupported_attributes atts;
        ComRewriteRule.do_rules id.v c)

  (* Gallina extensions *)

  | VernacNameSectionHypSet (lid, set) ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_name_sec_hyp lid set)

  | VernacCanonical qid ->
    vtdefault(fun () ->
        vernac_canonical ~local:(only_locality atts) qid)

  | VernacCoercion (r,st) ->
    vtdefault(fun () -> vernac_coercion ~atts r st)

  | VernacIdentityCoercion ({v=id},s,t) ->
    vtdefault(fun () -> vernac_identity_coercion ~atts id s t)

  (* Type classes *)
  | VernacInstance (name, bl, t, props, info) ->
    let atts, program = Attributes.(parse_with_extra program) atts in
    if program then
      vtmodifyprogram (vernac_instance_program ~atts name bl t props info)
    else begin match props with
    | None ->
       vtopenproof (fun () ->
        vernac_instance_interactive ~atts name bl t info None)
    | Some props ->
      let atts, refine = Attributes.parse_with_extra Classes.refine_att atts in
      if refine then
        vtopenproof (fun () ->
          vernac_instance_interactive ~atts name bl t info (Some props))
      else
        vtdefault (fun () ->
          vernac_instance ~atts name bl t props info)
    end

  | VernacDeclareInstance (id, bl, inst, info) ->
    vtdefault(fun () -> vernac_declare_instance ~atts id bl inst info)
  | VernacContext sup ->
    vtdefault(fun () -> vernac_context ~atts sup)
  | VernacExistingInstance insts ->
    vtdefault(fun () -> vernac_existing_instance ~atts insts)

  | VernacExistingClass id ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_existing_class id)

  (* Commands *)
  | VernacCreateHintDb (dbname,b) ->
    vtdefault(fun () ->
        with_module_locality ~atts vernac_create_hintdb dbname b)

  | VernacRemoveHints (dbnames,ids) ->
    vtdefault(fun () ->
        vernac_remove_hints ~atts dbnames ids)

  | VernacHints (dbnames,hints) ->
    vtdefault(fun () ->
        vernac_hints ~atts dbnames hints)

  | VernacSyntacticDefinition (id,c,b) ->
     vtdefault(fun () -> vernac_abbreviation ~atts id c b)

  | VernacArguments (qid, args, more_implicits, flags) ->
    vtdefault(fun () ->
        with_section_locality ~atts
          (ComArguments.vernac_arguments qid args more_implicits flags))

  | VernacReserve bl ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        vernac_reserve bl)

  | VernacGeneralizable gen ->
    vtdefault(fun () -> with_locality ~atts vernac_generalizable gen)

  | VernacSetOpacity (qidl, on_proj_constant) ->
    vtdefault(fun () ->
        with_locality ~atts (vernac_set_opacity ~on_proj_constant) qidl)

  | VernacSetStrategy l ->
    vtdefault(fun () -> with_locality ~atts vernac_set_strategy l)

  | VernacRemoveOption (key,v) ->
    vtdefault(fun () ->
      let local = Attributes.parse Attributes.hint_locality atts in
      Vernacoptions.vernac_remove_option local key v)

  | VernacAddOption (key,v) ->
    vtdefault(fun () ->
      let local = Attributes.parse Attributes.hint_locality atts in
      Vernacoptions.vernac_add_option local key v)

  | VernacMemOption (key,v) ->
    vtdefault(fun () ->
    unsupported_attributes atts;
    Vernacoptions.vernac_mem_option key v)

  | VernacPrintOption key ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        Vernacoptions.vernac_print_option key)

  | VernacCheckMayEval (r,g,c) ->
    vtreadproofopt(fun ~pstate ->
        unsupported_attributes atts;
        Feedback.msg_notice @@
        vernac_check_may_eval ~pstate r g c)

  | VernacDeclareReduction (s,r) ->
    vtdefault(fun () ->
        with_locality ~atts vernac_declare_reduction s r)

  | VernacGlobalCheck c ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        Feedback.msg_notice @@ vernac_global_check c)

  | VernacPrint p ->
    unsupported_attributes atts;
    Vernactypes.map_typed_vernac
      Feedback.msg_notice
      (vernac_print p)

  | VernacSearch (s,g,r) ->
    vtreadproofopt(
        unsupported_attributes atts;
        vernac_search ~atts s g r)

  | VernacLocate l ->
    vtreadproofopt(fun ~pstate ->
        unsupported_attributes atts;
        Feedback.msg_notice @@ vernac_locate ~pstate l)

  | VernacRegister (qid, r) ->
    vtnoproof(fun () ->
        vernac_register ~atts qid r)

  | VernacPrimitive ((id, udecl), prim, typopt) ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        ComPrimitive.do_primitive id udecl prim typopt)

  | VernacComments l ->
    vtdefault(fun () ->
        unsupported_attributes atts;
        Flags.if_verbose Feedback.msg_info (str "Comments ok\n"))

  | VernacAttributes atts ->
    vtdefault(fun () ->
        vernac_library_attributes atts)

  (* Proof management *)
  | VernacFocus n ->
    vtmodifyproof(unsupported_attributes atts;vernac_focus n)
  | VernacUnfocus ->
    vtmodifyproof(unsupported_attributes atts;vernac_unfocus)
  | VernacUnfocused ->
    vtreadproof(fun ~pstate ->
      unsupported_attributes atts;
      Feedback.msg_notice @@ vernac_unfocused ~pstate)
  | VernacBullet b ->
    vtmodifyproof(
      unsupported_attributes atts;
      vernac_bullet b)
  | VernacSubproof n ->
    vtmodifyproof(
      unsupported_attributes atts;
      vernac_subproof n)
  | VernacEndSubproof ->
    vtmodifyproof(
      unsupported_attributes atts;
      vernac_end_subproof)
  | VernacShow s ->
    vtreadproofopt(fun ~pstate ->
      unsupported_attributes atts;
      Feedback.msg_notice @@ vernac_show ~pstate s)
  | VernacCheckGuard ->
    vtreadproof(fun ~pstate ->
        unsupported_attributes atts;
        Feedback.msg_notice @@ vernac_check_guard ~pstate)
  | VernacValidateProof ->
    vtreadproof(fun ~pstate ->
        unsupported_attributes atts;
        Feedback.msg_notice @@ vernac_validate_proof ~pstate)
  | VernacProof (tac, using) ->
    vtmodifyproof(fun ~pstate ->
    unsupported_attributes atts;
    vernac_proof pstate tac using)

  | VernacEndProof pe ->
    unsupported_attributes atts;
    vtcloseproof (vernac_end_proof pe)

  | VernacAbort ->
    unsupported_attributes atts;
    vtcloseproof vernac_abort

let translate_vernac ?loc ~atts v =
  match v with
  | VernacSynterp e -> translate_vernac_synterp ?loc ~atts e
  | VernacSynPure e -> translate_pure_vernac ?loc ~atts e
