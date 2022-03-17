(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names
open Tac2expr

type environment = Tac2env.environment

type varmap = Tac2ffi.valexpr Names.Id.Map.t

let fmt_stack2 chunk () =
  let chunk = Option.default [] chunk in
  List.map (fun (desc, _) -> desc) chunk

module DebugPP : sig
  type 'a tag = 'a Tac2dyn.Val.tag
  type 'a pp = Environ.env -> Evd.evar_map -> 'a -> Pp.t

  (** [add tag pp] registers a debugger pretty-printer for the type with the
      given [tag]. If there already was such a printer, it is replaced. *)
  val add : 'a tag -> 'a pp -> unit

  (** [find tag] gives the currently registered pretty-printer for the type
      with tag [tag] if there is one, and raises [Not_found] otherwise. *)
  val find : 'a tag -> 'a pp

end = struct
  type 'a tag = 'a Tac2dyn.Val.tag
  type 'a pp = Environ.env -> Evd.evar_map -> 'a -> Pp.t

  module M = Tac2dyn.Val.Map(struct type 'a t = 'a pp end)

  let state = ref M.empty

  let add tag pp = state := M.add tag pp !state
  let find tag = M.find tag !state
end

(* Registering debug printers *)
(* TODO: verify completeness and correctness *)
(* TODO: make it possible for plugins to register types *)

(* Missing:
let val_exn = Val.create "exn"
let val_preterm = Val.create "preterm"
let val_matching_context = Val.create "matching_context"
let val_sort = Val.create "sort"
let val_cast = Val.create "cast"
let val_projection = Val.create "projection"
let val_case = Val.create "case"
let val_binder = Val.create "binder"
let val_univ = Val.create "universe"
let val_free : Names.Id.Set.t Val.tag = Val.create "free"
let val_ltac1 : Geninterp.Val.t Val.tag = Val.create "ltac1"
let val_ind_data : (Names.Ind.t * Declarations.mutual_inductive_body) Val.tag = Val.create "ind_data"
*)

let _ =
  DebugPP.add Tac2ffi.val_constant @@ fun env sigma c ->
  Printer.pr_constant env c

let _ =
  DebugPP.add Tac2ffi.val_constr @@ fun env sigma c ->
  Printer.pr_econstr_env env sigma c

let _ =
  DebugPP.add Tac2ffi.val_constructor @@ fun env sigma c ->
  Printer.pr_constructor env c

let _ =
  DebugPP.add Tac2ffi.val_evar @@ fun env sigma c ->
  Evar.print c

let _ =
  DebugPP.add Tac2ffi.val_ident @@ fun env sigma c ->
  Names.Id.print c

let _ =
  DebugPP.add Tac2ffi.val_inductive @@ fun env sigma c ->
  Printer.pr_inductive env c

let _ =
  DebugPP.add Tac2ffi.val_pattern @@ fun env sigma c ->
  Printer.pr_constr_pattern_env env sigma c

let _ =
  DebugPP.add Tac2ffi.val_pp @@ fun env sigma c ->
  c


let rec fmt_var : Tac2ffi.valexpr -> string -> (string * Pp.t) = fun v name ->
  let str s = Pp.str s in
  let with_type name t = Printf.sprintf "%s : %s" name t in
  let pr_arr arr =
    (* todo: way to format better? *)
    let lst = Array.to_list arr in
    let open Pp in
    let pr = (fun i -> let (_,v) = fmt_var i "" in v) in
    str "[| " ++ hv 0 (prlist_with_sep (fun () -> str ";" ++ spc()) pr lst) ++ str " |]"
  in
  match v with
  | ValInt i -> name, str (string_of_int i)  (* a simple int or index of a defined type, e.g. "true" (= 0) *)
  | ValStr bs -> name, str (Printf.sprintf "%S" (Bytes.to_string bs)) (* Ocaml escapes, not Coq :-( *)
  | ValBlk (tag, arr) -> with_type name (string_of_int tag), pr_arr arr
  | ValCls cls -> name, str "<closure>"
  | ValOpn (kn, args) -> with_type name (KerName.to_string kn), pr_arr args
  | ValExt (tag, v) ->
    let tag_name = Tac2dyn.Val.repr tag in
    let id_type = with_type name tag_name in
    let env = Global.env () in  (* TODO: correct? see Proofview.mli tclENV tclEVARMAP *)
    let sigma = Evd.from_env env in
    try
      let pp_fun = DebugPP.find tag in
      let pp = pp_fun env sigma v in
      id_type, pp
    with Not_found ->
      id_type, str "???"
    | _ ->
      id_type, str "(exception)" (* just in case *)

let fmt_vars2 : varmap list -> int -> Interface.db_vars_rty = fun varmaps framenum ->
  let varmap = List.nth varmaps framenum in
  let open Names in
  List.map (fun b -> let (id, v) = b in fmt_var v (Id.to_string id)) (Id.Map.bindings varmap)


let rec read_loop () =
  let nl = if (*Util.(!batch)*) false then "\n" else "" in
  let hook = Option.get (DebugHook.Intf.get ()) in
  hook.submit_answer (Prompt (tag "message.prompt" @@ fnl () ++ str ("TcDebug > " ^ nl)));
  DebugCommon.action := DebugCommon.read ();
  let open DebugHook.Action in
  match !DebugCommon.action with
  | Continue
  | ContinueRev
  | StepIn
  | StepInRev
  | StepOver
  | StepOverRev
  | StepOut
  | StepOutRev -> ()
  | Skip -> failwith "Skip not in Ltac2"
  | Interrupt -> raise Sys.Break
  | Help -> failwith "Help not in Ltac2"
  | UpdBpts updates -> failwith "UpdBpts"  (* handled in init() loop *)
  | Configd -> failwith "Configd" (* handled in init() loop *)
  | GetStack -> failwith "GetStack" (* handled in read() loop *)
  | GetVars _ -> failwith "GetVars" (* handled in read() loop *)
  | Subgoals _ -> failwith "Subgoals" (* handled in read() loop *)
  | RunCnt num -> failwith "RunCnt not in Ltac2"
  | RunBreakpoint s -> failwith "RunBreakpoint not in Ltac2"
  | Command _ -> failwith "Command"  (* not possible *)
  | Failed -> read_loop ()
  | Ignore -> failwith "Ignore" (* not possible *)

let rec dump_expr2 ?(indent=0) ?(p="D") e =
  let printloc loc =
    let loc = match loc with
    | None -> "None"
    | Some loc -> Pp.string_of_ppcmds (Loc.pr loc)
    in
    Printf.eprintf "loc =  %s\n%!" loc
  in
  let print s = Printf.eprintf "%s\n" s in
  Printf.eprintf "%s %s" p (String.make indent ' ');
  let indent = indent + 2 in
  match e with
  | GTacAtm _ -> print "GTacAtm"
  | GTacVar _ -> print "GTacVar"
  | GTacRef kn -> print (Printf.sprintf "GTacRef %s\n%!" (Names.KerName.to_string kn));
  | GTacFun (_, e) -> print "GTacFun";
    dump_expr2 ~indent ~p e
  | GTacApp (e, el, loc) -> print (Printf.sprintf "GTacApp el len = %d" (List.length el));
    printloc loc;
    dump_expr2 ~indent ~p e
  | GTacLet (_, _, e) -> print "GTacLet";
    dump_expr2 ~indent ~p e
  | GTacCst (_,n,_) -> print (Printf.sprintf "GTacCst %d" n)
  | GTacCse _ -> print "GTacCse"
  | GTacPrj _ -> print "GTacPrj"
  | GTacSet _ -> print "GTacSet"
  | GTacOpn _ -> print "GTacOpn"
  | GTacWth _ -> print "GTacWth"
  | GTacFullMatch _ -> print "GTacFullMatch"
  | GTacExt (tag,_) -> print (Printf.sprintf "GTacExt %s" (Tac2dyn.Arg.repr tag))
  | GTacPrm ml -> print (Printf.sprintf "GTacPrm %s. %s\n%!" ml.mltac_plugin ml.mltac_tactic)
  | GTacAls  _ -> print "GTacAls"

let push_locs item (ist : environment) =   (* ick *)
  match ist.stack with
  | Some s -> item :: ist.locs
  | None -> ist.locs

let push_stack item (ist : environment) =
  match ist.stack with
  | Some s -> Some (item :: s)
  | None -> None

let stop_stuff (ist : environment) loc =
  (* todo: replace with String.starts_with when OCaml 4.13 is required *)
  let starts_with p s =
    let plen = String.length p in
    plen < String.length s && (String.sub s 0 plen = p)
  in
  (* filter out locations in Ltac2 plugin files *)
  let not_internal loc =
    let open Loc in
    let fname = match loc with
      | Some {fname=InFile {file}} -> file
      | _ -> ""
    in
    if false then Printf.eprintf "loc = %s\n%!" fname;
    true || Bool.not (starts_with "user-contrib/Ltac2/" fname)
  in
  let chunk = (ist.locs, fmt_stack2 ist.stack, fmt_vars2 (ist.env_ist :: ist.varmaps)) in
  DebugCommon.save_chunk chunk loc;
  let stop = DebugCommon.get_debug () && (not_internal loc) &&
(*    (Bool.not (starts_with "Ltac2." fname)) && *)
    (DebugCommon.breakpoint_stop loc || DebugCommon.stepping_stop ())
  in
  if stop then
    DebugCommon.new_stop_point ();
  stop
