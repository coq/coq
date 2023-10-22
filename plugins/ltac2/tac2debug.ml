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
open Tac2ffi

type environment = Tac2env.environment

type varmap = valexpr Names.Id.Map.t

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
  DebugPP.add val_constant @@ fun env sigma c ->
  Printer.pr_constant env c

let _ =
  DebugPP.add val_constr @@ fun env sigma c ->
  Printer.pr_econstr_env env sigma c

let _ =
  DebugPP.add val_constructor @@ fun env sigma c ->
  Printer.pr_constructor env c

let _ =
  DebugPP.add val_evar @@ fun env sigma c ->
  Evar.print c

let _ =
  DebugPP.add val_ident @@ fun env sigma c ->
  Names.Id.print c

let _ =
  DebugPP.add val_inductive @@ fun env sigma c ->
  Printer.pr_inductive env c

let _ =
  DebugPP.add val_pattern @@ fun env sigma c ->
  Printer.pr_constr_pattern_env env sigma c

let _ =
  DebugPP.add val_pp @@ fun env sigma c ->
  c


let rec fmt_var v name =
  let cname = function
    | ValInt _ -> "ValInt"
    | ValStr _ -> "ValStr"
    | ValBlk _ -> "ValBlk"
    | ValCls _ -> "ValCls"
    | ValOpn _ -> "ValOpn"
    | ValExt _ -> "ValExt"
  in
  let str s = Pp.str s in
  let with_type name t = Printf.sprintf "%s : %s" name t in
  let pr_arr arr =
    (* todo: doesn't handle [], [1] or [ [| |]; [| |] ] cases correctly *)
    let lst = Array.to_list arr in
    let open Pp in
    let pr = (fun i -> let (_,v) = fmt_var i "" in v) in
    let is_list = Array.length arr = 2 && (cname arr.(0) <> (cname arr.(1))) in
    let ldelim, rdelim, lst = if is_list then
      let rec conv rv arr =
        match arr.(1) with
        | ValBlk (_,arr2) -> conv (arr.(0) :: rv) arr2
        | _ -> List.rev (arr.(0) :: rv)
      in
      "[ ", " ]", conv [] arr
    else
      "[| ", " |]", lst
    in
    str ldelim ++ hv 0 (prlist_with_sep (fun () -> str ";" ++ spc()) pr lst) ++ str rdelim
  in
(*  Printf.eprintf "name = %s val type %s\n%!" name (cname v); *)
  match v with
  | ValInt i -> name, str (string_of_int i)  (* a simple int or index of a defined type, e.g. "true" (= 0) *)
  | ValStr bs -> name, str (Printf.sprintf "%S" (Bytes.to_string bs)) (* Ocaml escapes, not Coq :-( *)
  | ValBlk (tag, arr) -> with_type name (string_of_int tag), pr_arr arr
  | ValCls cls -> name, str "<closure>"
  | ValOpn (kn, args) -> with_type name (KerName.to_string kn), pr_arr args
  | ValExt (tag, v) ->
    let tag_name = Tac2dyn.Val.repr tag in
    let id_type = with_type name tag_name in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    try
      let pp_fun = DebugPP.find tag in
      let pp = pp_fun env sigma v in
      id_type, pp
    with Not_found ->
      id_type, str "???"
    | _ ->
      id_type, str "(exception)" (* just in case *)

let fmt_vars2 varmaps framenum =
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
  | Continue | StepIn | StepOver | StepOut -> ()
  | Interrupt -> raise Sys.Break
  | Failed -> read_loop ()

  | Skip | Help | RunCnt _ | RunBreakpoint _ ->
    Feedback.msg_info Pp.(str "Not available in Ltac2");
    read_loop ()

  | Configd (* handled in init() loop *)
  | ContinueRev | StepInRev | StepOverRev | StepOutRev
  | UpdBpts _ | GetStack | GetVars _ | Subgoals _ (* handled in read() loop *)
  | Command _ | Ignore -> (* not possible *)
    failwith ("ltac2 invalid action: " ^ (DebugHook.Action.to_string !DebugCommon.action))

[@@@ocaml.warning "-32"]
let rec dump_expr ?(indent=0) e =
  let printloc item e =
    let {CAst.loc} = e in
    let loc = match loc with
    | None -> "None"
    | Some loc -> Pp.string_of_ppcmds (Loc.pr loc)
    in
    Printf.eprintf "%s  %s\n%!" item loc
  in
  Printf.eprintf "%s" (String.make indent ' ');
  let indent = indent + 2 in
  let {CAst.v} = e in
  match v with
  | CTacAtm _ -> printloc "CTacAtm" e
  | CTacRef _ -> printloc "CTacRef" e
  | CTacCst _ -> printloc "CTacCst" e
  | CTacFun (_, f) -> printloc "CTacFun" e;
    dump_expr ~indent f
  | CTacApp (f, args) -> printloc "CTacApp" e;
    dump_expr ~indent f;
    List.iter (fun i -> dump_expr ~indent i) args;
(*| CTacSyn of (raw_patexpr * raw_tacexpr) list * KerName.t*)
  | CTacSyn (el, kn) -> printloc "CTacSyn" e;
    Printf.eprintf "%s> %s\n%!" (String.make indent ' ') (Names.KerName.to_string kn);
    List.iter (fun i -> let (_, e) = i in dump_expr ~indent e) el
  | CTacLet (isrec, lc, e) -> printloc "CTacLet" e;
    List.iter (fun (p,te) -> dump_expr ~indent te) lc;
    dump_expr ~indent:(indent-2) e;
  | CTacCnv _ -> printloc "CTacCnv" e
  | CTacSeq (e1, e2) ->
    printloc "CTacSeq" e;
    dump_expr ~indent e1;
    dump_expr ~indent e2
  | CTacIft _ -> printloc "CTacIft" e
  | CTacCse _ -> printloc "CTacCse" e
  | CTacRec _ -> printloc "CTacRec" e
  | CTacPrj _ -> printloc "CTacPrj" e
  | CTacSet _ -> printloc "CTacSet" e
  | CTacExt _ -> printloc "CTacExt" e

(* for call from g_ltac2.mlg *)
let dump_Cexpr loc e =
  try ignore @@ Sys.getenv "TEST";
    let loc = match loc with
    | None -> "None"
    | Some loc -> Pp.string_of_ppcmds (Loc.pr loc)
    in
    Printf.eprintf "loc = %s\n%!" loc;
    dump_expr e;
  Printf.eprintf "\n%!"
  with Not_found -> ()

let rec dump_Gexpr ?(indent=0) ?(p="D") e =
  let printloc loc =
    let loc = match loc with
    | None -> "None"
    | Some loc -> Pp.string_of_ppcmds (Loc.pr loc)
    in
    Printf.eprintf "loc =  %s\n%!" loc
  in
  let print ?(indent=indent) s = Printf.eprintf "%s %s%s\n" p (String.make indent ' ') s in
  let indent = indent + 2 in
  match e with
  | GTacAtm at ->
    let s = match at with
      | AtmInt i -> string_of_int i
      | AtmStr s -> Printf.sprintf "\"%s\"" s
    in
    print (Printf.sprintf "GTacAtm %s%!" s)
  | GTacVar id -> print (Printf.sprintf "GTacVar %s" (Names.Id.to_string id))
  | GTacRef kn -> print (Printf.sprintf "GTacRef %s" (Names.KerName.to_string kn))
  | GTacFun (_, e) -> print "GTacFun";
    dump_Gexpr ~indent ~p e
  | GTacApp (e, el, loc) -> print (Printf.sprintf "GTacApp el len = %d" (List.length el));
    printloc loc;
    dump_Gexpr ~indent ~p e
  | GTacLet (isrec, lc, e) -> print "GTacLet";
    List.iter (fun (p,te) ->
        (match p with
        | Name nm -> print ~indent (Printf.sprintf "let name = %s" (Id.to_string nm))  (* vars to be assigned *)
        | Anonymous -> print ~indent (Printf.sprintf "Anonymous"));
        dump_Gexpr ~indent te
      ) lc;
    dump_Gexpr ~indent:(indent-2) ~p e
  | GTacCst (ci,n,el) ->
    let s = match ci with
    | Other kn -> Names.KerName.to_string kn
    | Tuple n -> string_of_int n
    in
    print (Printf.sprintf "GTacCst %s %d" s n);
    List.iter (fun e -> dump_Gexpr ~indent ~p e) el
  | GTacCse (e, ci, a1, a2) -> print (Printf.sprintf "GTacCse %d %d" (Array.length a1)  (Array.length a2));
    Array.iter (fun (a3, e2) ->
        Array.iter (fun n ->
            match n with
            | Name nm -> print (Printf.sprintf "case name = %s" (Id.to_string nm))  (* vars to be assigned *)
            | Anonymous -> print (Printf.sprintf "Anonymous");
          ) a3;
        dump_Gexpr ~indent ~p e2
      ) a2;
    Printf.eprintf "\n%!"
  | GTacPrj _ -> print "GTacPrj"
  | GTacSet _ -> print "GTacSet"
  | GTacOpn _ -> print "GTacOpn"
  | GTacWth _ -> print "GTacWth"
  | GTacFullMatch _ -> print "GTacFullMatch"
  | GTacExt (tag,_,_) -> print (Printf.sprintf "GTacExt %s" (Tac2dyn.Arg.repr tag))
  | GTacPrm ml -> print (Printf.sprintf "GTacPrm %s. %s%!" ml.mltac_plugin ml.mltac_tactic)
  | GTacAls (e,_) -> print "GTacAls";
    dump_Gexpr ~indent ~p e

let dump_Gexpr ?(indent=0) ?(p="D") e =
  dump_Gexpr ~indent ~p e;
  Printf.eprintf "%!"

let test = (try let _ = Sys.getenv("TEST") in true with _ -> false)

(* Tac2typing_env.TVar.t Tac2expr.glb_typexpr option    *)
let rec dump_type ?(indent=0) env t =
  Printf.eprintf "%s" (String.make indent ' ');
  let indent = indent + 2 in
  if false then dump_type ~indent env t;
  Printf.eprintf "type name is %s\n%!" (Pp.string_of_ppcmds (Tac2typing_env.pr_glbtype env t));
  match t with
  | GTypVar t1 -> ()
  | _ -> ()

let push_locs item (ist : environment) =
  match ist.stack with
  | Some s -> item :: ist.locs
  | None -> ist.locs

let push_stack item (ist : environment) =
  match ist.stack with
  | Some s -> Some (item :: s)
  | None -> None

(* todo: if desired, filter out stops in the Ltac2 libraries *)
let maybe_stop (ist : environment) loc =
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
  let chunk = DebugCommon.{ locs = ist.locs;
                            stack_f = (fmt_stack2 ist.stack);
                            vars_f = (fmt_vars2 (ist.env_ist :: ist.varmaps)) } in
  DebugCommon.save_chunk chunk loc;
  let stop = DebugCommon.get_debug () && (not_internal loc) &&
(*    (Bool.not (starts_with "Ltac2." fname)) && *)
    (DebugCommon.stop_in_debugger loc)
  in
  if stop then
    DebugCommon.new_stop_point ();
  stop
