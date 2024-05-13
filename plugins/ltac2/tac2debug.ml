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

(* todo: why isn't "open Tac2env" sufficient for these 2 types? *)
type environment = Tac2env.environment

type valtype = Tac2typing_env.TVar.t glb_typexpr option  (* todo: keep option? *)

type typed_valexpr = Tac2env.typed_valexpr = {
  e : valexpr;
  t : Obj.t option (* Obj.t is really valtype *)
}

let fmt_stack2 chunk () =
  let chunk = Option.default [] chunk in
  List.map (fun (desc, _) -> desc) chunk

let rec dump_type ?(indent=0) env t =
  let tname = match t with
  | GTypVar a -> "GTypVar"
  | GTypArrow (a,b) -> "GTypArrow"
  | GTypRef (tc, tl) -> "GTypRef"
  in
  Printf.eprintf "%s*%s\n%!" (String.make indent ' ') tname;
  let indent = indent + 2 in
  match t with
  | GTypVar _ -> ()
  | GTypArrow _ -> ()
  | GTypRef (tc, params) ->
    (match tc with
     | Tuple n -> Printf.eprintf "%sTuple %d\n%!" (String.make indent ' ') n
     | Other kn -> Printf.eprintf "%sOther %s\n%!" (String.make indent ' ') (Names.KerName.to_string kn)
     );
     List.iter (fun i -> dump_type ~indent env i) params

let fmt_vars2 varmaps framenum =
  let varmap = List.nth varmaps framenum in
  let open Names in
  List.map (fun b -> let (id, v) = b in
      let v_str = match v.t with
      | Some o ->
        let tenv, t = Tac2valtype.unwrap o in
        let env = Global.env () in
        let sigma = DebugCommon.get_sigma () in
        let maptv t = Tac2typing_env.nf tenv t in
        Tac2print.pr_valexpr ~maptv env sigma v.e t;
      | None -> str "<poly>"
      in
      (Id.to_string id), v_str
    ) (Id.Map.bindings varmap)


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
let rec dump_pat ?(indent=0) p =
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
  let {CAst.v} = p in
  match v with
  | CPatVar n ->
    let name = match n with
    | Anonymous -> "Anonymous"
    | Name id -> Names.Id.to_string id
    in
  printloc (Printf.sprintf "CPatVar %s" name) p
  | CPatAtm a ->
    let atom = match a with
    | AtmInt i -> string_of_int i
    | AtmStr s -> s
    in
    printloc (Printf.sprintf "CPatAtm %s" atom) p
  | CPatRef (c,pl) -> printloc "CPatRef" p;
    List.iter (fun p -> dump_pat ~indent p) pl
  | CPatRecord _ -> printloc "CPatRecord" p
  | CPatCnv _ -> printloc "CPatCnv" p
  | CPatOr _ -> printloc "CPatOr" p
  | CPatAs _ -> printloc "CPatAs" p

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
    List.iter (fun (p,te) -> dump_pat ~indent p; dump_expr ~indent te) lc;
    dump_expr ~indent:(indent-2) e;
  | CTacCnv _ -> printloc "CTacCnv" e
  | CTacSeq (e1, e2) ->
    printloc "CTacSeq" e;
    dump_expr ~indent e1;
    dump_expr ~indent e2
  | CTacIft _ -> printloc "CTacIft" e
  | CTacCse (e,pl) -> printloc "CTacCse" e;
    dump_expr ~indent e;
    List.iter (fun (p, e) -> dump_pat ~indent p; dump_expr ~indent e) pl
  | CTacRec _ -> printloc "CTacRec" e
  | CTacPrj _ -> printloc "CTacPrj" e
  | CTacSet _ -> printloc "CTacSet" e
  | CTacExt _ -> printloc "CTacExt" e

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
  | GTacFun (_, _, e) -> print "GTacFun";
    dump_Gexpr ~indent ~p e
  | GTacApp (e, el, loc) -> print (Printf.sprintf "GTacApp el len = %d" (List.length el));
    printloc loc;
    dump_Gexpr ~indent ~p e;
    List.iter (fun e -> dump_Gexpr ~indent ~p e) el
  | GTacLet (isrec, lc, e) -> print "GTacLet";
    List.iter (fun (p1,e2, t) ->
        (match p1 with
        | Name nm -> print ~indent (Printf.sprintf "let name = %s" (Id.to_string nm))  (* vars to be assigned *)
        | Anonymous -> print ~indent (Printf.sprintf "Anonymous"));
        dump_Gexpr ~indent ~p e2
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
    Array.iter (fun e1 -> dump_Gexpr ~indent ~p e1) a1;
    Array.iter (fun (a3, e2) ->
        Array.iter (fun (n,_) ->
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
  | GTacExt (tag,_) -> print (Printf.sprintf "GTacExt %s" (Tac2dyn.Arg.repr tag))
  | GTacPrm ml -> print (Printf.sprintf "GTacPrm %s. %s%!" ml.mltac_plugin ml.mltac_tactic)
  | GTacAls (e,_, fn) -> print (Printf.sprintf "GTacAls %s" fn);
    dump_Gexpr ~indent ~p e

let dump_Gexpr ?(indent=0) ?(p="D") e =
  dump_Gexpr ~indent ~p e;
  Printf.eprintf "%!"

let test = (try let _ = Sys.getenv("TEST") in true with _ -> false)

let push_locs item (ist : environment) =
  match ist.stack with
  | Some s -> item :: ist.locs
  | None -> ist.locs

let push_stack item (ist : environment) =
  match ist.stack with
  | Some s -> Some (item :: s)
  | None -> None

let get_chunk (ist : environment) =
  DebugCommon.{ locs = ist.locs;
                stack_f = (fmt_stack2 ist.stack);
                vars_f = (fmt_vars2 (ist.env_ist :: ist.varmaps)) }

let maybe_stop (ist : environment) loc =
  let chunk = get_chunk ist in
  DebugCommon.save_in_history chunk loc;
  if DebugCommon.stop_in_debugger loc then begin
    DebugCommon.pr_goals ();
    read_loop ()
  end
