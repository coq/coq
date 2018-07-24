(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*
Displays the differences between successive proof steps in coqtop and CoqIDE.
Proof General requires minor changes to make the diffs visible, but this code
shouldn't break the existing version of PG.  See pp_diff.ml for details on how
the diff works.

Diffs are computed for the hypotheses and conclusion of the first goal between
the old and new proofs.

Diffs can be enabled with the Coq commmand "Set Diffs on|off|removed." or
'-diffs "on"|"off"|"removed"' on the OS command line.  The "on" option shows only the
new item with added text, while "removed" shows each modified item twice--once
with the old value showing removed text and once with the new value showing
added text.

In CoqIDE, colors and highlights can be set in the Edit/Preferences/Tags panel.
For coqtop, these can be set through the COQ_COLORS environment variable.

Limitations/Possible enhancements:

- If you go back to a prior proof step, diffs are not shown on the new current
step.  Diffs will be shown again once you do another proof step.

- Diffs are done between the first active goal in the old and new proofs.
If, for example, the proof step completed a goal, then the new goal is a
different goal, not a transformation of the old goal, so a diff is probably
not appropriate.  (There's currently no way to tell when this happens or to
accurately match goals across old and new proofs.
See https://github.com/coq/coq/issues/7653)  This is also why only the
first goal is diffed.

- "Set Diffs "xx"." should reprint the current goal using the new option.

- coqtop colors were chosen for white text on a black background.  They're
not the greatest.  I didn't want to change the existing green highlight.
Suggestions welcome.

- coqtop underlines removed text because (per Wikipedia) the ANSI escape code
for strikeout is not commonly supported (it didn't work on mine).  CoqIDE
uses strikeout on removed text.
*)

open Pp_diff

let diff_option = ref `OFF

(* todo: Is there a way to persist the setting between sessions?
   Eg if the user wants this as a permanent config setting? *)
let read_diffs_option () = match !diff_option with
| `OFF -> "off"
| `ON -> "on"
| `REMOVED -> "removed"

let write_diffs_option = function
| "off" -> diff_option := `OFF
| "on" -> diff_option := `ON
| "removed" -> diff_option := `REMOVED
| _ -> CErrors.user_err Pp.(str "Diffs option only accepts the following values: \"off\", \"on\", \"removed\".")

let _ =
  Goptions.(declare_string_option {
    optdepr = false;
    optname = "show diffs in proofs";
    optkey = ["Diffs"];
    optread = read_diffs_option;
    optwrite = write_diffs_option
  })

let show_diffs () = !diff_option <> `OFF;;
let show_removed () = !diff_option = `REMOVED;;


(* DEBUG/UNIT TEST *)
let cfprintf oc = Printf.(kfprintf (fun oc -> fprintf oc "") oc)
let log_out_ch = ref stdout
[@@@ocaml.warning "-32"]
let cprintf s = cfprintf !log_out_ch s
[@@@ocaml.warning "+32"]

module StringMap = Map.Make(String);;

let tokenize_string s =
  (* todo: cLexer changes buff as it proceeds.  Seems like that should be saved, too.
  But I don't understand how it's used--it looks like things get appended to it but
  it never gets cleared. *)
  let rec stream_tok acc str =
    let e = Stream.next str in
    if Tok.(equal e EOI) then
      List.rev acc
    else
      stream_tok ((Tok.extract_string e) :: acc) str
  in
  let st = CLexer.get_lexer_state () in
  try
    let istr = Stream.of_string s in
    let lex = CLexer.lexer.Plexing.tok_func istr in
    let toks = stream_tok [] (fst lex) in
    CLexer.set_lexer_state st;
    toks
  with exn ->
    CLexer.set_lexer_state st;
    raise (Diff_Failure "Input string is not lexable");;


type hyp_info = {
  idents: string list;
  rhs_pp: Pp.t;
  mutable done_: bool;
}

(* Generate the diffs between the old and new hyps.
   This works by matching lines with the hypothesis name and diffing the right-hand side.
   Lines that have multiple names such as "n, m : nat" are handled specially to account
   for, say, the addition of m to a pre-existing "n : nat".
 *)
let diff_hyps o_line_idents o_map n_line_idents n_map =
  let rv : Pp.t list ref = ref [] in

  let is_done ident map = (StringMap.find ident map).done_ in
  let exists ident map =
    try let _ = StringMap.find ident map in true
    with Not_found -> false in
  let contains l ident = try [List.find (fun x  -> x = ident) l] with Not_found -> [] in

  let output old_ids_uo new_ids =
    (* use the order from the old line in case it's changed in the new *)
    let old_ids = if old_ids_uo = [] then [] else
      let orig = (StringMap.find (List.hd old_ids_uo) o_map).idents in
      List.concat (List.map (contains orig) old_ids_uo) in

    let setup ids map = if ids = [] then ("", Pp.mt ()) else
      let open Pp in
      let rhs_pp = (StringMap.find (List.hd ids) map).rhs_pp in
      let pp_ids = List.map (fun x -> str x) ids in
      let hyp_pp = List.fold_left (fun l1 l2 -> l1 ++ str ", " ++ l2) (List.hd pp_ids) (List.tl pp_ids) ++ rhs_pp in
      (string_of_ppcmds hyp_pp, hyp_pp)
    in

    let (o_line, o_pp) = setup old_ids o_map in
    let (n_line, n_pp) = setup new_ids n_map in

    let hyp_diffs = diff_str ~tokenize_string o_line n_line in
    let (has_added, has_removed) = has_changes hyp_diffs in
    if show_removed () && has_removed then begin
      let o_entry = StringMap.find (List.hd old_ids) o_map in
      o_entry.done_ <- true;
      rv := (add_diff_tags `Removed o_pp hyp_diffs) :: !rv;
    end;
    if n_line <> "" then begin
      let n_entry = StringMap.find (List.hd new_ids) n_map in
      n_entry.done_ <- true;
      rv := (add_diff_tags `Added n_pp hyp_diffs) :: !rv
    end
  in

  (* process identifier level diff *)
  let process_ident_diff diff =
    let (dtype, ident) = get_dinfo diff in
    match dtype with
    | `Removed ->
      if dtype = `Removed then begin
        let o_idents = (StringMap.find ident o_map).idents in
        (* only show lines that have all idents removed here; other removed idents appear later *)
        if show_removed () &&
            List.for_all (fun x -> not (exists x n_map)) o_idents then
          output (List.rev o_idents) []
      end
    | _ -> begin (* Added or Common case *)
      let n_idents = (StringMap.find ident n_map).idents in

      (* Process a new hyp line, possibly splitting it.  Duplicates some of
         process_ident iteration, but easier to understand this way *)
      let process_line ident2 =
        if not (is_done ident2 n_map) then begin
          let n_ids_list : string list ref = ref [] in
          let o_ids_list : string list ref = ref [] in
          let fst_omap_idents = ref None in
          let add ids id map =
            ids := id :: !ids;
            (StringMap.find id map).done_ <- true in

          (* get identifiers shared by one old and one new line, plus
             other Added in new and other Removed in old *)
          let process_split ident3 =
            if not (is_done ident3 n_map) then begin
              let this_omap_idents = try Some (StringMap.find ident3 o_map).idents
                                    with Not_found -> None in
              if !fst_omap_idents = None then
                fst_omap_idents := this_omap_idents;
              match (!fst_omap_idents, this_omap_idents) with
              | (Some fst, Some this) when fst == this ->  (* yes, == *)
                add n_ids_list ident3 n_map;
                (* include, in old order, all undone Removed idents in old *)
                List.iter (fun x -> if x = ident3 || not (is_done x o_map) && not (exists x n_map) then
                                    (add o_ids_list x o_map)) fst
              | (_, None) ->
                add n_ids_list ident3 n_map (* include all undone Added idents in new *)
              | _ -> ()
            end in
          List.iter process_split n_idents;
          output (List.rev !o_ids_list) (List.rev !n_ids_list)
        end in
      List.iter process_line n_idents (* O(n^2), so sue me *)
    end in

  let cvt s = Array.of_list (List.concat s) in
  let ident_diffs = diff_strs (cvt o_line_idents) (cvt n_line_idents) in
  List.iter process_ident_diff ident_diffs;
  List.rev !rv;;


type 'a hyp = (Names.Id.t list * 'a option * 'a)
type 'a reified_goal = { name: string; ty: 'a; hyps: 'a hyp list; env : Environ.env; sigma: Evd.evar_map }

(* XXX: Port to proofview, one day. *)
(* open Proofview *)
module CDC = Context.Compacted.Declaration

let to_tuple : Constr.compacted_declaration -> (Names.Id.t list * 'pc option * 'pc) =
  let open CDC in function
    | LocalAssum(idl, tm)   -> (idl, None, tm)
    | LocalDef(idl,tdef,tm) -> (idl, Some tdef, tm);;

(* XXX: Very unfortunately we cannot use the Proofview interface as
   Proof is still using the "legacy" one. *)
let process_goal sigma g : Constr.t reified_goal =
  let env  = Goal.V82.env   sigma g in
  let hyps = Goal.V82.hyps  sigma g in
  let ty   = Goal.V82.concl sigma g in
  let name = Goal.uid g             in
  (* There is a Constr/Econstr mess here... *)
  let ty   = EConstr.to_constr sigma ty in
  (* compaction is usually desired [eg for better display] *)
  let hyps      = Termops.compact_named_context (Environ.named_context_of_val hyps) in
  let hyps      = List.map to_tuple hyps in
  { name; ty; hyps; env; sigma };;

let pr_letype_core goal_concl_style env sigma t =
  Ppconstr.pr_lconstr_expr (Constrextern.extern_type goal_concl_style env sigma t)

let pp_of_type env sigma ty =
  pr_letype_core true env sigma EConstr.(of_constr ty)

let pr_leconstr_core goal_concl_style env sigma t =
  Ppconstr.pr_lconstr_expr (Constrextern.extern_constr goal_concl_style env sigma t)

let pr_lconstr_env env sigma c = pr_leconstr_core false env sigma (EConstr.of_constr c)

(* fetch info from a goal, returning (idents, map, concl_pp) where
idents is a list with one entry for each hypothesis, each entry is the list of
idents on the lhs of the hypothesis.  map is a map from ident to hyp_info
reoords.  For example: for the hypotheses:
  b : bool
  n, m : nat

list will be [ ["b"]; ["n"; "m"] ]

map will contain:
  "b" -> { ["b"], Pp.t for ": bool"; false }
  "n" -> { ["n"; "m"], Pp.t for ": nat"; false }
  "m" -> { ["n"; "m"], Pp.t for ": nat"; false }
 where the last two entries share the idents list.

concl_pp is the conclusion as a Pp.t
*)
let goal_info goal sigma =
  let map = ref StringMap.empty in
  let line_idents = ref [] in
  let build_hyp_info env sigma hyp =
    let (names, body, ty) = hyp in
    let open Pp in
    let idents = List.map (fun x -> Names.Id.to_string x) names in

    line_idents := idents :: !line_idents;
    let mid = match body with
    | Some c ->
      let pb = pr_lconstr_env env sigma c in
      let pb = if Constr.isCast c then surround pb else pb in
      str " := " ++ pb
    | None -> mt() in
    let ts = pp_of_type env sigma ty in
    let rhs_pp = mid ++ str " : " ++ ts in

    let make_entry () = { idents; rhs_pp; done_ = false } in
    List.iter (fun ident -> map := (StringMap.add ident (make_entry ()) !map); ()) idents
  in

  try
    let { ty=ty; hyps=hyps; env=env } = process_goal sigma goal in
    List.iter (build_hyp_info env sigma) (List.rev hyps);
    let concl_pp = pp_of_type env sigma ty in
    ( List.rev !line_idents, !map, concl_pp )
  with _ -> ([], !map, Pp.mt ());;

let diff_goal_info o_info n_info =
  let (o_line_idents, o_hyp_map, o_concl_pp) = o_info in
  let (n_line_idents, n_hyp_map, n_concl_pp) = n_info in
  let show_removed = Some (show_removed ()) in
  let concl_pp = diff_pp_combined ~tokenize_string ?show_removed o_concl_pp n_concl_pp in

  let hyp_diffs_list = diff_hyps o_line_idents o_hyp_map n_line_idents n_hyp_map in
  (hyp_diffs_list, concl_pp)

let hyp_list_to_pp hyps =
  let open Pp in
  match hyps with
  | h :: tl -> List.fold_left (fun x y -> x ++ cut () ++ y) h tl
  | [] -> mt ();;

(* Special purpuse, use only for the IDE interface,  *)
let diff_first_goal o_proof n_proof =
  let first_goal_info proof =
    match proof with
    | None -> ([], StringMap.empty, Pp.mt ())
    | Some proof2 ->
      let (goals,_,_,_,sigma) = Proof.proof proof2 in
      match goals with
      | hd :: tl -> goal_info hd sigma;
      | _ -> ([], StringMap.empty, Pp.mt ())
  in
  diff_goal_info (first_goal_info o_proof) (first_goal_info n_proof);;

let diff_goals ?prev_gs n_gs =
  let unwrap gs =
    match gs with
    | Some gs ->
      let goal = Evd.sig_it gs in
      let sigma = Refiner.project gs in
      goal_info goal sigma
    | None -> ([], StringMap.empty, Pp.mt ())
  in
  let (hyps_pp_list, concl_pp) = diff_goal_info (unwrap prev_gs) (unwrap n_gs) in
  let open Pp in
  v 0 (
    (hyp_list_to_pp hyps_pp_list) ++ cut () ++
    str "============================" ++ cut () ++
    concl_pp);;
