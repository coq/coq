(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*
Displays the differences between successive proof steps in coqtop and RocqIDE.
Proof General requires minor changes to make the diffs visible, but this code
shouldn't break the existing version of PG.  See pp_diff.ml for details on how
the diff works.

Diffs are computed for the hypotheses and conclusion of each goal in the new
proof with its matching goal in the old proof.

Diffs can be enabled in coqtop with 'Set Diffs "on"|"off"|"removed"' or
'-diffs on|off|removed' on the OS command line.  In RocqIDE, they can be enabled
from the View menu.  The "on" option shows only the new item with added text,
while "removed" shows each modified item twice--once with the old value showing
removed text and once with the new value showing added text.

In RocqIDE, colors and highlights can be set in the Edit/Preferences/Tags panel.
For coqtop, these can be set through the ROCQ_COLORS environment variable.

Limitations/Possible enhancements:

- coqtop colors were chosen for white text on a black background.  They're
not the greatest.  I didn't want to change the existing green highlight.
Suggestions welcome.

- coqtop underlines removed text because (per Wikipedia) the ANSI escape code
for strikeout is not commonly supported (it didn't work on my system).  RocqIDE
uses strikeout on removed text.
*)

open Pp_diff

let term_color = ref true

let write_color_enabled enabled =
  term_color := enabled

let color_enabled () = !term_color

type diffOpt = DiffOff | DiffOn | DiffRemoved

let diffs_to_string = function
  | DiffOff -> "off"
  | DiffOn -> "on"
  | DiffRemoved -> "removed"


let assert_color_enabled () =
  if not (color_enabled ()) then
    CErrors.user_err
      Pp.(str "Enabling Diffs requires setting the \"-color\" command line argument to \"on\" or \"auto\".")

let string_to_diffs = function
  | "off" -> DiffOff
  | "on" -> assert_color_enabled (); DiffOn
  | "removed" -> assert_color_enabled (); DiffRemoved
  | _ -> CErrors.user_err Pp.(str "Diffs option only accepts the following values: \"off\", \"on\", \"removed\".")

let opt_name = ["Diffs"]

let { Goptions.get = diff_option } =
  Goptions.declare_interpreted_string_option_and_ref
    ~key:opt_name
    ~value:DiffOff
    string_to_diffs
    diffs_to_string
    ()

let show_diffs () = match diff_option () with DiffOff -> false | _ -> true
let show_removed () = match diff_option () with DiffRemoved -> true | _ -> false


(* DEBUG/UNIT TEST *)
let cfprintf oc = Printf.(kfprintf (fun oc -> fprintf oc "") oc)
let log_out_ch = ref stdout
[@@@ocaml.warning "-32"]
let cprintf s = cfprintf !log_out_ch s
[@@@ocaml.warning "+32"]

let tokenize_string s =
  (* todo: cLexer changes buff as it proceeds.  Seems like that should be saved, too.
     But I don't understand how it's used--it looks like things get appended to it but
     it never gets cleared. *)
  let kwstate = Procq.get_keyword_state() in
  let rec stream_tok acc str =
    let e = Gramlib.LStream.next kwstate str in
    match e with
    | Tok.EOI -> List.rev acc
    | _ -> stream_tok ((Tok.extract_string true e) :: acc) str
  in
  let st = CLexer.Lexer.State.get () in
  Fun.protect ~finally:(fun () -> CLexer.Lexer.State.set st) @@ fun () ->
  try
    let istr = Gramlib.Stream.of_string s in
    let lex = CLexer.LexerDiff.tok_func istr in
    stream_tok [] lex
  with exn when CErrors.noncritical exn ->
    raise (Diff_Failure "Input string is not lexable")

type hyp_info = {
  idents: string list;
  rhs_pp: Pp.t;
}

(* Diff the old and new hypotheses.  The RHS (starting at ":" or ":=") is diffed with
   the same token-based diff used for goal conclusions.  Identifiers in the LHS are
   handled differently:

   The order and grouping of LHS identifiers in the added/unchanged lines is always
   the same as when diff is not enabled.  Identifiers existing in the old context
   that are present in the new context with the same RHS are not highlighted.  New
   identifiers are always highlighted.

   If all the existing identifiers in a line have a new RHS, those identifiers are
   not highlighted (in this case, the RHS will be highlighted, making the change clear).

   Removed and added lines are generated in separate passes.  Removed lines appear
   before the added line that has most identifiers in common with the old.  (For
   a tie, use the first one found.  For zero in common, put the removal before
   the first addition/common line.)  This should be a good but not perfect
   approximation to what a human might do.
 *)
let diff_hyps o_idents_in_lines o_map n_idents_in_lines n_map =
  let rv : Pp.t list ref = ref [] in
  let removals = ref CString.Map.empty in

  (* get the first identifier on the new line with the most ids in common
     with the given old idents *)
  let best_match old_ids =
    let rec aux best best_score = function
      | [] -> best
      | nl_idents :: tl ->
        let score = List.fold_left (fun rv ident ->
            if List.mem ident nl_idents then rv+1 else rv) 0 old_ids in
        if score > best_score then
          aux (List.hd nl_idents) score tl
        else
          aux best best_score tl
    in
    aux "" 0 n_idents_in_lines
  in

  (* generate the Pp.t for a single line of the hypotheses *)
  let gen_line old_ids old_rhs new_ids new_rhs otype =
    let gen_pp ids map hyp =
      if ids = [] then ("", Pp.mt ()) else begin
        let open Pp in
        let pp_ids = List.map (fun x -> str x) ids in
        let hyp_pp = List.fold_left (fun l1 l2 -> l1 ++ str ", " ++ l2) (List.hd pp_ids) (List.tl pp_ids) ++ hyp in
        (string_of_ppcmds hyp_pp, hyp_pp)
      end;
    in

    let (o_line, o_pp) = gen_pp old_ids o_map old_rhs in
    let (n_line, n_pp) = gen_pp new_ids n_map new_rhs in

    let hyp_diffs = diff_str ~tokenize_string o_line n_line in
    if otype = `Added then begin
      let rems = try CString.Map.find (List.hd new_ids) !removals with Not_found -> [] in
      rv := add_diff_tags otype n_pp hyp_diffs :: (rems @ !rv)
    end else begin
      let (has_added, has_removed) = has_changes hyp_diffs in
      if has_removed then begin
        let d_line = add_diff_tags otype o_pp hyp_diffs in
        let best = best_match old_ids in
        if best = "" then
          rv := d_line :: !rv
        else begin
          let ent = try CString.Map.find best !removals with Not_found -> [] in
          removals := CString.Map.add best (d_line :: ent) !removals
        end
      end
    end
  in

  (* generate only the removals or only the additions for all hypotheses *)
  let half_diff old_ids o_map n_idents_in_lines n_map otype =
    let rec do_lines = function
      | [] -> ()
      | ids_in_line :: tl ->
        let nl_idents, new_rhs =
          try let ent = CString.Map.find (List.hd ids_in_line) n_map in
            ent.idents, ent.rhs_pp
          with Not_found -> [], (Pp.mt ()) in

        let rec get_ol_idents ol_idents old_rhs = function
          | [] -> List.rev ol_idents, old_rhs
          | ident :: tl ->
            try
              let o_ent = CString.Map.find ident o_map in
              let eq = (o_ent.rhs_pp = new_rhs) in
              let ol_idents = if eq then ident :: ol_idents else ol_idents in
              let old_rhs = if eq || old_rhs = None then Some o_ent.rhs_pp else old_rhs in
              get_ol_idents ol_idents old_rhs tl
            with Not_found -> get_ol_idents ol_idents old_rhs tl
        in

        let (ol_idents, old_rhs) = get_ol_idents [] None nl_idents in
        let old_rhs = Option.default (Pp.mt ()) old_rhs in

        let rhs_eq = old_rhs = new_rhs in
        (* if RHS differs, only highlight idents new to the context *)
        let filter_ol () = if rhs_eq then ol_idents else
          List.filter (fun ident -> CString.Map.mem ident o_map) nl_idents in
        if otype = `Added then begin
          let ol_idents = filter_ol () in
          gen_line ol_idents old_rhs  nl_idents new_rhs otype
        end else if not rhs_eq || List.length nl_idents <> List.length ol_idents then begin
          let ol_idents = filter_ol () in
          gen_line nl_idents new_rhs  ol_idents old_rhs otype
        end;
        do_lines tl
    in
    do_lines n_idents_in_lines
  in
  if show_removed () then
    (* note reversal of new and old *)
    half_diff (List.flatten n_idents_in_lines) n_map  o_idents_in_lines o_map `Removed;
  half_diff (List.flatten o_idents_in_lines) o_map  n_idents_in_lines n_map `Added;
  List.rev !rv

type goal = { ty: EConstr.t; env : Environ.env; sigma : Evd.evar_map; }

(* XXX: Port to proofview, one day. *)
(* open Proofview *)
module CDC = Context.Compacted.Declaration

let to_tuple : EConstr.compacted_declaration -> (Names.Id.t EConstr.binder_annot list * 'pc option * 'pc) =
  let open CDC in function
    | LocalAssum(idl, tm)   -> (idl, None, tm)
    | LocalDef(idl,tdef,tm) -> (idl, Some tdef, tm)

let make_goal env sigma g =
  let evi = Evd.find_undefined sigma g in
  let env = Evd.evar_filtered_env env evi in
  let ty  = Evd.evar_concl evi in
  { ty; env; sigma }

let pr_letype_env ?goal_concl_style env sigma ?impargs t =
  Ppconstr.pr_lconstr_expr env sigma
    (Constrextern.extern_type ?goal_concl_style env sigma ?impargs t)

let pp_of_type env sigma ty =
  pr_letype_env ~goal_concl_style:true env sigma ty

let pr_leconstr_env ?inctx ?scope env sigma t =
  Ppconstr.pr_lconstr_expr env sigma (Constrextern.extern_constr ?inctx ?scope env sigma t)

let pr_econstr_env ?inctx ?scope env sigma t =
  Ppconstr.pr_constr_expr env sigma (Constrextern.extern_constr ?inctx ?scope env sigma t)

let diff_concl ?og_s ng =
  let o_concl_pp = match og_s with
  | Some { ty = oty; env = oenv; sigma = osigma } -> pp_of_type oenv osigma oty
  | None -> Pp.mt()
  in
  let { ty = nty; env = nenv; sigma = nsigma } = ng in
  let n_concl_pp = pp_of_type nenv nsigma nty in

  let show_removed = Some (show_removed ()) in

  diff_pp_combined ~tokenize_string ?show_removed o_concl_pp n_concl_pp

(* fetch info from a goal, returning (idents, map, concl_pp) where
idents is a list with one entry for each hypothesis, in which each entry
is the list of idents on the lhs of the hypothesis.  map is a map from
ident to hyp_info reoords.  For example: for the hypotheses:
  b : bool
  n, m : nat

idents will be [ ["b"]; ["n"; "m"] ]

map will contain:
  "b" -> { ["b"], Pp.t for ": bool"; false }
  "n" -> { ["n"; "m"], Pp.t for ": nat"; false }
  "m" -> { ["n"; "m"], Pp.t for ": nat"; false }
 where the last two entries share the idents list.

concl_pp is the conclusion as a Pp.t
*)
let goal_info goal =
  let map = ref CString.Map.empty in
  let line_idents = ref [] in
  let build_hyp_info env sigma hyp =
    let (names, body, ty) = to_tuple hyp in
    let open Pp in
    let idents = List.map (fun x -> Names.Id.to_string x.Context.binder_name) names in

    line_idents := idents :: !line_idents;
    let mid = match body with
    | Some c ->
      let pb = pr_leconstr_env env sigma c in
      let pb = if EConstr.isCast sigma c then surround pb else pb in
      str " := " ++ pb
    | None -> mt() in
    let ts = pp_of_type env sigma ty in
    let rhs_pp = mid ++ str " : " ++ ts in

    let make_entry () = { idents; rhs_pp } in
    List.iter (fun ident -> map := (CString.Map.add ident (make_entry ()) !map); ()) idents
  in

  try
    let { ty=ty; env=env; sigma } = goal in
    (* compaction is usually desired [eg for better display] *)
    let hyps = Termops.compact_named_context sigma (EConstr.named_context env) in
    let () = List.iter (build_hyp_info env sigma) (List.rev hyps) in
    let concl_pp = pp_of_type env sigma ty in
    ( List.rev !line_idents, !map, concl_pp )
  with e when CErrors.noncritical e -> ([], !map, Pp.mt ())

let diff_goal_info ~short o_info n_info =
  let (o_idents_in_lines, o_hyp_map, o_concl_pp) = o_info in
  let (n_idents_in_lines, n_hyp_map, n_concl_pp) = n_info in
  let show_removed = Some (show_removed ()) in
  let concl_pp = diff_pp_combined ~tokenize_string ?show_removed o_concl_pp n_concl_pp in

  let hyp_diffs_list =
    if short then [] else diff_hyps o_idents_in_lines o_hyp_map n_idents_in_lines n_hyp_map in
  (hyp_diffs_list, concl_pp)

let unwrap g_s =
  match g_s with
  | Some g_s -> goal_info g_s
  | None -> ([], CString.Map.empty, Pp.mt ())

let diff_goal ?(short=false) ?og_s ng =
  diff_goal_info ~short (unwrap og_s) (goal_info ng)

(*** Code to determine which calls to compare between the old and new proofs ***)

module GoalMap = Evar.Map

let goal_to_evar g sigma = Names.Id.to_string (Termops.evar_suggested_name (Global.env ()) sigma g)

open Evar.Set

[@@@ocaml.warning "-32"]
let db_goal_map op np ng_to_og =
  let pr_goals title prf =
    Printf.printf "%s: " title;
    let Proof.{goals;sigma} = Proof.data prf in
    List.iter (fun g -> Printf.printf "%d -> %s  " (Evar.repr g) (goal_to_evar g sigma)) goals;
    let gs = diff (Proof.all_goals prf) (List.fold_left (fun s g -> add g s) empty goals) in
    List.iter (fun g -> Printf.printf "%d  " (Evar.repr g)) (elements gs);
  in

  pr_goals "New Goals" np;
  (match op with
  | Some op ->
    pr_goals "\nOld Goals" op
  | None -> ());
  Printf.printf "\nGoal map: ";
  GoalMap.iter (fun ng og -> Printf.printf "%d -> %d  " (Evar.repr ng) (Evar.repr og)) ng_to_og;
  let unmapped = ref (Proof.all_goals np) in
  GoalMap.iter (fun ng _ -> unmapped := Evar.Set.remove ng !unmapped) ng_to_og;
  if Evar.Set.cardinal !unmapped > 0 then begin
    Printf.printf "\nUnmapped goals: ";
    Evar.Set.iter (fun ng -> Printf.printf "%d  " (Evar.repr ng)) !unmapped
  end;
  Printf.printf "\n"
[@@@ocaml.warning "+32"]

type goal_map = Evd.evar_map * Evar.t Evar.Map.t

let map_goal g (osigma, map) = match GoalMap.find_opt g map with
| None -> None
| Some g -> Some (make_goal (Global.env ()) osigma g)
(* if not found, returning None treats the goal as new and it will be diff highlighted;
    returning Some { it = g; sigma = sigma } will compare the new goal
    to itself and it won't be highlighted *)

(* Create a map from new goals to old goals for proof diff. *)
let make_goal_map op np =
  let ogs = Proof.all_goals op in
  let ngs = Proof.all_goals np in
  let { Proof.sigma } = Proof.data np in

  let fold_old_evar oevk acc =
    match Evd.find sigma oevk with
    | exception Not_found -> acc (* evar got deleted, maybe by Optimize Proof? *)
    | EvarInfo evi -> match Evd.evar_body evi with
      | Evar_empty ->
        if Evar.Set.mem oevk ngs then Evar.Map.add oevk oevk acc
        else
          (* lost evar, probably a bug but we don't want to assert false in proof diffs *)
          acc
      | Evar_defined body ->
        let evars = Evd.evars_of_term sigma body in
        let evars =
          (* remove lost evars (not sure if worth doing) *)
          Evar.Set.inter evars ngs
        in
        Evar.Map.union (fun _ x _ -> Some x)
          acc
          (Evar.Map.bind (fun _ -> oevk) evars)
  in
  Evar.Set.fold fold_old_evar ogs Evar.Map.empty

let make_goal_map op np =
  let map = make_goal_map op np in
  ((Proof.data op).Proof.sigma, map)

let notify_proof_diff_failure msg =
  Feedback.msg_notice Pp.(str "Unable to compute diffs: " ++ str msg)

let diff_proofs ~diff_opt ?old proof =
  let pp_proof p =
    let sigma, env = Proof.get_proof_context p in
    let pprf = Proof.partial_proof p in
    Pp.prlist_with_sep Pp.fnl (pr_econstr_env env sigma) pprf in
  match diff_opt with
  | DiffOff -> pp_proof proof
  | _ -> begin
      try
        let n_pp = pp_proof proof in
        let o_pp = match old with
          | None -> Pp.mt()
          | Some old -> pp_proof old in
        let show_removed = Some (diff_opt = DiffRemoved) in
        Pp_diff.diff_pp_combined ~tokenize_string ?show_removed o_pp n_pp
      with Pp_diff.Diff_Failure msg ->
        notify_proof_diff_failure msg;
        pp_proof proof
    end
