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

Diffs are computed for the hypotheses and conclusion of each goal in the new
proof with its matching goal in the old proof.

Diffs can be enabled in coqtop with 'Set Diffs "on"|"off"|"removed"' or
'-diffs on|off|removed' on the OS command line.  In CoqIDE, they can be enabled
from the View menu.  The "on" option shows only the new item with added text,
while "removed" shows each modified item twice--once with the old value showing
removed text and once with the new value showing added text.

In CoqIDE, colors and highlights can be set in the Edit/Preferences/Tags panel.
For coqtop, these can be set through the COQ_COLORS environment variable.

Limitations/Possible enhancements:

- coqtop colors were chosen for white text on a black background.  They're
not the greatest.  I didn't want to change the existing green highlight.
Suggestions welcome.

- coqtop underlines removed text because (per Wikipedia) the ANSI escape code
for strikeout is not commonly supported (it didn't work on my system).  CoqIDE
uses strikeout on removed text.
*)

open Pp_diff

let diff_option = ref `OFF

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
      List.concat (List.map (contains orig) old_ids_uo)
    in

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
let process_goal_concl sigma g : Constr.t * Environ.env =
  let env  = Goal.V82.env   sigma g in
  let ty   = Goal.V82.concl sigma g in
  let ty   = EConstr.to_constr sigma ty in
  (ty, env)

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

let diff_concl ?og_s nsigma ng =
  let open Evd in
  let o_concl_pp = match og_s with
    | Some { it=og; sigma=osigma } ->
      let (oty, oenv) = process_goal_concl osigma og in
      pp_of_type oenv osigma oty
    | None -> Pp.mt()
  in
  let (nty, nenv) = process_goal_concl nsigma ng in
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

let unwrap g_s =
  match g_s with
  | Some g_s ->
    let goal = Evd.sig_it g_s in
    let sigma = Refiner.project g_s in
    goal_info goal sigma
  | None -> ([], StringMap.empty, Pp.mt ())

let diff_goal_ide og_s ng nsigma =
  diff_goal_info (unwrap og_s) (goal_info ng nsigma)

let diff_goal ?og_s ng ns =
  let (hyps_pp_list, concl_pp) = diff_goal_info (unwrap og_s) (goal_info ng ns) in
  let open Pp in
  v 0 (
    (hyp_list_to_pp hyps_pp_list) ++ cut () ++
    str "============================" ++ cut () ++
    concl_pp);;


(*** Code to determine which calls to compare between the old and new proofs ***)

open Constrexpr
open Glob_term
open Names
open CAst

(* Compare the old and new proof trees to identify the correspondence between
new and old goals.  Returns a map from the new evar name to the old,
e.g. "Goal2" -> "Goal1".  Assumes that proof steps only rewrite CEvar nodes
and that CEvar nodes cannot contain other CEvar nodes.

The comparison works this way:
1. Traverse the old and new trees together (ogname = "", ot != nt):
- if the old and new trees both have CEvar nodes, add an entry to the map from
  the new evar name to the old evar name.  (Position of goals is preserved but
  evar names may not be--see below.)
- if the old tree has a CEvar node and the new tree has a different type of node,
  we've found a changed goal.  Set ogname to the evar name of the old goal and
  go to step 2.
- any other mismatch violates the assumptions, raise an exception
2. Traverse the new tree from the point of the difference (ogname <> "", ot = nt).
- if the node is a CEvar, generate a map entry from the new evar name to ogname.

Goal ids for unchanged goals appear to be preserved across proof steps.
However, the evar name associated with a goal id may change in a proof step
even if that goal is not changed by the tactic.  You can see this by enabling
the call to db_goal_map and entering the following:

  Parameter P : nat -> Prop.
  Goal (P 1 /\ P 2 /\ P 3) /\ P 4.
  split.
  Show Proof.
  split.
  Show Proof.

  Which gives you this summarized output:

  > split.
  New Goals: 3 -> Goal  4 -> Goal0              <--- goal 4 is "Goal0"
  Old Goals: 1 -> Goal
  Goal map: 3 -> 1  4 -> 1
  > Show Proof.
  (conj ?Goal ?Goal0)                           <--- goal 4 is the rightmost goal in the proof
  > split.
  New Goals: 6 -> Goal0  7 -> Goal1  4 -> Goal  <--- goal 4 is now "Goal"
  Old Goals: 3 -> Goal  4 -> Goal0
  Goal map: 6 -> 3  7 -> 3
  > Show Proof.
  (conj (conj ?Goal0 ?Goal1) ?Goal)             <--- goal 4 is still the rightmost goal in the proof
 *)
let match_goals ot nt =
  let nevar_to_oevar = ref StringMap.empty in
  (* ogname is "" when there is no difference on the current path.
     It's set to the old goal's evar name once a rewitten goal is found,
     at which point the code only searches for the replacing goals
     (and ot is set to nt). *)
  let rec match_goals_r ogname ot nt =
    let constr_expr ogname exp exp2 =
      match_goals_r ogname exp.v exp2.v
    in
    let constr_expr_opt ogname exp exp2 =
      match exp, exp2 with
      | Some expa, Some expb -> constr_expr ogname expa expb
      | None, None -> ()
      | _, _ -> raise (Diff_Failure "Unable to match goals betwen old and new proof states (1)")
    in
    let local_binder_expr ogname exp exp2 =
      match exp, exp2 with
      | CLocalAssum (nal,bk,ty), CLocalAssum(nal2,bk2,ty2) ->
        constr_expr ogname ty ty2
      | CLocalDef (n,c,t), CLocalDef (n2,c2,t2) ->
        constr_expr ogname c c2;
        constr_expr_opt ogname t t2
      | CLocalPattern p, CLocalPattern p2 ->
        let (p,ty), (p2,ty2) = p.v,p2.v in
        constr_expr_opt ogname ty ty2
      | _, _ -> raise (Diff_Failure "Unable to match goals betwen old and new proof states (2)")
    in
    let recursion_order_expr ogname exp exp2 =
      match exp, exp2 with
      | CStructRec, CStructRec -> ()
      | CWfRec c, CWfRec c2 ->
        constr_expr ogname c c2
      | CMeasureRec (m,r), CMeasureRec (m2,r2) ->
        constr_expr ogname m m2;
        constr_expr_opt ogname r r2
      | _, _ -> raise (Diff_Failure "Unable to match goals betwen old and new proof states (3)")
    in
    let fix_expr ogname exp exp2 =
      let (l,(lo,ro),lb,ce1,ce2), (l2,(lo2,ro2),lb2,ce12,ce22) = exp,exp2 in
        recursion_order_expr ogname ro ro2;
        List.iter2 (local_binder_expr ogname) lb lb2;
        constr_expr ogname ce1 ce12;
        constr_expr ogname ce2 ce22
    in
    let cofix_expr ogname exp exp2 =
      let (l,lb,ce1,ce2), (l2,lb2,ce12,ce22) = exp,exp2 in
        List.iter2 (local_binder_expr ogname) lb lb2;
        constr_expr ogname ce1 ce12;
        constr_expr ogname ce2 ce22
    in
    let case_expr ogname exp exp2 =
      let (ce,l,cp), (ce2,l2,cp2) = exp,exp2 in
      constr_expr ogname ce ce2
    in
    let branch_expr ogname exp exp2 =
      let (cpe,ce), (cpe2,ce2) = exp.v,exp2.v in
        constr_expr ogname ce ce2
    in
    let constr_notation_substitution ogname exp exp2 =
      let (ce, cel, cp, lb), (ce2, cel2, cp2, lb2) = exp, exp2 in
      List.iter2 (constr_expr ogname) ce ce2;
      List.iter2 (fun a a2 -> List.iter2 (constr_expr ogname) a a2) cel cel2;
      List.iter2 (fun a a2 -> List.iter2 (local_binder_expr ogname) a a2) lb lb2
    in
    begin
    match ot, nt with
    | CRef (ref,us), CRef (ref2,us2) -> ()
    | CFix (id,fl), CFix (id2,fl2) ->
      List.iter2 (fix_expr ogname) fl fl2
    | CCoFix (id,cfl), CCoFix (id2,cfl2) ->
      List.iter2 (cofix_expr ogname) cfl cfl2
    | CProdN (bl,c2), CProdN (bl2,c22)
    | CLambdaN (bl,c2), CLambdaN (bl2,c22) ->
      List.iter2 (local_binder_expr ogname) bl bl2;
      constr_expr ogname c2 c22
    | CLetIn (na,c1,t,c2), CLetIn (na2,c12,t2,c22) ->
      constr_expr ogname c1 c12;
      constr_expr_opt ogname t t2;
      constr_expr ogname c2 c22
    | CAppExpl ((isproj,ref,us),args), CAppExpl ((isproj2,ref2,us2),args2) ->
      List.iter2 (constr_expr ogname) args args2
    | CApp ((isproj,f),args), CApp ((isproj2,f2),args2) ->
      constr_expr ogname f f2;
      List.iter2 (fun a a2 -> let (c, _) = a and (c2, _) = a2 in
          constr_expr ogname c c2) args args2
    | CRecord fs, CRecord fs2 ->
      List.iter2 (fun a a2 -> let (_, c) = a and (_, c2) = a2 in
          constr_expr ogname c c2) fs fs2
    | CCases (sty,rtnpo,tms,eqns), CCases (sty2,rtnpo2,tms2,eqns2) ->
        constr_expr_opt ogname rtnpo rtnpo2;
        List.iter2 (case_expr ogname) tms tms2;
        List.iter2 (branch_expr ogname) eqns eqns2
    | CLetTuple (nal,(na,po),b,c), CLetTuple (nal2,(na2,po2),b2,c2) ->
      constr_expr_opt ogname po po2;
      constr_expr ogname b b2;
      constr_expr ogname c c2
    | CIf (c,(na,po),b1,b2), CIf (c2,(na2,po2),b12,b22) ->
      constr_expr ogname c c2;
      constr_expr_opt ogname po po2;
      constr_expr ogname b1 b12;
      constr_expr ogname b2 b22
    | CHole (k,naming,solve), CHole (k2,naming2,solve2) -> ()
    | CPatVar _, CPatVar _ -> ()
    | CEvar (n,l), CEvar (n2,l2) ->
      let oevar = if ogname = "" then Id.to_string n else ogname in
      nevar_to_oevar := StringMap.add (Id.to_string n2) oevar !nevar_to_oevar;
      List.iter2  (fun x x2 -> let (_, g) = x and (_, g2) = x2 in constr_expr ogname g g2)  l l2
    | CEvar (n,l), nt' ->
      (* pass down the old goal evar name *)
      match_goals_r (Id.to_string n) nt' nt'
    | CSort s, CSort s2 -> ()
    | CCast (c,c'), CCast (c2,c'2) ->
      constr_expr ogname c c2;
      (match c', c'2 with
      | CastConv a, CastConv a2
      | CastVM a, CastVM a2
      | CastNative a, CastNative a2 ->
        constr_expr ogname a a2
      | CastCoerce, CastCoerce -> ()
      | _, _ -> raise (Diff_Failure "Unable to match goals betwen old and new proof states (4)"))
    | CNotation (ntn,args), CNotation (ntn2,args2) ->
      constr_notation_substitution ogname args args2
    | CGeneralization (b,a,c), CGeneralization (b2,a2,c2) ->
      constr_expr ogname c c2
    | CPrim p, CPrim p2 -> ()
    | CDelimiters (key,e), CDelimiters (key2,e2) ->
      constr_expr ogname e e2
    | _, _ -> raise (Diff_Failure "Unable to match goals betwen old and new proof states (5)")
    end
  in

  (match ot with
  | Some ot -> match_goals_r "" ot nt
  | None -> ());
  !nevar_to_oevar


let to_constr p =
  let open CAst in
  let pprf = Proof.partial_proof p in
  (* pprf generally has only one element, but it may have more in the derive plugin *)
  let t = List.hd pprf in
  let sigma, env = Pfedit.get_current_context ~p () in
  let x = Constrextern.extern_constr false env sigma t in  (* todo: right options?? *)
  x.v


module GoalMap = Evar.Map

let goal_to_evar g sigma = Id.to_string (Termops.pr_evar_suggested_name g sigma)

[@@@ocaml.warning "-32"]
let db_goal_map op np ng_to_og =
  Printf.printf "New Goals: ";
  let (ngoals,_,_,_,nsigma) = Proof.proof np in
  List.iter (fun ng -> Printf.printf "%d -> %s  " (Evar.repr ng) (goal_to_evar ng nsigma)) ngoals;
  (match op with
  | Some op ->
    let (ogoals,_,_,_,osigma) = Proof.proof op in
    Printf.printf "\nOld Goals: ";
    List.iter (fun og -> Printf.printf "%d -> %s  " (Evar.repr og) (goal_to_evar og osigma)) ogoals
  | None -> ());
  Printf.printf "\nGoal map: ";
  GoalMap.iter (fun og ng -> Printf.printf "%d -> %d  " (Evar.repr og) (Evar.repr ng)) ng_to_og;
  Printf.printf "\n"
[@@@ocaml.warning "+32"]

(* Create a map from new goals to old goals for proof diff.  The map only
 has entries for new goals that are not the same as the corresponding old
 goal; there are no entries for unchanged goals.

 It proceeds as follows:
 1. Find the goal ids that were removed from the old proof and that were
 added in the new proof.  If the same goal id is present in both proofs
 then conclude the goal is unchanged (assumption).

 2. The code assumes that proof changes only take the form of replacing
 one or more goal symbols (CEvars) with new terms.  Therefore:
 - if there are no removals, the proofs are the same.
 - if there are removals but no additions, then there are no new goals
   that aren't the same as their associated old goals.  For the both of
   these cases, the map is empty because there are no new goals that differ
   from their old goals
 - if there is only one removal, then any added goals should be mapped to
   the removed goal.
 - if there are more than 2 removals and more than one addition, call
   match_goals to get a map between old and new evar names, then use this
   to create the map from new goal ids to old goal ids for the differing goals.
*)
let make_goal_map_i op np =
  let ng_to_og = ref GoalMap.empty in
  match op with
  | None -> !ng_to_og
  | Some op ->
    let open Goal.Set in
    let ogs = Proof.all_goals op in
    let ngs = Proof.all_goals np in
    let rem_gs = diff ogs ngs in
    let num_rems = cardinal rem_gs in
    let add_gs = diff ngs ogs in
    let num_adds = cardinal add_gs in

    if num_rems = 0 then
      !ng_to_og (* proofs are the same *)
    else if num_adds = 0 then
      !ng_to_og (* only removals *)
    else if num_rems = 1 then begin
      (* only 1 removal, some additions *)
      let removed_g = List.hd (elements rem_gs) in
      Goal.Set.iter (fun x -> ng_to_og := GoalMap.add x removed_g !ng_to_og) add_gs;
      !ng_to_og
    end else begin
      (* >= 2 removals, >= 1 addition, need to match *)
      let nevar_to_oevar = match_goals (Some (to_constr op)) (to_constr np) in

      let oevar_to_og = ref StringMap.empty in
      let (_,_,_,_,osigma) = Proof.proof op in
      List.iter (fun og -> oevar_to_og := StringMap.add (goal_to_evar og osigma) og !oevar_to_og)
          (Goal.Set.elements rem_gs);

      try
        let (_,_,_,_,nsigma) = Proof.proof np in
        let get_og ng =
          let nevar = goal_to_evar ng nsigma in
          let oevar = StringMap.find nevar nevar_to_oevar in
          let og = StringMap.find oevar !oevar_to_og in
          og
        in
        Goal.Set.iter (fun ng -> ng_to_og := GoalMap.add ng (get_og ng) !ng_to_og) add_gs;
        !ng_to_og
      with Not_found -> raise (Diff_Failure "Unable to match goals betwen old and new proof states (6)")
    end

let make_goal_map op np =
  let ng_to_og = make_goal_map_i op np in
  (*db_goal_map op np ng_to_og;*)
  ng_to_og
