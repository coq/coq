(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

let debug_scheduler = CDebug.create ~name:"scheduler"

let log msg =
  if CDebug.get_debug_level "scheduler" >= 2 then
    Format.eprintf "@[%s@]@\n%!" msg

type vernac_classification =
  ParsingEffect | StateEffect

let classify_vernac ast =
  let open Vernacextend in
  match Vernac_classifier.classify_vernac ast with
  | VtSideff (_, VtNow) -> ParsingEffect
  | _ -> StateEffect

module SM = Map.Make (Stateid)

(* TODO should we remove ASTs from here? *)
type task =
  | Skip of sentence_id
  | Exec of sentence_id * ast
  | OpaqueProof of { terminator_id: sentence_id;
                     opener_id: sentence_id;
                     tasks_ids : sentence_id list;
                   }
  | Query of sentence_id * ast
(*
  | SubProof of ast list
  | ModuleWithSignature of ast list
*)
type proof_block = {
  proof_sentences : sentence_id list;
  opener_id : sentence_id;
}

type state = {
  document_scope : sentence_id list; (* List of sentences whose effect scope is the document *)
  proof_blocks : proof_block list;
  section_depth : int;
}

let initial_state = {
  document_scope = [];
  proof_blocks = [];
  section_depth = 0;
}

type schedule = {
  tasks : (sentence_id option * task) SM.t;
  dependencies : Stateid.Set.t SM.t;
}

let initial_schedule = {
  tasks = SM.empty;
  dependencies = SM.empty;
}

let push_proof_sentence id block =
  { block with proof_sentences = id :: block.proof_sentences }

let push_id id st =
  match st.proof_blocks with
  | [] -> { st with document_scope = id :: st.document_scope }
  | l::q -> { st with proof_blocks = push_proof_sentence id l :: q }

(* Not sure what the base_id for nested lemmas should be, e.g.
Lemma foo : X.
Proof.
Definition x := True.
intros ...
Lemma bar : Y. <- What should the base_id be for this command? -> 83
*)
let base_id st =
  let rec aux = function
  | [] -> (match st.document_scope with hd :: _ -> Some hd | [] -> None)
  | block :: l ->
    begin match block.proof_sentences with
    | [] -> aux l
    | hd :: _ -> Some hd
    end
  in
  aux st.proof_blocks

let open_proof_block id st =
  let st = push_id id st in
  let block = { proof_sentences = []; opener_id = id } in
  { st with proof_blocks = block :: st.proof_blocks }

let extrude_side_effect id st =
  let document_scope = id :: st.document_scope in
  let proof_blocks = List.map (push_proof_sentence id) st.proof_blocks in
  { st with document_scope; proof_blocks }

let flatten_proof_block st =
  match st.proof_blocks with
  | [] -> st
  | [block] ->
    let document_scope = CList.uniquize @@ block.proof_sentences @ st.document_scope in
    { st with document_scope; proof_blocks = [] }
  | block1 :: block2 :: tl -> (* Nested proofs. TODO check if we want to extrude one level or directly to document scope *)
    let proof_sentences = CList.uniquize @@ block1.proof_sentences @ block2.proof_sentences in
    let block2 = { block2 with proof_sentences } in
    { st with proof_blocks = block2 :: tl }

(*
Lemma foo : XX.
Proof.
Definition y := True.
Lemma bar : y.
Proof.
exact I.
Qed.

apply bar.

Qed.

-> We don't delegate

129: Exec(127, Qed)
122: Exec(121, Lemma bar : XX)

--> We delegate only pure proofs
*)

(* FIXME handle commands with side effects followed by `Abort` *)
let push_state id ast st =
  let open Vernacextend in
  match Vernac_classifier.classify_vernac ast with
  | VtStartProof _ -> base_id st, open_proof_block id st, Exec(id,ast)
  | VtQed (VtKeep (VtKeepAxiom | VtKeepOpaque)) when st.section_depth = 0 -> (* TODO do not delegate if command with side effect inside the proof or nested lemmas *)
    begin match st.proof_blocks with
    | [] ->
      (* can happen on ill-formed documents *)
      base_id st, push_id id st, Exec(id,ast)
    | block :: pop ->
      let terminator_id = id in
      let tasks_ids = List.rev block.proof_sentences in
      let st = { st with proof_blocks = pop } in
      base_id st, push_id id st, OpaqueProof { terminator_id; opener_id = block.opener_id; tasks_ids }
    end
  | VtQed _ ->
    let st = flatten_proof_block st in
    base_id st, push_id id st, Exec(id,ast)
  | (VtQuery | VtProofStep _) ->
    base_id st, push_id id st, Exec(id, ast)
  | VtSideff _ ->
    base_id st, extrude_side_effect id st, Exec(id,ast)
  | _ -> assert false

let string_of_task (task_id,(base_id,task)) =
  let s = match task with
  | Skip id -> "Skip " ^ Stateid.to_string id
  | Exec (id, ast) -> "Exec " ^ Stateid.to_string id ^ " (" ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^ ")"
  | OpaqueProof { terminator_id; tasks_ids } -> "OpaqueProof [" ^ Stateid.to_string terminator_id ^ " | " ^ String.concat "," (List.map Stateid.to_string tasks_ids) ^ "]"
  | Query(id,ast) -> "Query " ^ Stateid.to_string id
  in
  Format.sprintf "[%s] : [%s] -> %s" (Stateid.to_string task_id) (Option.cata Stateid.to_string "init" base_id) s

let string_of_state st =
  let scopes = (List.map (fun b -> b.proof_sentences) st.proof_blocks) @ [st.document_scope] in
  String.concat "|" (List.map (fun l -> String.concat " " (List.map Stateid.to_string l)) scopes)

let schedule_sentence (id,oast) st schedule =
  let base, st, task = match oast with
    | Some ast ->
      let open Vernacexpr in
      let (base, st, task) = push_state id ast st in
      begin match ast.CAst.v.expr with
      | VernacBeginSection _ ->
        (base, { st with section_depth = st.section_depth + 1 }, task)
      | VernacEndSegment _ ->
        (base, { st with section_depth = max 0 (st.section_depth - 1) }, task)
      | _ -> (base, st, task)
      end
    | None -> base_id st, st, Skip id
  in
  log @@ "Scheduled " ^ (Stateid.to_string id) ^ " based on " ^ (match base with Some id -> Stateid.to_string id | None -> "no state");
  log @@ string_of_task (id, (base, task));
  log @@ "New scheduler state: " ^ string_of_state st;
  let tasks = SM.add id (base, task) schedule.tasks in
  let add_dep deps x id =
    let upd = function
    | Some deps -> Some (Stateid.Set.add id deps)
    | None -> Some (Stateid.Set.singleton id)
    in
    SM.update x upd deps
  in
  let dependencies =
    List.fold_left (fun deps l -> List.fold_left (fun deps x -> add_dep deps x id) deps l) schedule.dependencies (List.map (fun b -> b.proof_sentences) st.proof_blocks@[st.document_scope]) (* TODO simplify *)
  in
  st, { tasks; dependencies }

let task_for_sentence schedule id =
  match SM.find_opt id schedule.tasks with
  | Some x -> x
  | None -> CErrors.anomaly Pp.(str "cannot find schedule for sentence " ++ Stateid.print id)

let dependents schedule id =
  match SM.find_opt id schedule.dependencies with
  | Some x -> x
  | None -> CErrors.anomaly Pp.(str "cannot find dependents for sentence " ++ Stateid.print id)

(** Dependency computation algo *)
(*
{}
1. Definition y := ...
{{1}}
2. Lemma x : T.
{{},{1,2}}
3. Proof using v.
{{3},{1,2}}
4. tac1.
{{3,4},{1,2}}
5. Definition f := Type.
{{3,4,5},{1,2,5}}
6. Defined.    ||     6. Qed.
{{1,2,3,4,5,6}}  ||     {{1,2,5,6}}
7. Check x.
*)

let string_of_schedule schedule =
  "Task\n" ^
  String.concat "\n" @@ List.map string_of_task @@ SM.bindings schedule.tasks
