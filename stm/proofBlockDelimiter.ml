(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Stm

module Util : sig

val simple_goal : Evd.evar_map -> Goal.goal -> Goal.goal list -> bool
val is_focused_goal_simple : Stateid.t -> [ `Simple of Goal.goal list | `Not ]

type 'a until = [ `Stop | `Found of static_block_declaration | `Cont of 'a ]

val crawl :
  document_view -> ?init:document_node option ->
  ('a -> document_node -> 'a until) -> 'a ->
    static_block_declaration option

val unit_val : Stm.DynBlockData.t
val of_bullet_val : Vernacexpr.bullet -> Stm.DynBlockData.t
val to_bullet_val : Stm.DynBlockData.t -> Vernacexpr.bullet
val of_vernac_expr_val : Vernacexpr.vernac_expr -> Stm.DynBlockData.t
val to_vernac_expr_val : Stm.DynBlockData.t -> Vernacexpr.vernac_expr

end = struct

let unit_tag = DynBlockData.create "unit"
let unit_val = DynBlockData.Easy.inj () unit_tag

let of_bullet_val, to_bullet_val = DynBlockData.Easy.make_dyn "bullet"
let of_vernac_expr_val, to_vernac_expr_val = DynBlockData.Easy.make_dyn "vernac_expr"

let simple_goal sigma g gs =
  let open Evar in
  let open Evd in
  let open Evarutil in
  let evi = Evd.find sigma g in
  Set.is_empty (evars_of_term evi.evar_concl) &&
  Set.is_empty (evars_of_filtered_evar_info (nf_evar_info sigma evi)) &&
  not (List.exists (Proofview.depends_on sigma g) gs)

let is_focused_goal_simple id =
  match state_of_id id with
  | `Expired | `Error _ | `Valid None -> `Not
  | `Valid (Some { proof }) ->
       let proof = Proof_global.proof_of_state proof in
       let focused, r1, r2, r3, sigma = Proof.proof proof in
       let rest = List.(flatten (map (fun (x,y) -> x @ y) r1)) @ r2 @ r3 in
       if List.for_all (fun x -> simple_goal sigma x rest) focused
       then `Simple focused
       else `Not

type 'a until = [ `Stop | `Found of static_block_declaration | `Cont of 'a ]

let crawl { entry_point; prev_node } ?(init=Some entry_point) f acc =
  let rec crawl node acc =
    match node with
    | None -> None
    | Some node ->
        match f acc node with
        | `Stop -> None
        | `Found x -> Some x
        | `Cont acc -> crawl (prev_node node) acc in
  crawl init acc

end

include Util

(* ****************** - foo - bar - baz *********************************** *)

let static_bullet ({ entry_point; prev_node } as view) =
  match entry_point.ast with
  | Vernacexpr.VernacBullet b ->
      let base = entry_point.indentation in
      let last_tac = prev_node entry_point in
      crawl view ~init:last_tac (fun prev node ->
        if node.indentation < base then `Stop else
        if node.indentation > base then `Cont node else
        match node.ast with
        | Vernacexpr.VernacBullet b' when b = b' ->
          `Found { block_stop = entry_point.id; block_start = prev.id;
                   dynamic_switch = node.id; carry_on_data = of_bullet_val b }
        | _ -> `Stop) entry_point
  | _ -> assert false

let dynamic_bullet { dynamic_switch = id; carry_on_data = b } =
  match is_focused_goal_simple id with
  | `Simple focused ->
      `ValidBlock {
         base_state = id;
         goals_to_admit = focused;
         recovery_command = Some (Vernacexpr.VernacBullet (to_bullet_val b))
      }
  | `Not -> `Leaks

let () = register_proof_block_delimiter
  "bullet" static_bullet dynamic_bullet

(* ******************** { block } ***************************************** *)
  
let static_curly_brace ({ entry_point; prev_node } as view) =
  assert(entry_point.ast = Vernacexpr.VernacEndSubproof);
  crawl view (fun (nesting,prev) node ->
    match node.ast with
    | Vernacexpr.VernacSubproof _ when nesting = 0 ->
      `Found { block_stop = entry_point.id; block_start = prev.id;
               dynamic_switch = node.id; carry_on_data = unit_val }
    | Vernacexpr.VernacSubproof _ ->
      `Cont (nesting - 1,node)
    | Vernacexpr.VernacEndSubproof ->
      `Cont (nesting + 1,node)
    | _ -> `Cont (nesting,node)) (-1, entry_point)

let dynamic_curly_brace { dynamic_switch = id } =
  match is_focused_goal_simple id with
  | `Simple focused ->
      `ValidBlock {
         base_state = id;
         goals_to_admit = focused;
         recovery_command = Some Vernacexpr.VernacEndSubproof
      }
  | `Not -> `Leaks

let () = register_proof_block_delimiter
  "curly" static_curly_brace dynamic_curly_brace

(* ***************** par: ************************************************* *)

let static_par { entry_point; prev_node } =
  match prev_node entry_point with
  | None -> None
  | Some { id = pid } ->
      Some { block_stop = entry_point.id; block_start = pid;
             dynamic_switch = pid; carry_on_data = unit_val }

let dynamic_par { dynamic_switch = id } =
  match is_focused_goal_simple id with
  | `Simple focused ->
      `ValidBlock {
         base_state = id;
         goals_to_admit = focused;
         recovery_command = None;
      }
  | `Not -> `Leaks

let () = register_proof_block_delimiter "par" static_par dynamic_par

(* ***************** simple indentation *********************************** *)

let static_indent ({ entry_point; prev_node } as view) =
   Printf.eprintf "@%d\n" (Stateid.to_int entry_point.id);
   match prev_node entry_point with
   | None -> None
   | Some last_tac ->
      if last_tac.indentation <= entry_point.indentation then None
      else
        crawl view ~init:(Some last_tac) (fun prev node ->
        if node.indentation >= last_tac.indentation then `Cont node
        else 
          `Found { block_stop = entry_point.id; block_start = node.id;
                   dynamic_switch = node.id;
                   carry_on_data = of_vernac_expr_val entry_point.ast }
        ) last_tac

let dynamic_indent { dynamic_switch = id; carry_on_data = e } =
  Printf.eprintf "%s\n" (Stateid.to_string id);
  match is_focused_goal_simple id with
  | `Simple [] -> `Leaks
  | `Simple focused ->
      let but_last = List.tl (List.rev focused) in 
      `ValidBlock {
         base_state = id;
         goals_to_admit = but_last;
         recovery_command = Some (to_vernac_expr_val e);
      }
  | `Not -> `Leaks

let () = register_proof_block_delimiter "indent" static_indent dynamic_indent

