(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


(* tag is the tag to be hooked, item is the item covered by this tag, make_menu
 *  * is the template for building menu if needed, sel_cb is the callback if
 *  there
 *   * is a selection o said menu, hover_cb is the callback when there is only
 *    * hovering *)
let hook_tag_cb tag menu_content sel_cb hover_cb =
  ignore (tag#connect#event ~callback:
            (fun ~origin evt it ->
               let iter = new GText.iter it in
               let start = iter#backward_to_tag_toggle (Some tag) in
               let stop = iter#forward_to_tag_toggle (Some tag) in
               match GdkEvent.get_type evt with
                 | `BUTTON_PRESS ->
                     let ev = GdkEvent.Button.cast evt in
                     if (GdkEvent.Button.button ev) <> 3 then false else begin
                       let ctxt_menu = GMenu.menu () in
                       let factory = new GMenu.factory ctxt_menu in
                       List.iter
                         (fun (text,cmd) -> ignore (factory#add_item text ~callback:(sel_cb cmd)))
                         menu_content;
                       ctxt_menu#popup ~button:3 ~time:(GdkEvent.Button.time ev);
                       true
                     end
                 | `MOTION_NOTIFY ->
                     hover_cb start stop; false
                 | _ -> false))

let mode_tactic sel_cb (proof:GText.view) goals hints = match goals with
  | [] -> assert false
  | { Interface.goal_hyp = hyps; Interface.goal_ccl = cur_goal; } :: rem_goals ->
      let on_hover sel_start sel_stop =
        proof#buffer#remove_tag
          ~start:proof#buffer#start_iter
          ~stop:sel_start
          Tags.Proof.highlight;
        proof#buffer#remove_tag
          ~start:sel_stop
          ~stop:proof#buffer#end_iter
          Tags.Proof.highlight;
        proof#buffer#apply_tag ~start:sel_start ~stop:sel_stop Tags.Proof.highlight
      in
      let goals_cnt = List.length rem_goals + 1 in
      let head_str = Printf.sprintf
        "%d subgoal%s\n" goals_cnt (if 1 < goals_cnt then "" else "s")
      in
      let goal_str index total = Printf.sprintf
        "______________________________________(%d/%d)\n" index total
      in
      (* Insert current goal and its hypotheses *)
      let hyps_hints, goal_hints = match hints with
      | None -> [], []
      | Some (hl, h) -> (hl, h)
      in
      let rec insert_hyp hints hs = match hs with
      | [] -> ()
      | hyp :: hs ->
        let tags, rem_hints = match hints with
        | [] -> [], []
        | hint :: hints ->
          let tag = proof#buffer#create_tag [] in
          let () = hook_tag_cb tag hint sel_cb on_hover in
          [tag], hints
        in
        let () = proof#buffer#insert ~tags (hyp ^ "\n") in
        insert_hyp rem_hints hs
      in
      let () = proof#buffer#insert head_str in
      let () = insert_hyp hyps_hints hyps in
      let () =
        let tags = Tags.Proof.goal :: if goal_hints <> [] then
          let tag = proof#buffer#create_tag [] in
          let () = hook_tag_cb tag goal_hints sel_cb on_hover in
          [tag]
          else []
        in
        proof#buffer#insert (goal_str 1 goals_cnt);
        proof#buffer#insert ~tags cur_goal;
	proof#buffer#insert "\n"
      in
      (* Insert remaining goals (no hypotheses) *)
      let fold_goal i _ { Interface.goal_ccl = g } =
        proof#buffer#insert (goal_str i goals_cnt);
        proof#buffer#insert (g ^ "\n")
      in
      let () = Minilib.list_fold_left_i fold_goal 2 () rem_goals in

      ignore(proof#buffer#place_cursor
               ~where:(proof#buffer#end_iter#backward_to_tag_toggle
			 (Some Tags.Proof.goal)));
      ignore(proof#scroll_to_mark ~use_align:true ~yalign:0.95 `INSERT)

let mode_cesar (proof:GText.view) = function
  | [] -> assert false
  | { Interface.goal_hyp = hyps; Interface.goal_ccl = cur_goal; } :: _ ->
      proof#buffer#insert "    *** Declarative Mode ***\n";
      List.iter
        (fun hyp -> proof#buffer#insert (hyp^"\n"))
        hyps;
      proof#buffer#insert "______________________________________\n";
      proof#buffer#insert ("thesis := \n "^cur_goal^"\n");
      ignore (proof#scroll_to_iter (proof#buffer#get_iter_at_mark `INSERT))

let display mode (view:GText.view) goals hints evars =
  let () = view#buffer#set_text "" in
  match goals with
  | None -> ()
    (* No proof in progress *)
  | Some { Interface.fg_goals = []; Interface.bg_goals = [] } ->
    (* A proof has been finished, but not concluded *)
    begin match evars with
    | Some evs when evs <> [] ->
      view#buffer#insert "No more subgoals but non-instantiated existential variables:\n\n";
      let iter evar =
        let msg = Printf.sprintf "%s\n" evar.Interface.evar_info in
        view#buffer#insert msg
      in
      List.iter iter evs
    | _ ->
      view#buffer#insert "Proof Completed."
    end
  | Some { Interface.fg_goals = []; Interface.bg_goals = bg } ->
    (* No foreground proofs, but still unfocused ones *)
    view#buffer#insert "This subproof is complete, but there are still unfocused goals:\n\n";
    let iter goal =
      let msg = Printf.sprintf "%s\n" goal.Interface.goal_ccl in
      view#buffer#insert msg
    in
    List.iter iter bg
  | Some { Interface.fg_goals = fg } ->
    mode view fg hints
