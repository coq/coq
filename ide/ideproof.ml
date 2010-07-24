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

let mode_tactic sel_cb (proof:GText.view) = function
  | [] -> assert false
  | (hyps,(cur_goal,cur_goal_menu))::rem_goals ->
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
      let head_str = Printf.sprintf "%d subgoal%s\n" goals_cnt (if 1 < goals_cnt then "" else "s") in
      let insert_hyp (h,menu) =
        let tag = proof#buffer#create_tag [] in
        hook_tag_cb tag menu sel_cb on_hover;
        proof#buffer#insert ~tags:[tag] (h^"\n")
      in
      let insert_goal g menu index total =
        let tags = if menu <> [] then
          let tag = proof#buffer#create_tag [] in
          hook_tag_cb tag menu sel_cb on_hover;
          [tag]
          else []
        in
        proof#buffer#insert (Printf.sprintf
                               "\n______________________________________(%d/%d)\n" index total);
        proof#buffer#insert ~tags (g^"\n")
      in
      proof#buffer#insert head_str;
      List.iter insert_hyp hyps;
      insert_goal cur_goal cur_goal_menu 1 goals_cnt;
      Util.list_fold_left_i (fun i _ (_,(g,_)) -> insert_goal g [] i goals_cnt) 2 () rem_goals;
      ignore(proof#buffer#place_cursor  
        ((proof#buffer#get_iter_at_mark `INSERT)#backward_lines (3*goals_cnt - 2)));
      ignore(proof#scroll_to_mark `INSERT)


let mode_cesar (proof:GText.view) = function
  | [] -> assert false
  | (hyps,(cur_goal,cur_goal_menu))::_ ->
      proof#buffer#insert "    *** Declarative Mode ***\n";
      List.iter
        (fun (hyp,_) -> proof#buffer#insert (hyp^"\n"))
        hyps;
      proof#buffer#insert "______________________________________\n";
      proof#buffer#insert ("thesis := \n "^cur_goal^"\n");
      ignore (proof#scroll_to_iter (proof#buffer#get_iter_at_mark `INSERT))

let display mode (view:GText.view) goals =
  view#buffer#set_text "";
  match goals with
    | Ide_blob.Message msg ->
        view#buffer#insert msg
    | Ide_blob.Goals g ->
        mode view g
