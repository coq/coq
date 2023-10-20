(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Preferences
open Ideutils

type goals =
| NoGoals
| FocusGoals of { fg : DebuggerTypes.goal list; bg : DebuggerTypes.goal list }
| NoFocusGoals of {
  bg : DebuggerTypes.goal list;
  shelved : DebuggerTypes.goal list;
  given_up : DebuggerTypes.goal list;
}

class type proof_view =
  object
    inherit GObj.widget
    method source_buffer : GSourceView3.source_buffer
    method buffer : GText.buffer
    method refresh : force:bool -> unit
    method clear : unit -> unit
    method set_goals : goals -> unit
    method incr_sel_goal_num : int -> unit
    method select_first_goal : unit -> unit
  end

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

let sel_goal_num = ref 0

(* todo: hints are dead code? (None is passed to mode_tactics) *)
let mode_tactic sel_cb (proof : #GText.view_skel) goals ~unfoc_goals hints = match goals with
  | [] -> assert false
  | _ ->
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
      let fg_cnt = List.length goals in
      let goal_cnt = fg_cnt +
        (if Coq.PrintOpt.printing_unfocused () then List.length unfoc_goals else 0) in
      let head_str = Printf.sprintf
        "%d goal%s\n" fg_cnt (if 1 < fg_cnt then "s" else "")
      in
      let goal_str ?(shownum=false) index total name =
        let annot =
          match name with
          | Some id -> Printf.sprintf "(?%s)" id
          | None -> if shownum then Printf.sprintf "(%d/%d)" index total else "" in
        Printf.sprintf "______________________________________%s\n" annot
      in
      let width = Ideutils.textview_width proof in

      let insert_w_hyps ~shownum hyps cur_goal cur_name i =
        (* todo: print a space if i > 1? *)
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
            hook_tag_cb tag hint sel_cb on_hover;
            [tag], hints
          in
          insert_xml ~tags proof#buffer (Richpp.richpp_of_pp ~width hyp);
          proof#buffer#insert "\n";
          insert_hyp rem_hints hs
        in
        insert_hyp hyps_hints hyps;
        let _ = if goal_hints <> [] then
          let tag = proof#buffer#create_tag [] in
          let () = hook_tag_cb tag goal_hints sel_cb on_hover in
          [tag]
          else []
        in
        proof#buffer#insert (goal_str ~shownum i goal_cnt cur_name);
        insert_xml ~tags:[Tags.Proof.goal] proof#buffer (Richpp.richpp_of_pp ~width cur_goal);
        proof#buffer#insert "\n"
      in

      let insert_wo_hyps ~shownum i _ DebuggerTypes.{ goal_ccl = g; goal_name = name } =
        proof#buffer#insert (goal_str ~shownum i goal_cnt name);
        insert_xml proof#buffer (Richpp.richpp_of_pp ~width g);
        proof#buffer#insert "\n"
      in

      let print_goal ~shownum i g =
        if i = !sel_goal_num then
          let DebuggerTypes.{ goal_hyp = hyps; goal_ccl = cur_goal; goal_name = cur_name } = g in
          insert_w_hyps ~shownum hyps cur_goal cur_name (i+1);
        else
          insert_wo_hyps ~shownum (i+1) () g
      in

      proof#buffer#insert head_str;
      if !sel_goal_num >= goal_cnt then sel_goal_num := 0;
      List.iteri (print_goal ~shownum:true) goals;

      (* show unfocused goal if option set *)
      (* Insert remaining goals (no hypotheses) *)
      if Coq.PrintOpt.printing_unfocused () then begin
        ignore(proof#buffer#place_cursor ~where:(proof#buffer#end_iter)); (* why? *)
        if unfoc_goals <> [] then begin
          proof#buffer#insert "\nUnfocused Goals:\n";
          List.iteri (fun i g -> print_goal ~shownum:false (i+fg_cnt) g) unfoc_goals
        end
      end;
      ignore(proof#buffer#place_cursor
               ~where:(proof#buffer#end_iter#backward_to_tag_toggle
                         (Some Tags.Proof.goal)));
      ignore(proof#scroll_to_mark `INSERT)

let display mode (view : #GText.view_skel) goals hints =
  let () = view#buffer#set_text "" in
  let width = Ideutils.textview_width view in
  match goals with
  | NoGoals -> ()
    (* No proof in progress *)
  | FocusGoals { fg; bg } ->
    mode view fg ~unfoc_goals:bg hints
  | NoFocusGoals { bg; shelved; given_up } ->
    begin match (bg, shelved, given_up) with
    | [], [], [] ->
      view#buffer#insert "All goals completed."
    | [], [], _ ->
      (* The proof is finished, with the exception of given up goals. *)
      view#buffer#insert "All goals completed except some admitted goals:\n\n";
      let iter goal =
        insert_xml view#buffer (Richpp.richpp_of_pp ~width goal.DebuggerTypes.goal_ccl);
        view#buffer#insert "\n"
      in
      List.iter iter given_up;
      view#buffer#insert "\nYou need to go back and solve them."
    | [], _, _ ->
      (* All the goals have been resolved but those on the shelf. *)
      view#buffer#insert "All the remaining goals are on the shelf:\n\n";
      let iter goal =
        insert_xml view#buffer (Richpp.richpp_of_pp ~width goal.DebuggerTypes.goal_ccl);
        view#buffer#insert "\n"
      in
      List.iter iter shelved
    | _, _, _ ->
      (* No foreground proofs, but still unfocused ones *)
      let total = List.length bg in
      let goal_str index id =
        let annot =
          if Option.has_some (int_of_string_opt id) (* some uid *) then Printf.sprintf "(%d/%d)" index total
          else Printf.sprintf "(?%s)" id in
        Printf.sprintf
               "______________________________________%s\n" annot
      in
      view#buffer#insert "This subproof is complete, but there are some unfocused goals:\n\n";
      let iter i goal =
        let () = view#buffer#insert (goal_str (succ i) goal.DebuggerTypes.goal_id) in
        insert_xml view#buffer (Richpp.richpp_of_pp ~width goal.DebuggerTypes.goal_ccl);
        view#buffer#insert "\n"
      in
      List.iteri iter bg
    end


let proof_view () =
  let buffer = GSourceView3.source_buffer
    ~highlight_matching_brackets:true
    ~tag_table:Tags.Proof.table
    ?style_scheme:(style_manager#style_scheme source_style#get) ()
  in
  let text_buffer = new GText.buffer buffer#as_buffer in
  let view = GSourceView3.source_view
    ~source_buffer:buffer ~editable:false ~wrap_mode:`WORD ()
  in
  let () = Gtk_parsing.fix_double_click view in
  let default_clipboard = GData.clipboard Gdk.Atom.primary in
  let _ = buffer#add_selection_clipboard default_clipboard in
(* FIXME: handle this using CSS *)
(*   let cb clr = view#misc#modify_bg [`NORMAL, `NAME clr] in *)
(*   let _ = background_color#connect#changed ~callback:cb in *)
(*   let _ = view#misc#connect#realize ~callback:(fun () -> cb background_color#get) in *)
  let cb ft = view#misc#modify_font (GPango.font_description_from_string ft) in
  stick text_font view cb;

  let pf = object(self)
    inherit GObj.widget view#as_widget
    val mutable goals = NoGoals
    val mutable last_width = -1

    method source_buffer = buffer

    method buffer = text_buffer

    method clear () = buffer#set_text ""

    method set_goals gls = goals <- gls

    method incr_sel_goal_num incr =
      let fg, bg = match goals with
      | NoGoals -> [], []
      | FocusGoals { fg; bg } -> fg, bg
      | NoFocusGoals { bg; shelved; given_up } -> [], bg
      in
      let numgoals = List.length fg +
         (if Coq.PrintOpt.printing_unfocused () then List.length bg else 0) in
      let new_sel = !sel_goal_num + incr in
      sel_goal_num :=
        if new_sel < 0 then numgoals - 1
        else if new_sel >= numgoals then 0
        else new_sel;
      self#refresh ~force:true

    method select_first_goal () = sel_goal_num := 0

    method refresh ~force =
      (* We need to block updates here due to the following race:
         insertion of messages may create a vertical scrollbar, this
         will trigger a width change, calling refresh again and
         going into an infinite loop. *)
      let width = Ideutils.textview_width view  in
      (* Could still this method race if the scrollbar changes the
         textview_width ?? *)
      let needed = force || last_width <> width in
      if needed then begin
        last_width <- width;
        let dummy _ () = () in
        display (mode_tactic dummy) view goals None
      end
  end
  in
  (* Is there a better way to connect the signal ? *)
  (* Can this be done in the object constructor? *)
  let w_cb _ = pf#refresh ~force:false in
  ignore (view#misc#connect#size_allocate ~callback:w_cb);
  pf
