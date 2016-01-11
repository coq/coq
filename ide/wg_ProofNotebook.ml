(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*let _ = proof#misc#set_can_focus true in
  let _ = GtkBase.Widget.add_events proof#as_widget
  [`ENTER_NOTIFY;`POINTER_MOTION] in*)

open Interface

type goal_tab = {
  interface_goal : goal;
  goal_view : Wg_GoalView.goal_view;
}

let rec flatten = function
| [] -> []
| (lg, rg) :: l ->
  let inner = flatten l in
  List.rev_append lg inner @ rg


class proof_notebook nb msg =
object(self)
  inherit GPack.notebook nb as super
  val mutable goals = None
  val mutable evars = None
  val mutable tabs = []

  method clear () =
    ()

  method set_goals g =
    goals <- g

  method set_evars (e: Interface.evar list option) =
    evars <- e

  method refresh () =
    match goals with
    | None -> (* no proof in progress, remove all tabs *)
      List.iter (fun t -> 
        let p = self#page_num t.goal_view#coerce in
        self#remove_page p
      ) tabs;
      tabs <- []
    | Some { fg_goals = fg; bg_goals = bg; shelved_goals; given_up_goals; } ->
      let evars = match evars with None -> [] | Some evs -> evs in
      if fg = [] then
      begin
        match (bg, shelved_goals, given_up_goals, evars) with
        | [], [], [], [] -> msg Pp.Info "No more subgoals."
        | [], [], [], _::_ -> msg Pp.Notice
            ("No more subgoals, but there are non-instantiated existential variables:\n\n" ^
            List.fold_left (fun acc e ->
              acc ^ e.Interface.evar_info ^ "\n"
            ) "" evars ^
            "\nYou can use Grab Existential Variables.")
        | [], [], _, _ -> msg Pp.Notice
            ("No more subgoals, but there are some goals you gave up:\n\n" ^
            List.fold_left (fun acc g ->
              acc ^ g.Interface.goal_ccl ^ "\n"
            ) "" given_up_goals ^
            "\nYou need to go back and solve them.")
        | [], _, _, _ ->  msg Pp.Notice
            ("All the remaining goals are on the shelf:\n\n" ^
            List.fold_left (fun acc g ->
              acc ^ g.Interface.goal_ccl ^ "\n"
            ) "" given_up_goals)
        | _, _, _, _ -> ()
      end;
        let new_tabs = ref [] in
        (* Remove all old tabs *)
        List.iter (fun t ->
          let p = self#page_num t.goal_view#coerce in
          self#remove_page p
        ) tabs;
        List.iter (fun g ->
          let lbl = GMisc.label
            ~markup:(Printf.sprintf "<b>%s</b>" g.goal_name) () in
          let proof = Wg_GoalView.goal_view () in
          new_tabs := { interface_goal = g; goal_view = proof }::!new_tabs;
          ignore (self#append_page ~tab_label:lbl#coerce proof#coerce);
          proof#refresh g
        ) fg;
        self#goto_page 0;
        List.iter (fun g ->
          let lbl = GMisc.label ~markup:(Printf.sprintf "%s" g.goal_name) () in
          let proof = Wg_GoalView.goal_view () in
          new_tabs := { interface_goal = g; goal_view = proof }::!new_tabs;
          ignore (self#append_page ~tab_label:lbl#coerce proof#coerce);
          proof#refresh g
        ) (flatten (List.rev bg));
        List.iter (fun g ->
          let lbl = GMisc.label ~markup:(Printf.sprintf "<i>%s</i>" g.goal_name) () in
          let proof = Wg_GoalView.goal_view () in
          new_tabs := { interface_goal = g; goal_view = proof }::!new_tabs;
          ignore (self#append_page ~tab_label:lbl#coerce proof#coerce);
          proof#refresh g
        ) shelved_goals;
        List.iter (fun g ->
          let lbl = GMisc.label ~markup:(Printf.sprintf "<s>%s</s>" g.goal_name) () in
          let proof = Wg_GoalView.goal_view () in
          new_tabs := { interface_goal = g; goal_view = proof }::!new_tabs;
          ignore (self#append_page ~tab_label:lbl#coerce proof#coerce);
          proof#refresh g
        ) given_up_goals;
        tabs <- List.rev !new_tabs
end

let create msg =
  GtkPack.Notebook.make_params []
    ~cont:(GContainer.pack_container
      ~create:(fun pl ->
        let nb = GtkPack.Notebook.create pl in
          new proof_notebook nb msg))
