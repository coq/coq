(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ideutils
open Session
open Preferences

type gui = {
  notebook : session Wg_Notebook.typed_notebook;
  action_groups : GAction.action_group list;
}

let actiong gui name = List.find (fun ag -> ag#name = name) gui.action_groups

let make_emacs_mode gui name enter_sym bindings =
  let notebook = gui.notebook in
  let bound k = List.mem_assoc k bindings in
  let is_set, set, unset, mask = match enter_sym with
    | None -> (fun () -> true), (fun _ -> false), (fun () -> ()), bound
    | Some (k,_) -> let status = ref false in
        let is_set () = !status in
        let set ~dry_run k' =
          if not (is_set ()) && k = k' then begin
            if dry_run then true else begin
             flash_info ("Waiting " ^name^" command: " ^
               String.concat " " (List.map (fun (_,(d,_,_)) ->"^"^d) bindings));
             status := true; true
            end
          end else false in
        let unset () = status := false in
        let mask k' = set ~dry_run:true k' || (is_set () && bound k') in
        is_set, set ~dry_run:false, unset, mask in
  let doc =
    let prefix =
      match enter_sym with
      | None -> "  "
      | Some (_,k) -> "  ^"^k in 
    name ^":\n"^
    String.concat "\n"
      (List.map (fun (_,(k,doc,_)) -> prefix^"^"^k^" "^doc) bindings) in
  let run k = if not (is_set ()) then false else try 
     let action = match Util.pi3 (List.assoc k bindings) with
      | `Callback f -> f
      | `Edit f -> (fun () ->
          let b = notebook#current_term.script#source_buffer in
          let i = b#get_iter_at_mark `INSERT in
          f b i)
      | `Motion f -> (fun () ->
          let b = notebook#current_term.script#source_buffer in
          let i = b#get_iter_at_mark `INSERT in
          b#place_cursor ~where:(f i))
      | `Action(group,name) -> ((actiong gui group)#get_action name)#activate in
      action ();
      unset ();
      true
    with Not_found -> false in
  run, set, unset, mask, doc

let compile_emacs_modes gui l =
  List.fold_left (fun (r,s,u,m,d) mode ->
    let run, set, unset, mask,doc = mode gui in
    (fun k -> r k || run k), (fun k -> s k or set k),
    (fun () -> u (); unset ()), (fun k -> m k || mask k), d^"\n"^doc)
  ((fun _ -> false),(fun _ -> false),(fun () -> ()),(fun _ -> false),"") l

let pg_mode gui = make_emacs_mode gui "Proof General" (Some(GdkKeysyms._c,"c"))[
  GdkKeysyms._Return, ("RET", "Go to",      `Action("Navigation", "Go to"));
  GdkKeysyms._n, ("n", "Advance 1 sentence",`Action("Navigation", "Forward"));
  GdkKeysyms._u, ("u", "Retract 1 sentence",`Action("Navigation", "Backward"));
  GdkKeysyms._b, ("b", "Advance",           `Action("Navigation", "End"));
  GdkKeysyms._r, ("r", "Restart",           `Action("Navigation", "Start"));
  GdkKeysyms._c, ("c", "Stop",              `Action("Navigation", "Interrupt"));
  ]

let std_mode gui = make_emacs_mode gui "Emacs" None [
  GdkKeysyms._underscore, ("_", "Undo", `Action("Edit", "Undo"));
  GdkKeysyms._g, ("g", "Esc", `Callback(fun () ->
    gui.notebook#current_term.finder#hide ()));
  GdkKeysyms._s, ("s", "Search", `Callback(fun () ->
    if gui.notebook#current_term.finder#coerce#misc#visible then
      ((actiong gui "Edit")#get_action "Find Next")#activate ()
    else ((actiong gui "Edit")#get_action "Find")#activate ()));
  GdkKeysyms._e, ("e", "Move to end of line", `Motion(fun i ->
    i#forward_to_line_end));
  GdkKeysyms._a, ("a", "More to beginning of line", `Motion(fun i ->
    i#backward_sentence_start));
  GdkKeysyms._n, ("n", "Move to next line", `Motion(fun i ->
    i#forward_line#set_line_offset i#line_offset));
  GdkKeysyms._p, ("p", "Move to previous line", `Motion(fun i ->
    i#backward_line#set_line_offset i#line_offset));
  GdkKeysyms._k, ("k", "Kill untill the end of line", `Edit(fun b i ->
    b#delete ~start:i ~stop:i#forward_to_line_end));
  ]

let std_xmode gui = make_emacs_mode gui "Emacs" (Some (GdkKeysyms._x,"x")) [
  GdkKeysyms._s, ("s", "Save", `Action("File", "Save"));
  GdkKeysyms._c, ("c", "Quit", `Action("File", "Quit"));
  ]
  
let is_ctrl t = List.mem `CONTROL (GdkEvent.Key.state t)

let documentation = ref ""

let init w nb ags =
  let gui = { notebook = nb; action_groups = ags } in
  let emacs_run, emacs_set, emacs_unset, emacs_mask, doc =
    compile_emacs_modes gui [std_xmode; pg_mode; std_mode] in
  ignore(w#event#connect#key_release ~callback:(fun t ->
    current.nanoPG && is_ctrl t &&
    emacs_mask (GdkEvent.Key.keyval t)
  ));
  ignore(w#event#connect#key_press ~callback:(fun t ->
    if current.nanoPG && is_ctrl t then
      let keyval = GdkEvent.Key.keyval t in
      if emacs_run keyval then (emacs_unset (); true)
      else emacs_set keyval
    else false
  ));
  documentation := doc

let get_documentation () = !documentation
