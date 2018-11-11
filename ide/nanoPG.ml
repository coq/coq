(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ideutils
open Session
open Preferences
open GdkKeysyms
open Printf

let eprintf x =
  if !Flags.debug then Printf.eprintf x else Printf.ifprintf stderr x

type gui = {
  notebook : session Wg_Notebook.typed_notebook;
  action_groups : GAction.action_group list;
}

let actiong gui name = List.find (fun ag -> ag#name = name) gui.action_groups
let ct gui = gui.notebook#current_term

let get_sel b = b#selection_bounds
let sel_nonempty b = let i, j = get_sel b in not (i#equal j)
let get_sel_txt b = let i, j = get_sel b in i#get_text ~stop:j

type status = { move : int option; kill : (string * bool) option; sel: bool }

let pr_status { move; kill; sel } =
  let move = Option.cata (fun i -> string_of_int i) "" move in
  let kill = Option.cata (fun (s,b) -> sprintf "kill(%b) %S" b s) "" kill in
  let sel = string_of_bool sel in
  Printf.sprintf "{ move: %s; kill: %s; sel: %s }" move kill sel
let pr_key t =
  let kv = GdkEvent.Key.keyval t in
  let str = GdkEvent.Key.string t in
  let str_of_mod = function
  | `SHIFT -> "SHIFT" | `LOCK -> "LOCK" | `CONTROL -> "CONTROL"
  | `MOD1 -> "MOD1" | `MOD2 -> "MOD2" | `MOD3 -> "MOD3" | `MOD4 -> "MOD4"
  | `MOD5 -> "MOD5" | `BUTTON1 -> "BUTTON1" | `BUTTON2 -> "BUTTON2"
  | `BUTTON3 -> "BUTTON3" | `BUTTON4 -> "BUTTON4" | `BUTTON5 -> "BUTTON5"
  | `SUPER -> "SUPER" | `HYPER -> "HYPER" | `META -> "META"
  | `RELEASE -> "RELEASE" in
  let mods = String.concat " " (List.map str_of_mod (GdkEvent.Key.state t)) in
  Printf.sprintf "'%s' (%d, %s)" str kv mods

type action =
  | Action of string * string
  | Callback of (gui -> unit)
  | Edit of (status -> GSourceView2.source_buffer -> GText.iter ->
              (string -> string -> unit) -> status)
  | Motion of (status -> GText.iter -> GText.iter * status)

type 'c entry = {
  mods : Gdk.Tags.modifier list;
  key : Gdk.keysym;
  keyname : string;
  doc : string;
  contents : 'c
}

let mC = [`CONTROL]
let mM = [`MOD1]

let mod_of t x = List.for_all (fun m -> List.mem m (GdkEvent.Key.state t)) x

let pr_keymod l =
  if l = mC then "C-"
  else if l = mM then "M-"
  else ""

let mkE ?(mods=mC) key keyname doc ?(alias=[]) contents =
  List.map (fun (mods, key, keyname) -> { mods; key; keyname; doc; contents })
    ((mods, key, keyname)::alias)

type keypaths = Step of action entry list * keypaths entry list

let print_keypaths kps =
  let rec aux prefix (Step (l, konts)) =
    String.concat "\n" (
       (List.map (fun x ->
         prefix ^ pr_keymod x.mods ^ x.keyname ^ "  " ^ x.doc ) l) @
       (List.map (fun x ->
         aux (prefix^pr_keymod x.mods^x.keyname^" ") x.contents) konts)) in
  aux "  " kps

let empty = Step([],[])

let frontier (Step(l1,l2)) =
  List.map (fun x -> pr_keymod x.mods ^ x.keyname) l1 @
  List.map (fun x -> pr_keymod x.mods ^ x.keyname) l2

let insert kps name enter_syms bindings =
  let rec aux kps enter_syms =
    match enter_syms, kps with
    | [], Step (el, konts) -> Step (List.flatten bindings @ el, konts)
    | (mods, key, keyname)::gs, Step (el, konts) ->
         if List.exists (fun { key = k; mods = m } -> key = k && mods = m) konts
         then
           let konts =
             List.map
               (fun ({ key = k; contents } as x) ->
                 if key <> k then x else { x with contents = aux contents gs })
             konts in
           Step(el,konts)
         else
           let kont =
             { mods; key; keyname; doc = name; contents = aux empty gs } in
           Step(el, kont::konts) in
  aux kps enter_syms

let run_action gui group name =
  ((actiong gui group)#get_action name)#activate ()

let run key gui action status =
  match action with
  | Callback f -> f gui; status
  | Action(group, name) -> run_action gui group name; status
  | Edit f ->
      let b = (ct gui).script#source_buffer in
      let i = b#get_iter_at_mark `INSERT in
      let status = f status b i (run_action gui) in
      if not status.sel then
        b#place_cursor ~where:(b#get_iter_at_mark `SEL_BOUND);
      status
  | Motion f ->
      let b, script = (ct gui).script#source_buffer, (ct gui).script in
      let sel_mode = status.sel || List.mem `SHIFT (GdkEvent.Key.state key) in
      let i =
        if sel_mode then b#get_iter_at_mark `SEL_BOUND
        else b#get_iter_at_mark `INSERT in
      let where, status = f status i in
      let sel_mode = status.sel || List.mem `SHIFT (GdkEvent.Key.state key) in
      if sel_mode then (b#move_mark `SEL_BOUND ~where; script#scroll_mark_onscreen `SEL_BOUND)
      else (b#place_cursor ~where; script#scroll_mark_onscreen `INSERT);
      status

let emacs = empty 

let emacs = insert emacs "Emacs" [] [
  (* motion *)
  mkE _e "e" "Move to end of line" (Motion(fun s i ->
    (if not i#ends_line then i#forward_to_line_end else i),
    { s with move = None }));
  mkE _a "a" "Move to beginning of line" (Motion(fun s i ->
    (i#set_line_offset 0), { s with move = None }));
  mkE ~mods:mM _e "e" "Move to end of sentence" (Motion(fun s i ->
    i#forward_sentence_end, { s with move = None }));
  mkE ~mods:mM _a "a" "Move to beginning of sentence" (Motion(fun s i ->
    i#backward_sentence_start, { s with move = None }));
  mkE _n "n" "Move to next line" (Motion(fun s i ->
    let orig_off = Option.default i#line_offset s.move in
    let i = i#forward_line in
    let new_off = min (i#chars_in_line - 1) orig_off in
    (if new_off > 0 then i#set_line_offset new_off else i),
    { s with move = Some orig_off }));
  mkE _p "p" "Move to previous line" (Motion(fun s i ->
    let orig_off = Option.default i#line_offset s.move in
    let i = i#backward_line in
    let new_off = min (i#chars_in_line - 1) orig_off in
    (if new_off > 0 then i#set_line_offset new_off else i),
    { s with move = Some orig_off }));
  mkE _f "f" "Forward char" ~alias:[[],_Right,"RIGHT"]
    (Motion(fun s i -> i#forward_char, { s with move = None }));
  mkE _b "b" "Backward char" ~alias:[[],_Left,"LEFT"]
    (Motion(fun s i -> i#backward_char, { s with move = None }));
  mkE ~mods:mM _f "f" "Forward word" ~alias:[mC,_Right,"RIGHT"]
    (Motion(fun s i -> i#forward_word_end, { s with move = None }));
  mkE ~mods:mM _b "b" "Backward word" ~alias:[mC,_Left,"LEFT"]
    (Motion(fun s i -> i#backward_word_start, { s with move = None }));
  mkE _space "SPC" "Set mark" ~alias:[mC,_at,"@"] (Motion(fun s i ->
    if s.sel = false then i, { s with sel = true }
    else i, { s with sel = false } ));
  (* edits *)
  mkE ~mods:mM _w "w" "Copy selected region" (Edit(fun s b i run ->
    if sel_nonempty b then
      let txt = get_sel_txt b in
      run "Edit" "Copy";
      { s with kill = Some(txt,false); sel = false }
    else s));
  mkE _w "w" "Kill selected region" (Edit(fun s b i run ->
    if sel_nonempty b then
      let txt = get_sel_txt b in
      run "Edit" "Cut";
      { s with kill = Some(txt,false); sel = false }
    else s));
  mkE _k "k" "Kill until the end of line" (Edit(fun s b i _ ->
    let already_killed = match s.kill with Some (k,true) -> k | _ -> "" in
    let k =
      if i#ends_line then begin
        b#delete ~start:i ~stop:i#forward_char; "\n"
      end else begin 
        let k = b#get_text ~start:i ~stop:i#forward_to_line_end () in
        b#delete ~start:i ~stop:i#forward_to_line_end; k
      end in
    { s with kill = Some (already_killed ^ k,true) }));
  mkE ~mods:mM _d "d" "Kill next word" (Edit(fun s b i _ ->
    let already_killed = match s.kill with Some (k,true) -> k | _ -> "" in
    let k =
      let k = b#get_text ~start:i ~stop:i#forward_word_end () in
      b#delete ~start:i ~stop:i#forward_word_end; k in
    { s with kill = Some (already_killed ^ k,true) }));
  mkE ~mods:mM _k "k" "Kill until sentence end" (Edit(fun s b i _ ->
    let already_killed = match s.kill with Some (k,true) -> k | _ -> "" in
    let k =
      let k = b#get_text ~start:i ~stop:i#forward_sentence_end () in
      b#delete ~start:i ~stop:i#forward_sentence_end; k in
    { s with kill = Some (already_killed ^ k,true) }));
  mkE ~mods:mM _BackSpace "DELBACK" "Kill word before cursor"
    (Edit(fun s b i _ ->
    let already_killed = match s.kill with Some (k,true) -> k | _ -> "" in
    let k =
      let k = b#get_text ~start:i ~stop:i#backward_word_start () in
      b#delete ~start:i ~stop:i#backward_word_start; k in
    { s with kill = Some (already_killed ^ k,true) }));
  mkE _d "d" "Delete next character" (Edit(fun s b i _ ->
    b#delete ~start:i ~stop:i#forward_char; s));
  mkE _y "y" "Yank killed text back " (Edit(fun s b i _ ->
    let k, s = match s.kill with
    | Some (k,_) -> k, { s with kill = Some (k,false) }
    | _ -> "", s in
    b#insert ~iter:i k;
    s));
  (* misc *)
  mkE _underscore "_" "Undo" (Action("Edit", "Undo"));
  mkE _g "g" "Esc" (Callback(fun gui -> (ct gui).finder#hide ()));
  mkE _s "s" "Search" (Callback(fun gui ->
    if (ct gui).finder#coerce#misc#visible
    then run_action gui "Edit" "Find Next"
    else run_action gui "Edit" "Find"));
  mkE _s "r" "Search backward" (Callback(fun gui ->
    if (ct gui).finder#coerce#misc#visible
    then run_action gui "Edit" "Find Previous"
    else run_action gui "Edit" "Find"));
  ]

let emacs = insert emacs "Emacs" [mC,_x,"x"] [
  mkE _s "s" "Save" (Action("File", "Save"));
  mkE _c "c" "Quit" (Action("File", "Quit"));
  mkE _f "f" "Open" (Action("File", "Open"));
  mkE ~mods:[] _u "u" "Undo" (Action("Edit", "Undo"));
  ]
  
let pg = insert emacs "Proof General" [mC,_c,"c"] [
  mkE _Return "RET" "Go to" (Action("Navigation", "Go to"));
  mkE _n "n" "Advance 1 sentence" (Action("Navigation", "Forward"));
  mkE _u "u" "Retract 1 sentence" (Action("Navigation", "Backward"));
  mkE _b "b" "Advance" (Action("Navigation", "End"));
  mkE _r "r" "Restart" (Action("Navigation", "Start"));
  mkE _c "c" "Stop"    (Action("Navigation", "Interrupt"));
  ]

let command gui c =
  let command = (ct gui).command in
  let script = (ct gui).script in
  let term =
    let i, j = script#source_buffer#selection_bounds in
    if i#equal j then None
    else Some (script#buffer#get_text ~start:i ~stop:j ()) in
  command#show;
  command#new_query ~command:c ?term ()

let pg = insert pg "Proof General" [mC,_c,"c"; mC,_a,"a"] [
  mkE _p "p" "Print" (Callback (fun gui -> command gui "Print"));
  mkE _c "c" "Check" (Callback (fun gui -> command gui "Check"));
  mkE _b "b" "About" (Callback (fun gui -> command gui "About"));
  mkE _a "a" "Search About" (Callback (fun gui -> command gui "SearchAbout"));
  mkE _o "o" "Search Pattern" (Callback (fun gui->command gui "SearchPattern"));
  mkE _l "l" "Locate" (Callback (fun gui -> command gui "Locate"));
  mkE _Return "RET" "match template" (Action("Templates","match"));
  ]

let empty = { sel = false; kill = None; move = None }

let find gui (Step(here,konts)) t =
  (* hack: ^c does copy in clipboard *)
  let sel_nonempty () = sel_nonempty (ct gui).script#source_buffer in
  let k = GdkEvent.Key.keyval t in
  if k = _x && mod_of t mC && sel_nonempty () then
    ignore(run t gui (Action("Edit","Cut")) empty)
  else
    if k = _c && mod_of t mC && sel_nonempty () then
      ignore(run t gui (Action("Edit","Copy")) empty);
    let cmp { key; mods } = key = k && mod_of t mods in
    try `Do (List.find cmp here) with Not_found ->
    try `Cont (List.find cmp konts).contents with Not_found -> `NotFound

let init w nb ags =
  let gui = { notebook = nb; action_groups = ags } in
  let cur = ref pg in
  let status = ref empty in
  let reset () = eprintf "reset\n%!"; cur := pg in
  ignore(w#event#connect#key_press ~callback:(fun t ->
    let on_current_term f =
      let term = try Some nb#current_term with Invalid_argument _ -> None in
      match term with None -> false | Some t -> f t
    in
    on_current_term (fun x ->
    if x.script#misc#get_property "has-focus" <> `BOOL true
    then false
    else begin
    eprintf "got key %s\n%!" (pr_key t);
    if nanoPG#get then begin
      match find gui !cur t with
      | `Do e ->
           eprintf "run (%s) %s on %s\n%!" e.keyname e.doc (pr_status !status);
           status := run t gui e.contents !status; reset (); true
      | `Cont c ->
           flash_info ("Waiting one of " ^ String.concat " " (frontier c));
           cur := c; true
      | `NotFound -> reset (); false
    end else false
  end)));
  ignore(w#event#connect#button_press ~callback:(fun t -> reset (); false))



let get_documentation () = print_keypaths pg
