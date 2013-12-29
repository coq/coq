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
open GdkKeysyms

let eprintf x =
  if !Flags.debug then Printf.eprintf x else Printf.ifprintf stderr x

type gui = {
  notebook : session Wg_Notebook.typed_notebook;
  action_groups : GAction.action_group list;
}

let actiong gui name = List.find (fun ag -> ag#name = name) gui.action_groups
let ct gui = gui.notebook#current_term

type status = [ `Empty | `CnCu of int | `Kill of string * bool ]

let pr_status = function
  | `Empty -> "empty"
  | `CnCu n -> Printf.sprintf "^n^u %d" n
  | `Kill (s,b) -> Printf.sprintf "kill(%b) %S" b s

type action =
  | Action of string * string
  | Callback of (gui -> unit)
  | Edit of (status -> GSourceView2.source_buffer -> GText.iter -> status)
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

let mkE ?(mods=mC) key keyname doc contents =
  { mods; key; keyname; doc; contents }

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
    | [], Step (el, konts) -> Step (bindings @ el, konts)
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

let run gui action status =
  match action with
  | Callback f -> f gui; status
  | Action(group, name) ->
      ((actiong gui group)#get_action name)#activate (); status
  | Edit f ->
      let b = (ct gui).script#source_buffer in
      let i = b#get_iter_at_mark `INSERT in
      f status b i
  | Motion f ->
      let b = (ct gui).script#source_buffer in
      let i = b#get_iter_at_mark `INSERT in
      let where, status = f status i in
      b#place_cursor ~where;
      status

let emacs = empty 

let emacs = insert emacs "Emacs" [] [
  mkE _underscore "_" "Undo" (Action("Edit", "Undo"));
  mkE _g "g" "Esc" (Callback(fun gui -> (ct gui).finder#hide ()));
  mkE _s "s" "Search" (Callback(fun gui ->
    if (ct gui).finder#coerce#misc#visible then
      ((actiong gui "Edit")#get_action "Find Next")#activate ()
    else ((actiong gui "Edit")#get_action "Find")#activate ()));
  mkE _s "r" "Search backward" (Callback(fun gui ->
    if (ct gui).finder#coerce#misc#visible then
      ((actiong gui "Edit")#get_action "Find Previous")#activate ()
    else ((actiong gui "Edit")#get_action "Find")#activate ()));
  mkE _e "e" "Move to end of line" (Motion(fun s i ->
    (if not i#ends_line then i#forward_to_line_end else i), s));
  mkE _a "a" "Move to beginning of line" (Motion(fun s i ->
    (i#set_line_offset 0), s));
  mkE ~mods:mM _e "e" "Move to end of sentence" (Motion(fun s i ->
    i#forward_sentence_end, s));
  mkE ~mods:mM _a "a" "Move to beginning of sentence" (Motion(fun s i ->
    i#backward_sentence_start, s));
  mkE _n "n" "Move to next line" (Motion(fun s i ->
    let orig_off = match s with `CnCu n -> n | _ -> i#line_offset in
    let i = i#forward_line in
    let new_off = min (i#chars_in_line - 1) orig_off in
    (if new_off > 0 then i#set_line_offset new_off else i), `CnCu orig_off));
  mkE _p "p" "Move to previous line" (Motion(fun s i ->
    let orig_off = match s with `CnCu n -> n | _ -> i#line_offset in
    let i = i#backward_line in
    let new_off = min (i#chars_in_line - 1) orig_off in
    (if new_off > 0 then i#set_line_offset new_off else i), `CnCu orig_off));
  mkE _f "f" "Forward char" (Motion(fun s i -> i#forward_char, s));
  mkE _b "b" "Backward char" (Motion(fun s i -> i#backward_char, s));
  mkE ~mods:mM _f "f" "Forward word" (Motion(fun s i -> i#forward_word_end, s));
  mkE ~mods:mM _b "b" "Backward word" (Motion(fun s i ->
    i#backward_word_start, s));
  mkE _k "k" "Kill untill the end of line" (Edit(fun s b i ->
    let already_killed = match s with `Kill (k,true) -> k | _ -> "" in
    let k =
      if i#ends_line then begin
        b#delete ~start:i ~stop:i#forward_char; "\n"
      end else begin 
        let k = b#get_text ~start:i ~stop:i#forward_to_line_end () in
        b#delete ~start:i ~stop:i#forward_to_line_end; k
      end in
    `Kill (already_killed ^ k,true)));
  mkE ~mods:mM _d "d" "Kill next word" (Edit(fun s b i ->
    let already_killed = match s with `Kill (k,true) -> k | _ -> "" in
    let k =
      let k = b#get_text ~start:i ~stop:i#forward_word_end () in
      b#delete ~start:i ~stop:i#forward_word_end; k in
    `Kill (already_killed ^ k,true)));
  mkE ~mods:mM _k "k" "Kill until sentence end" (Edit(fun s b i ->
    let already_killed = match s with `Kill (k,true) -> k | _ -> "" in
    let k =
      let k = b#get_text ~start:i ~stop:i#forward_sentence_end () in
      b#delete ~start:i ~stop:i#forward_sentence_end; k in
    `Kill (already_killed ^ k,true)));
  mkE ~mods:mM _BackSpace "DELBACK" "Kill word before cursor" (Edit(fun s b i ->
    let already_killed = match s with `Kill (k,true) -> k | _ -> "" in
    let k =
      let k = b#get_text ~start:i ~stop:i#backward_word_start () in
      b#delete ~start:i ~stop:i#backward_word_start; k in
    `Kill (already_killed ^ k,true)));
  mkE _d "d" "Delete next character" (Edit(fun s b i ->
    b#delete ~start:i ~stop:i#forward_char; s));
  mkE _y "y" "Yank killed text back " (Edit(fun s b i ->
    let k, s = match s with `Kill (k,_) -> k, `Kill(k,false) | _ -> "", s in
    b#insert ~iter:i k;
    s));
  ]

let emacs = insert emacs "Emacs" [mC,_x,"x"] [
  mkE _s "s" "Save" (Action("File", "Save"));
  mkE _c "c" "Quit" (Action("File", "Quit"));
  mkE _f "f" "Open" (Action("File", "Open"));
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

let find gui (Step(here,konts)) t =
  (* hack: ^c does copy in clipboard *)
  let sel_nonempty () =
    let i, j = (ct gui).script#source_buffer#selection_bounds in
    not (i#equal j) in
  let k = GdkEvent.Key.keyval t in
  if k = _c && mod_of t mC && sel_nonempty () then
    ignore(run gui (Action("Edit","Copy")) `Empty);
  let cmp { key; mods } = key = k && mod_of t mods in
  try `Do (List.find cmp here) with Not_found ->
  try `Cont (List.find cmp konts).contents with Not_found -> `NotFound

let init w nb ags =
  let gui = { notebook = nb; action_groups = ags } in
  let cur = ref pg in
  let status = ref `Empty in
  let reset () = cur := pg in
  ignore(w#event#connect#key_press ~callback:(fun t ->
    if current.nanoPG then begin
      match find gui !cur t with
      | `Do e ->
           eprintf "run (%s) %s on %s\n%!" e.keyname e.doc (pr_status !status);
           status := run gui e.contents !status; reset (); true
      | `Cont c ->
           flash_info ("Waiting one of " ^ String.concat " " (frontier c));
           cur := c; true
      | `NotFound -> reset (); false
    end else false
  ));
  ignore(w#event#connect#button_press ~callback:(fun t -> reset (); false))



let get_documentation () = print_keypaths pg
