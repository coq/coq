(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ideutils

let reload_timer = mktimer ()
let autosave_timer = mktimer ()

class type ops =
object
  method filename : string option
  method update_stats : unit
  method changed_on_disk : bool
  method reload : ?parent:GWindow.window -> unit -> unit
  method auto_save : unit
  method save : string -> bool
  method saveas : ?parent:GWindow.window -> string -> bool
end

class fileops (buffer:GText.buffer) _fn (reset_handler:unit->unit) =
object(self)

  val mutable filename = _fn
  val mutable last_stats = NoSuchFile
  val mutable last_modification_time = 0.
  val mutable last_auto_save_time = 0.

  method filename = filename

  method update_stats = match filename with
    |Some f -> last_stats <- Ideutils.stat f
    |_ -> ()

  method changed_on_disk = match filename with
    |None -> false
    |Some f -> match Ideutils.stat f, last_stats with
        |MTime cur_mt, MTime last_mt -> cur_mt > last_mt
        |MTime _, (NoSuchFile|OtherError) -> true
        |NoSuchFile, MTime _ ->
          flash_info ("Warning, file not on disk anymore : "^f);
          false
        |_ -> false

  method reload ?parent () =
    let do_reload f =
      push_info "Reloading buffer";
      try
        reset_handler ();
        let b = Buffer.create 1024 in
        Ideutils.read_file f b;
        let s = try_convert (Buffer.contents b) in
        buffer#set_text s;
        self#update_stats;
        buffer#place_cursor ~where:buffer#start_iter;
        buffer#set_modified false;
        pop_info ();
        flash_info "Buffer reloaded";
        Sentence.tag_all buffer;
      with _  ->
        pop_info ();
        flash_info "Warning: could not reload buffer";
    in
    match filename with
      | None -> ()
      | Some f ->
        if not buffer#modified then do_reload f
        else
          let answ = Ui_dialogs.question_box
            ~title:"Modified buffer changed on disk"
            ~buttons:[ButtonWithLabel "Reload from file";
                      ButtonWithLabel "Overwrite file";
                      ButtonWithLabel "Disable Auto Reload"]
            ~default:0
            ~icon:(stock_to_widget `DIALOG_WARNING)
            ?parent
            "Some unsaved buffers changed on disk"
          in
          match answ with
            | 1 -> do_reload f
            | 2 -> if self#save f then flash_info "Overwritten" else
                flash_info "Could not overwrite file"
            | _ ->
              Minilib.log "Auto reload set to false";
              Preferences.global_auto_reload#set false;
              reload_timer.kill ()

  method save f =
    if try_export f (buffer#get_text ()) then begin
      filename <- Some f;
      self#update_stats;
      buffer#set_modified false;
      (match self#auto_save_name with
        | None -> ()
        | Some fn -> try Sys.remove fn with _ -> ());
      true
    end
    else false

  method saveas ?parent f =
  if not (Sys.file_exists f) then self#save f
  else
    (* The dialog's content may be determined by GTK, but we have to provide placeholders
       or the dialog may not appear at all *)
    let answ = Ui_dialogs.question_box ~title:"File exists on disk"
      ~buttons:[ButtonWithLabel "Overwrite"; ButtonWithStock `CANCEL]
      ~default:1
      ~icon:(warn_image ())#coerce
      ?parent
      ("File "^f^" already exists")
    in
    match answ with
      | 1 -> self#save f
      | _ -> false

  method private auto_save_name =
    match filename with
      | None -> None
      | Some f ->
        let dir = Filename.dirname f in
        let base = (fst Preferences.auto_save_name#get) ^
          (Filename.basename f) ^
          (snd Preferences.auto_save_name#get)
        in Some (Filename.concat dir base)

  method private need_auto_save =
    buffer#modified &&
      last_modification_time > last_auto_save_time

  method auto_save =
    if self#need_auto_save then begin
      match self#auto_save_name with
        | None -> ()
        | Some fn ->
          try
            last_auto_save_time <- Unix.time();
            Minilib.log ("Autosave time: "^(string_of_float (Unix.time())));
            if try_export fn (buffer#get_text ()) then begin
              flash_info ~delay:1000 "Autosaved"
            end
            else warning
              ("Autosave failed (check if " ^ fn ^ " is writable)")
          with _ ->
            warning ("Autosave: unexpected error while writing "^fn)
    end

  initializer
  let _ = buffer#connect#end_user_action
    ~callback:(fun () -> last_modification_time <- Unix.time ())
  in ()

end
