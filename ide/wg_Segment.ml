(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Preferences

type color = GDraw.color

type model_event = [ `INSERT | `REMOVE | `SET of int * color ]

class type model =
object
  method changed : callback:(model_event -> unit) -> unit
  method length : int
  method fold : 'a. ('a -> color -> 'a) -> 'a -> 'a
end

let i2f = float_of_int
let f2i = int_of_float

let color_eq (c1 : GDraw.color) (c2 : GDraw.color) = match c1, c2 with
| `BLACK, `BLACK -> true
| `COLOR c1, `COLOR c2 -> c1 == c2
| `NAME s1, `NAME s2 -> String.equal s1 s2
| `RGB (r1, g1, b1), `RGB (r2, g2, b2) -> r1 = r2 && g1 = g2 && b1 = b2
| `WHITE, `WHITE -> true
| _ -> false

class type segment_signals =
object
  inherit GObj.misc_signals
  inherit GUtil.add_ml_signals
  method clicked : callback:(int -> unit) -> GtkSignal.id
end

class segment_signals_impl obj (clicked : 'a GUtil.signal) : segment_signals =
object
  val after = false
  inherit GObj.misc_signals obj
  inherit GUtil.add_ml_signals obj [clicked#disconnect]
  method clicked = clicked#connect ~after
end

class segment () =
let box = GBin.frame () in
let eventbox = GBin.event_box ~packing:box#add () in
let draw = GMisc.image ~packing:eventbox#add () in
object (self)

  inherit GObj.widget box#as_widget

  val mutable width = 1
  val mutable height = 20
  val mutable model : model option = None
  val mutable default : color = `WHITE
  val mutable pixmap : GDraw.pixmap = GDraw.pixmap ~width:1 ~height:1 ()
  val clicked = new GUtil.signal ()
  val mutable need_refresh = false
  val refresh_timer = Ideutils.mktimer ()

  initializer
    box#misc#set_size_request ~height ();
    let cb rect =
      let w = rect.Gtk.width in
      let h = rect.Gtk.height in
      (** Only refresh when size actually changed, otherwise loops *)
      if self#misc#visible && (width <> w || height <> h) then begin
        width <- w;
        height <- h;
        self#redraw ();
      end
    in
    let _ = box#misc#connect#size_allocate ~callback:cb in
    let clicked_cb ev = match model with
    | None -> true
    | Some md ->
      let x = GdkEvent.Button.x ev in
      let (width, _) = pixmap#size in
      let len = md#length in
      let idx = f2i ((x *. i2f len) /. i2f width) in
      let () = clicked#call idx in
      true
    in
    let _ = eventbox#event#connect#button_press ~callback:clicked_cb in
    let cb show = if show then self#misc#show () else self#misc#hide () in
    stick show_progress_bar self cb;
    (** Initial pixmap *)
    draw#set_pixmap pixmap;
    refresh_timer.Ideutils.run ~ms:300
      ~callback:(fun () -> if need_refresh then self#refresh (); true)

  method set_model md =
    model <- Some md;
    let changed_cb = function
    | `INSERT | `REMOVE ->
      if self#misc#visible then need_refresh <- true
    | `SET (i, color) ->
      if self#misc#visible then self#fill_range color i (i + 1)
    in
    md#changed ~callback:changed_cb

  method private fill_range color i j = match model with
  | None -> ()
  | Some md ->
    let i = i2f i in
    let j = i2f j in
    let width = i2f width in
    let len = i2f md#length in
    let x = f2i ((i *. width) /. len) in
    let x' = f2i ((j *. width) /. len) in
    let w = x' - x in
    pixmap#set_foreground color;
    pixmap#rectangle ~x ~y:0 ~width:w ~height ~filled:true ();
    draw#set_mask None;

  method set_default_color color = default <- color
  method default_color = default

  method private redraw () =
    pixmap <- GDraw.pixmap ~width ~height ();
    draw#set_pixmap pixmap;
    self#refresh ();

  method private refresh () = match model with
  | None -> ()
  | Some md ->
    need_refresh <- false;
    pixmap#set_foreground default;
    pixmap#rectangle ~x:0 ~y:0 ~width ~height ~filled:true ();
    let make (k, cur, accu) v = match cur with
    | None -> pred k, Some (k, k, v), accu
    | Some (i, j, w) ->
      if k = j - 1 && color_eq v w then pred k, Some (k, i, w), accu
      else pred k, Some (k, k, v), (i, j, w) :: accu
    in
    let _, p, segments = md#fold make (md#length - 1, None, []) in
    let segments = match p with
    | None -> segments
    | Some p -> p :: segments
    in
    List.iter (fun (i, j, v) -> self#fill_range v i (j + 1)) segments;
    draw#set_mask None;

  method connect =
    new segment_signals_impl box#as_widget clicked

end
