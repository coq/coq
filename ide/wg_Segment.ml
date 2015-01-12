(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util

type color = GDraw.color

module Segment :
sig
  type +'a t
  val length : 'a t -> int
  val resize : 'a t -> int -> 'a t
  val empty : 'a t
  val add : int -> 'a -> 'a t -> 'a t
  val remove : int -> 'a t -> 'a t
  val fold : ('a -> 'a -> bool) -> (int -> int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
end =
struct
  type 'a t = {
    length : int;
    content : 'a Int.Map.t;
  }

  let empty = { length = 0; content = Int.Map.empty }

  let length s = s.length

  let resize s len =
    if s.length <= len then { s with length = len }
    else
      let filter i v = i < len in
      { length = len; content = Int.Map.filter filter s.content }

  let add i v s =
    if i < s.length then
      { s with content = Int.Map.add i v s.content }
    else s

  let remove i s = { s with content = Int.Map.remove i s.content }

  let fold eq f s accu =
    let make k v (cur, accu) = match cur with
    | None -> Some (k, k, v), accu
    | Some (i, j, w) ->
      if k = j + 1 && eq v w then Some (i, k, w), accu
      else Some (k, k, v), (i, j, w) :: accu
    in
    let p, segments = Int.Map.fold make s.content (None, []) in
    let segments = match p with
    | None -> segments
    | Some p -> p :: segments
    in
    List.fold_left (fun accu (i, j, v) -> f i j v accu) accu segments

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

class segment () =
let box = GBin.frame () in
let draw = GMisc.image ~packing:box#add () in
object (self)

  inherit GObj.widget box#as_widget

  val mutable width = 1
  val mutable height = 20
  val mutable data = Segment.empty
  val mutable default : color = `WHITE
  val mutable pixmap : GDraw.pixmap = GDraw.pixmap ~width:1 ~height:1 ()

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
    let _ = box#misc#connect#size_allocate cb in
    (** Initial pixmap *)
    draw#set_pixmap pixmap

  method length = Segment.length data

  method set_length len =
    data <- Segment.resize data len;
    if self#misc#visible then self#refresh ()

  method private fill_range color i j =
    let i = i2f i in
    let j = i2f j in
    let width = i2f width in
    let len = i2f (Segment.length data) in
    let x = f2i ((i *. width) /. len) in
    let x' = f2i ((j *. width) /. len) in
    let w = x' - x in
    pixmap#set_foreground color;
    pixmap#rectangle ~x ~y:0 ~width:w ~height ~filled:true ();
    draw#set_mask None;

  method add i color =
    data <- Segment.add i color data;
    if self#misc#visible then self#fill_range color i (i + 1)

  method remove i =
    data <- Segment.remove i data;
    if self#misc#visible then self#fill_range default i (i + 1)

  method set_default_color color = default <- color
  method default_color = default

  method private redraw () =
    pixmap <- GDraw.pixmap ~width ~height ();
    draw#set_pixmap pixmap;
    self#refresh ();

  method private refresh () =
    pixmap#set_foreground default;
    pixmap#rectangle ~x:0 ~y:0 ~width ~height ~filled:true ();
    let fold i j v () = self#fill_range v i (j + 1) in
    Segment.fold color_eq fold data ();
    draw#set_mask None;

end
