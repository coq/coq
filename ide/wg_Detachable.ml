(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class type detachable_signals =
  object
    inherit GContainer.container_signals
    method attached : callback:(GObj.widget -> unit) -> unit
    method detached : callback:(GObj.widget -> unit) -> unit
  end

class detachable (obj : ([> Gtk.box] as 'a) Gobject.obj) =

  object(self)
    inherit GPack.box_skel (obj :> Gtk.box Gobject.obj) as super

    val but = GButton.button ()
    val win = GWindow.window ~type_hint:`DIALOG ()
    val frame = GBin.frame ~shadow_type:`NONE ()
    val mutable detached = false
    val mutable detached_cb = (fun _ -> ())
    val mutable attached_cb = (fun _ -> ())

    method child = frame#child
    method! add = frame#add
    method! pack ?from ?expand ?fill ?padding w =
      if frame#all_children = [] then self#add w
      else raise (Invalid_argument "detachable#pack")

    method title = win#title
    method set_title = win#set_title

    method connect : detachable_signals = object
      inherit GContainer.container_signals_impl obj
      method attached ~callback = attached_cb <- callback
      method detached ~callback = detached_cb <- callback
    end

    method show =
      if detached then win#present ()
      else self#misc#show ();

    method hide =
      if detached then win#misc#hide ()
      else self#misc#hide ()

    method visible = win#misc#visible || self#misc#visible

    method frame = frame

    method button = but

    method attach () =
      win#misc#hide ();
      frame#misc#reparent self#coerce;
      detached <- false;
      attached_cb self#child

    method detach () =
      frame#misc#reparent win#coerce;
      self#misc#hide ();
      win#present ();
      detached <- true;
      detached_cb self#child

    initializer
      self#set_homogeneous false;
      super#pack ~expand:false but#coerce;
      super#pack ~expand:true ~fill:true frame#coerce;
      win#misc#hide ();
      but#add (GMisc.label
        ~markup:"<span size='x-small'>D\nE\nT\nA\nC\nH</span>" ())#coerce;
      ignore(win#event#connect#delete ~callback:(fun _ -> self#attach (); true));
      ignore(but#connect#clicked ~callback:(fun _ -> self#detach ()))

  end

let detachable ?title =
  GtkPack.Box.make_params [] ~cont:(
    GContainer.pack_container
      ~create:(fun p ->
         let d = new detachable (GtkPack.Box.create `HORIZONTAL p) in
         Option.iter d#set_title title;
         d))

