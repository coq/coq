(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class debugger name =
  (* todo: shouldn't be detachable *)
  let widget = Wg_Detachable.detachable ~title:"Debugger" () in

  object (self)
(*    inherit GPack.box*)

    method coerce = widget#coerce
    method hide () = widget#hide  (* todo: give up focus *)
    method show () = widget#show  (* todo: take focus? *)
    initializer
      let vb = GPack.vbox ~packing:(widget#pack ~expand:true (*~fill:true*)) () in
      let _ = GMisc.label ~text:"Call Stack" ~xalign:0.02 (* todo: use padding instead of xalign *)
        ~packing:(vb#pack ~expand:false ~fill:true ~padding:3) () in
(*        set not editable*)
(*      should be resizable*)
(*      does ~expand do anything?*)
      let stack_scroll = GBin.scrolled_window (*~height:125*)
        ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:(vb#pack ~expand:true) () in

      let stack = GText.view () in
      stack_scroll#add stack#coerce;

      (* todo: makes widget not resizable *)
      (* unit is 1/100 inch *)
(*
      widget#misc#set_size_request ~height:125 ();
      let _ = GMisc.label ~text:"Variables" ~xalign:1.0
        ~packing:(hb#pack ~expand:false ~fill:true ~padding:3) () in
*)
      ()
  end
