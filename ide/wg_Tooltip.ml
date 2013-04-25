(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This super inefficient thing should be an interval tree *)
module Table = struct
  type 'a t = ((int * int) * 'a) list ref

  let in_interval x (i1,i2) = i1 - x <= 0 && i2 - x > 0
  let overlap_interval (i1,i2 as x) (j1,j2 as y) =
    in_interval i1 y || in_interval i2 y || in_interval j1 x

  let create () = ref []
  let add l i c = l := (i,c) :: !l
  let remove_all l i =
    l := List.filter (fun (j,_) -> not (overlap_interval i j)) !l
  let find_all l x =
    let res =
      CList.map_filter
        (fun (i,c) -> if in_interval x i then Some c else None)
        !l
    in
    if res = [] then raise Not_found else res
end

let table : string lazy_t Table.t = Table.create ()

let tooltip_callback (view : GText.view) ~x ~y ~kbd tooltip =
  let x, y = view#window_to_buffer_coords `WIDGET x y in
  let iter = view#get_iter_at_location x y in
  if iter#has_tag Tags.Script.tooltip then begin
    try
      let ss = Table.find_all table iter#offset in
      view#misc#set_tooltip_text
        (String.concat "\n"
          (CList.uniquize (List.map Lazy.force ss)))
    with Not_found -> ()
  end else begin
    view#misc#set_tooltip_text ""; view#misc#set_has_tooltip true
  end;
  false

let remove_tag_callback tag ~start ~stop =
  if tag#get_oid = Tags.Script.tooltip#get_oid then
    Table.remove_all table (start#offset,stop#offset) 

let apply_tooltip_tag (buffer : GText.buffer) ~start ~stop ~markup =
  Table.add table (start#offset,stop#offset) markup;
  buffer#apply_tag Tags.Script.tooltip ~start ~stop

let set_tooltip_callback view =
  view#misc#set_has_tooltip true;
  ignore(view#misc#connect#query_tooltip ~callback:(tooltip_callback view));
  ignore(view#buffer#connect#remove_tag ~callback:remove_tag_callback)

