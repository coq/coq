(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project      *)
(*         *   University of Bologna                                   *)
(***********************************************************************)

(* Copyright (C) 2000-2004, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.unibo.it/.
 *)

exception CanNotUnshare;;

(* [unshare t] gives back a copy of t where all sharing has been removed   *)
(* Physical equality becomes meaningful on unshared terms. Hashtables that *)
(* use physical equality can now be used to associate information to evey  *)
(* node of the term.                                                       *)
let unshare ?(already_unshared = function _ -> false) t =
 let obj = Obj.repr t in
  let rec aux obj =
   if already_unshared (Obj.obj obj) then
    obj
   else
    (if Obj.is_int obj then
      obj
     else if Obj.is_block obj then
      begin
       let tag = Obj.tag obj in
        if tag < Obj.no_scan_tag then
         begin
          let size = Obj.size obj in
           let new_obj = Obj.new_block 0 size in
            Obj.set_tag new_obj tag ;
            for i = 0 to size - 1 do
             Obj.set_field new_obj i (aux (Obj.field obj i))
            done ;
            new_obj
         end
        else if tag = Obj.string_tag then
         obj
        else
         raise CanNotUnshare
      end
     else
      raise CanNotUnshare
    )
  in
   Obj.obj (aux obj)
;;
