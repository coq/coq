(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

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
