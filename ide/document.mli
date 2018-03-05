(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* An 'a document is a structure to hold and manipulate list of sentences.
   Sentences are equipped with an id = Stateid.t and can carry arbitrary
   data ('a).
   
   When added (push) to the document, a sentence has no id, it has
   be manually assigned just afterward or the sentence has to be removed
   (pop) before any other sentence can be pushed.
   This exception is useful since the process of assigning an id to
   a sentence may fail (parse error) and an error handler may want to annotate
   a script buffer with the error message.  This handler needs to find the
   sentence in question, and it is simpler if the sentence is in the document.
   Only the functions pop, find, fold_all and find_map can be called on a
   document with a tip that has no id (and assign_tip_id of course).
   
   The document can be focused (non recursively) to a zone.  After that
   some functions operate on the focused zone only.  When unfocused the
   context (the part of the document out of focus) is restored.
*)

exception Empty

type 'a document
type id = Stateid.t

val create : unit -> 'a document

(* Functions that work on the focused part of the document ******************* *)

(** The last sentence.  @raise Invalid_argument if tip has no id.  @raise Empty *)
val tip       : 'a document -> id

(** The last sentence.  @raise Empty *)
val tip_data  : 'a document -> 'a

(** Add a sentence on the top (with no state_id) *)
val push : 'a document -> 'a -> unit

(** Remove the tip setence.  @raise Empty *)
val pop : 'a document -> 'a

(** Assign the state_id of the tip.  @raise Empty *)
val assign_tip_id : 'a document -> id -> unit

(** [cut_at d id] cuts the document at [id] that is the new tip.
    Returns the list of sentences that were cut.
    @raise Not_found *)
val cut_at : 'a document -> id -> 'a list

(* Functions that work on the whole document ********************************* *)

(** returns the id of the topmost sentence validating the predicate and
    a boolean that is true if one needs to unfocus the document to access
    such sentence.  @raise Not_found *)
val find_id : 'a document -> (id -> 'a -> bool) -> id * bool

(** look for a sentence validating the predicate.  The boolean is true
    if the sentence is in the zone currently focused.  @raise Not_found *)
val find : 'a document -> (bool -> id option -> 'a -> bool) -> 'a
val find_map : 'a document -> (bool -> id option -> 'a -> 'b option) -> 'b

(** After [focus s c1 c2] the top of [s] is the topmost element [x] such that
    [c1 x] is [true] and the bottom is the first element [y] following [x]
    such that [c2 y] is [true].
    @raise Invalid_argument if there is no such [x] and [y] or already focused *)
val focus :
  'a document ->
    cond_top:(id -> 'a -> bool) -> cond_bot:(id -> 'a -> bool) -> unit

(** Undoes a [focus].
    @raise Invalid_argument "CStack.unfocus" if the stack is not focused *)
val unfocus : 'a document -> unit

(** Is the document focused *)
val focused : 'a document -> bool

(** No sentences at all *)
val is_empty : 'a document -> bool

(** returns the 1 to-last sentence, and true if we need to unfocus to reach it.
    @raise Not_found *)
val before_tip : 'a document -> id * bool

(** Is the id in the focused zone? *)
val is_in_focus : 'a document -> id -> bool

(** Folds over the whole document starting from the topmost (maybe unfocused)
    sentence. *)
val fold_all :
  'a document -> 'c -> ('c -> bool -> id option -> 'a -> 'c) -> 'c

(** Returns (top,bot) such that the document is morally (top @ s @ bot) where
    s is the focused part.  @raise Invalid_argument *)
val context : 'a document -> (id * 'a) list * (id * 'a) list

(** debug print *)
val print :
  'a document -> (bool -> id option -> 'a ->  Pp.t) -> Pp.t

(** Callbacks on documents *)

class type ['a] signals =
  object
    method popped : callback:('a -> ('a list * 'a list) option -> unit) -> unit
    method pushed : callback:('a -> ('a list * 'a list) option -> unit) -> unit
  end

val connect : 'a document -> 'a signals
