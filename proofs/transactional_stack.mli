(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: transactional_stack.mli aspiwack $ *)

(* The datastructure implemented in this module is a transactional 
   stack, i.e. a stack of transactions. A transaction is a list of 
   sequential actions (the type of action is 'a (independent from the
   implementation)) which are pushed one after another. When the 
   transaction is finished, it is then committed to the stack.
   Other basic operations include rollback (cancelling the current 
   transaction), pop (consuming the last committed transaction).

   In the case of an undo stack, here is the spirit of how it is used:
   when the user types a command, first, a transaction is started, 
   then for each atomic action executed by the command, an action
   to revert it is pushed in the transaction.
   If the command fails, then the transaction is rolled back
   If the command succeeds, then the transaction is committed.

   In case an undo happen, the last transaction is popped, and 
   all of its action are undone. 

   The rollback and pop operations are implemented in the continuation
   passing style, because they are meant to be easily lifted *)

type 'a transactional_stack
 (** The type of transactional stacks *)
type 'a transaction
 (** The type of handlers to transactions (they are implicitely associated 
     to a stack) *)

val start_transaction :  'a transactional_stack -> 'a transaction
 (** [start_transaction st] starts a new transaction bound to the
     stack [st]. In addition [st] is frozen until the new transaction
     ends. (While [st] is frozen you can't open any other transaction,
     nor pop the last transaction, it would raise an anomaly) *)

val commit : 'a transaction -> unit
 (** [commit tr] commits the transaction [tr] to the stack it is bound
     to. The transaction is then killed (you can't use it anymore, trying
     to do so raises an anomaly) and the associated stack is released. *)
			 
val rollback : ('a list -> 'b) -> 'a transaction -> 'b
 (** [rollback cont tr] rolls the transaction back, by executing
     cont on the list representing the transaction. The transaction 
     is then killed and the associated stack released. *)


val push : 'a -> 'a transaction -> unit
 (** [push a tr] pushes the action [a] onto the transaction [tr] *)


val pop  : ('a list -> 'b) -> 'a transactional_stack -> 'b
 (** [pop cont st] pops the last transaction out of [st] 
     and applies [cont] to the list representing it *)
