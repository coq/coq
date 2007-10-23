(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: transactional_stack.ml aspiwack $ *)

(* This module implements a datastructure that is not strictly bound
   to the interractive proof system. But currently it is used as an 
   undo stack for the proof system thus it is present in the proofs
   directory *)

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


(* The internal representation of a transactional stack is essentially 
   a stack of lists, stack being represented as pointers to a list *)

module Stack : (sig
		  type 'a stack
		  val create : unit -> 'a stack
		  val push : 'a -> 'a stack -> unit
		  val pop : 'a stack -> 'a
		  val snapshot : 'a stack -> 'a list
		  val lock : 'a stack -> unit
		  val unlock : 'a stack -> unit
		  val locked : 'a stack -> bool
		end) = 
  (* arnaud: the type of Stack has not been abstracted yet
             out of sheer lazyness *)
  (* stacks are basically a list without the possibility of map/fold.
     they contain an extra lock that is hear for pure safety reasons.
     trying to push or pop to a locked stack raises an anomaly *)
  struct
    type 'a stack = {mutable stack : 'a list ; mutable locked : bool }

    let create () = { stack = [] ; locked = false}
    let push a st = 
      if st.locked then
	Util.anomaly 
	  "Transactional_stack.Stack.push: nsafe use of a stack"
      else
	st.stack <- a::st.stack
	
    let pop st = 
      if st.locked then
	Util.anomaly 
	  "Transactional_stack.Stack.pop: unsafe use of a stack"
      else
      match st.stack with
      | [] -> raise Not_found
      | a::r -> st.stack <- r ; a
    let snapshot st = st.stack

    let lock st = st.locked <- true
    let unlock st = st.locked <- false

    let locked st = st.locked
  end


type 'a transactional_stack = 'a list Stack.stack
type 'a transaction = { transaction: 'a Stack.stack;
		        t_stack: 'a transactional_stack }


(* General note : freezing/unfreezing of transactional stacks and
   death of transactions both use the lock mechanism of stacks.
   In some case it imposes naturally a restriction, in other cases
   we also need to check the lock manually. *)


let start_transaction t_st = 
  if Stack.locked t_st then
    Util.anomaly 
      "Transitional_stack.start_transaction: cannot start a transaction from a frozen stack"
  else
    Stack.lock t_st;
    { transaction = Stack.create () ;
      t_stack = t_st }

let commit tr =
  if Stack.locked tr.transaction then
    Util.anomaly "Transitional_stack.commit: cannot commit a dead transaction"
  else
    Stack.unlock tr.t_stack;
    Stack.push (Stack.snapshot tr.transaction) tr.t_stack;
    Stack.lock tr.transaction
			 
let rollback cont tr =
  if Stack.locked tr.transaction then
    Util.anomaly 
      "Transitional_stack.rollback: cannot rollback a dead transaction"
  else
    Stack.unlock tr.t_stack;
    Stack.lock tr.transaction;
    cont (Stack.snapshot tr.transaction)



let push action tr = Stack.push action tr.transaction


let pop cont t_st =
  cont (Stack.pop t_st)
