(***************************************************************************

This module defines the class of parameterized signatures for parameterized 
words

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


let verbose = ref 5

let debug ?(f=prerr_endline) k s  =
  if k <= !verbose then
    begin
      f s;
      flush stdout
    end

class type parameter_c =
object
  method parameters : Linear_constraints.var_env
  method print : unit -> unit
end


		 
(*

  This module defines the class of parameterized signatures for parameterized 
  words

  \subsection{The parameterized signature type}

*)

open Format 

  
type element = 
    { sig_symbol : string;
      sig_index : Linear_constraints.expr list;
      sig_constr : Linear_constraints.formula;
      sig_env : Linear_constraints.var_env
    }

(* The general signature class.*)
class type parameterized_signature =
object
  val psig :  (string,element) Hashtbl.t
  val parameters : parameter_c

    (* [decoration_of_symbol f] returns the index of the full
       description of the symbol [f] and its associated constraint. *)
    method decoration_of_symbol : string -> element

    method to_list : unit -> element list
    method parameters : parameter_c
    method print : unit -> unit
    method print_element : element -> unit
  end

