(********************************************************************

This module defines the class of parameterized signatures for 
  parameterized words

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

********************************************************************)


(*
  This module defines the class of parameters.

  \subsection{The parameters type}
*)

val verbose : int ref

val debug : ?f:(string -> unit) -> int -> string -> unit


class type parameter_c =
object
  method parameters : Linear_constraints.var_env
  method print : unit -> unit
end

(*
  This module defines the class of parameterized signatures for
  parameterized words.

  \subsection{The parameterized signature type}
*)


(* The type of elements in the signature. 
   For example $a_{i+n}|_{i}i\leq n$ is represented by 
   [{sig_symbol="a";
   sig_index=["i + n"];
   sig_constr= "i <= n"}]
*)


type element = 
    { sig_symbol : string;
      sig_index : Linear_constraints.expr list;
      sig_constr : Linear_constraints.formula;
      sig_env : Linear_constraints.var_env
    }



(* The general signature class.*)
class type parameterized_signature =
object
  val psig : (string,element) Hashtbl.t
  val parameters : parameter_c

    (* [decoration_of_symbol f] returns the index of the full
       description of the symbol [f] and its associated constraint.
    *)
    method decoration_of_symbol : string -> element

    method to_list : unit -> element list
    method parameters : parameter_c
    method print : unit -> unit
    method print_element : element -> unit
  end
