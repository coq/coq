open Opname
open Jterm

type rule =
 | Ax | Andr | Andl | Orr | Orr1 | Orr2 | Orl | Impr | Impl | Negr | Negl
 | Allr | Alll| Exr | Exl | Fail | Falsel | Truer

let ruletable = function
 | Fail -> "Fail"
 | Ax ->     "Ax"
 | Negl ->  "Negl"
 | Negr ->  "Negr"
 | Andl ->  "Andl"
 | Andr ->  "Andr"
 | Orl ->   "Orl"
 | Orr ->   "Orr"
 | Orr1 ->   "Orr1"
 | Orr2 ->   "Orr2"
 | Impl ->   "Impl"
 | Impr ->   "Impr"
 | Exl ->   "Exl"
 | Exr ->   "Exr"
 | Alll ->   "Alll"
 | Allr ->   "Allr"
 | Falsel -> "Falsel"
 | Truer -> "Truer"

module type JLogicSig =
sig
   (* understanding the input *)
	val is_all_term	: term -> bool
	val dest_all : term -> string * term * term
	val is_exists_term : term -> bool
	val dest_exists : term -> string * term * term
	val is_and_term : term -> bool
	val dest_and : term -> term * term
	val is_or_term : term -> bool
	val dest_or : term -> term * term
	val is_implies_term : term -> bool
	val dest_implies : term -> term * term
	val is_not_term : term -> bool
	val dest_not : term -> term 

   (* processing the output *)
   type inf_step = rule * (string * term) * (string * term)
   type inference = inf_step list
(* type inference *)
   val empty_inf : inference
   val append_inf : inference -> (string * term) -> (string * term) -> rule -> inference
   val print_inf : inference -> unit
end;;

(* Copy from [term_op_std.ml]: *)

   let rec print_address int_list =
      match int_list with
       | [] ->
            Format.print_string ""
       | hd::rest ->
            begin
               Format.print_int hd;
               print_address rest
            end

module JLogic: JLogicSig =
struct
  let is_all_term = Jterm.is_all_term
  let dest_all = Jterm.dest_all
  let is_exists_term = Jterm.is_exists_term
  let dest_exists = Jterm.dest_exists
  let is_and_term = Jterm.is_and_term
  let dest_and = Jterm.dest_and
  let is_or_term = Jterm.is_or_term
  let dest_or = Jterm.dest_or
  let is_implies_term = Jterm.is_implies_term
  let dest_implies = Jterm.dest_implies
  let is_not_term = Jterm.is_not_term
  let dest_not = Jterm.dest_not

  type inf_step = rule * (string * term) * (string * term)
  type inference = inf_step list

  let empty_inf = []
  let append_inf inf t1 t2 rule =
    (rule, t1, t2)::inf

  let rec print_inf inf =
   match inf with
  |  [] -> print_string "."; Format.print_flush ()
  |  (rule, (n1,t1), (n2,t2))::d ->
      print_string (ruletable rule);
      print_string (":("^n1^":");
      print_term stdout t1;
      print_string (","^n2^":");
      print_term stdout t2;
      print_string ")\n";
      print_inf d
end;;

let show_loading s = print_string s
type my_Debug = { mutable debug_name: string;
                  mutable debug_description: string;
                  debug_value: bool
                }

let create_debug x = ref false
