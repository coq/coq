(* tacinvutils.ml *)
(*s utilities *)

(*i*)
open Termops
open Equality
open Names
open Pp
open Tacmach
open Proof_type
open Tacinterp
open Tactics
open Tacticals
open Term
open Util
open Printer
open Reductionops
open Inductiveops
open Coqlib
open Refine
open Evd
(*i*)

(* printing debugging *)
val prconstr: constr -> unit
val prlistconstr: constr list  -> unit
val prNamedConstr:string -> constr -> unit
val prNamedLConstr:string -> constr list -> unit
val prstr: string -> unit 


val mknewmeta: unit -> constr
val mknewexist: unit -> existential
val resetmeta: unit -> unit (* safe *)
val resetexist: unit -> unit (* be careful with this one *)
val mkevarmap_from_listex: (Term.existential * Term.types) list -> evar_map
val mkEq: types -> constr -> constr -> constr
(* let mkEq typ c1 c2 =   mkApp (build_coq_eq_data.eq(),[| typ; c1; c2|]) *)
val mkRefl: types -> constr -> constr
val buildrefl_from_eqs: constr list -> constr list
(* typ c1 =  mkApp ((constant ["Coq"; "Init"; "Logic"] "refl_equal"), [| typ; c1|]) *)

val nth_dep_constructor: constr -> int -> (constr*int)

val prod_it_lift:  (name*constr) list -> constr -> constr
val prod_it_anonym_lift: constr -> constr list -> constr
val lam_it_anonymous: constr -> constr list -> constr
val lift1L: (constr list) -> constr list
val popn: int -> constr -> constr
val lambda_id: constr -> constr -> constr -> constr
val prod_id: constr -> constr -> constr -> constr


val name_of_string : string -> name
val newname_append: name -> string -> name

val apply_eqtrpl: constr*(constr*constr*constr) -> constr -> constr
val substitterm: int -> constr -> constr -> constr -> constr
val apply_leqtrpl_t: 
  constr -> (constr*(constr*constr*constr)) list -> constr
val apply_eq_leqtrpl: 
  (constr*(constr*constr*constr)) list -> constr -> (constr*(constr*constr*constr)) list
(* val apply_leq_lt: constr list -> constr list -> constr list *)

val hdMatchSub: constr -> constr -> constr list
val hdMatchSub_cpl: constr -> int*int -> constr list
val exchange_hd_prod: constr -> constr -> constr
val exchange_reli_arrayi_L: constr array  -> int*int -> constr list -> constr list
val substit_red: int -> constr -> constr -> constr -> constr
val expand_letins: constr -> constr

val def_of_const: constr -> constr
val name_of_const: constr -> string

(*i
 *** Local Variables: ***
 *** compile-command: "make -C ../.. contrib/funind/tacinvutils.cmi" ***
 *** End: ***
i*)

