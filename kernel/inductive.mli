
(* $Id$ *)

open Names
open Term
open Sign

type recarg = 
  | Param of int 
  | Norec 
  | Mrec of int 
  | Imbr of section_path * int * (recarg list)

type mutual_inductive_packet = {
  mind_consnames : identifier array;
  mind_typename : identifier;
  mind_lc : constr;
  mind_stamp : name;
  mind_arity : typed_type;
  mind_lamexp : constr option;
  mind_kd : sorts list;
  mind_kn : sorts list;
  mind_listrec : (recarg list) array;
  mind_finite : bool }

type mutual_inductive_body = {
  mind_kind : path_kind;
  mind_ntypes : int;
  mind_hyps : typed_type signature;
  mind_packets : mutual_inductive_packet array;
  mind_singl : constr option;
  mind_nparams : int }

type mutual_inductive_entry = section_path * mutual_inductive_body

val mind_type_finite : mutual_inductive_body -> int -> bool

type mind_specif = {
  mis_sp : section_path;
  mis_mib : mutual_inductive_body;
  mis_tyi : int;
  mis_args : constr array;
  mis_mip : mutual_inductive_packet }

val mis_ntypes : mind_specif -> int
val mis_nconstr : mind_specif -> int
val mis_nparams : mind_specif -> int
val mis_kd : mind_specif -> sorts list
val mis_kn : mind_specif -> sorts list
val mis_recargs : mind_specif -> (recarg list) array array

