
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

let mind_type_finite mib i = mib.mind_packets.(i).mind_finite

type mind_specif = {
  mis_sp : section_path;
  mis_mib : mutual_inductive_body;
  mis_tyi : int;
  mis_args : constr array;
  mis_mip : mutual_inductive_packet }

let mis_ntypes mis = mis.mis_mib.mind_ntypes
let mis_nconstr mis = Array.length (mis.mis_mip.mind_consnames)
let mis_nparams mis = mis.mis_mib.mind_nparams
let mis_kd mis = mis.mis_mip.mind_kd
let mis_kn mis = mis.mis_mip.mind_kn
let mis_recargs mis =
  Array.map (fun mip -> mip.mind_listrec) mis.mis_mib.mind_packets

let mind_nth_type_packet mib n = mib.mind_packets.(n)
