
(* $Id$ *)

open Names

type mind_entry

type mutual_inductive_body

type mutual_inductive_entry = section_path * mutual_inductive_body

val mind_type_finite : mutual_inductive_body -> int -> bool
