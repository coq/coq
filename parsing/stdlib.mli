
(* $Id$ *)

open Term

(*s This module collects the global references of the standard library
    used in ocaml files *)

(* Natural numbers *)
val glob_nat : global_reference
val glob_O : global_reference
val glob_S : global_reference

(* Special variable for pretty-printing of constant naturals *)
val glob_My_special_variable_nat : global_reference
