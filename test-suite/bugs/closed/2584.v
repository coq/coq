Require Import List.

Set Implicit Arguments.

Definition err : Type := unit. 

Inductive res (A: Type) : Type :=
| OK: A -> res A
| Error: err -> res A. 

Arguments Error [A].

Set Printing Universes.

Section FOO.

Inductive ftyp : Type :=
  | Funit : ftyp 
  | Ffun : list ftyp -> ftyp 
  | Fref : area -> ftyp
with area : Type := 
  | Stored : ftyp -> area        
.

Print ftyp.
(* yields:
Inductive ftyp : Type (* Top.27429 *) :=
    Funit : ftyp | Ffun : list ftyp -> ftyp | Fref : area -> ftyp
  with area : Type (* Set *) :=  Stored : ftyp -> area
*)

Fixpoint tc_wf_type (ftype: ftyp) {struct ftype}: res unit :=
  match ftype with
    | Funit => OK tt
    | Ffun args => 
       ((fix tc_wf_types (ftypes: list ftyp){struct ftypes}: res unit :=
           match ftypes with
             | nil => OK tt
             | t::ts =>
                 match tc_wf_type t with
                   | OK tt => tc_wf_types ts
                   | Error m => Error m 
                 end 
           end) args) 
     | Fref a => tc_wf_area a
   end
with tc_wf_area (ar:area): res unit :=
  match ar with
    | Stored c => tc_wf_type c
  end.

End FOO.

Print ftyp.
(* yields:
Inductive ftyp : Type (* Top.27465 *) :=
    Funit : ftyp | Ffun : list ftyp -> ftyp | Fref : area -> ftyp
  with area : Set :=  Stored : ftyp -> area
*)

Fixpoint tc_wf_type' (ftype: ftyp) {struct ftype}: res unit :=
  match ftype with
    | Funit => OK tt
    | Ffun args => 
       ((fix tc_wf_types (ftypes: list ftyp){struct ftypes}: res unit :=
           match ftypes with
             | nil => OK tt
             | t::ts =>
                 match tc_wf_type' t with
                   | OK tt => tc_wf_types ts
                   | Error m => Error m 
                 end 
           end) args) 
     | Fref a => tc_wf_area' a
   end
with tc_wf_area' (ar:area): res unit :=
  match ar with
    | Stored c => tc_wf_type' c
  end.

(* yields:
Error:
Incorrect elimination of "ar" in the inductive type "area":
the return type has sort "Type (* max(Set, Top.27424) *)" while it
should be "Prop" or "Set".
Elimination of an inductive object of sort Set
is not allowed on a predicate in sort Type
because strong elimination on non-small inductive types leads to paradoxes.
*)
