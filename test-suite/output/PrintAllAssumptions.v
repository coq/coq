(** Test for Set Printing All Assumptions *)
Require Import TestSuite.impred_set_prereq.

(** Without the flag, impredicative_set is not in the current env,
    so Print Assumptions hides the theory dependency *)
Print Assumptions impred_def.

(** With the flag, per-definition theory info is shown *)
Set Printing All Assumptions.
Print Assumptions impred_def.

(** Inductive that uses impredicative Set should show it *)
Print Assumptions impred_ind.

(** Inductive that does not use impredicative Set should not show ImpredicativeSet axiom *)
Print Assumptions normal_ind.

(** Definitions merely typechecked with -impredicative-set but not
    relying on it are not reported, even with the flag set *)
Print Assumptions impred_unused.
Print Assumptions IdSet.

(** Reliance via a subterm that only typechecks with Set impredicative *)
Print Assumptions impred_def_nested.
Print Assumptions impred_ind_nested.

(** The impredicative product rule fired during typechecking, but the
    definition does not rely on it: cumulativity absorbs the sort
    difference, and the re-typechecking pass exonerates it *)
Print Assumptions impred_fires_but_unused.

(** Reliance inside opaque proof bodies (tracked with the opaque proof) *)
Print Assumptions impred_opaque_used.
Print Assumptions impred_opaque_unused.

(** Parameterized inductives: no false positive, and no false negative *)
Print Assumptions param_ind.
Print Assumptions param_impred_ind.
