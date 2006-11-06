
Require Export Relation_Definitions.

(* Compatibility *)

Definition equiv A (R:A->A->Prop) := 
  reflexive R /\ transitive R /\ symmetric R.

Implicit Arguments reflexive [].
Implicit Arguments transitive [].
Implicit Arguments symmetric [].
Implicit Arguments antisymmetric [].
Implicit Arguments asymmetric [].
Implicit Arguments irreflexive [].
Implicit Arguments preorder [].
Implicit Arguments Build_preorder [].
Implicit Arguments preorder_rect [].
Implicit Arguments preorder_ind [].
Implicit Arguments preorder_rec [].
Implicit Arguments preord_refl [].
Implicit Arguments preord_trans [].
Implicit Arguments order [].
Implicit Arguments Build_order [].
Implicit Arguments order_rect [].
Implicit Arguments order_ind [].
Implicit Arguments order_rec [].
Implicit Arguments ord_refl [].
Implicit Arguments ord_trans [].
Implicit Arguments ord_antisym [].
Implicit Arguments equivalence [].
Implicit Arguments Build_equivalence [].
Implicit Arguments equivalence_rect [].
Implicit Arguments equivalence_ind [].
Implicit Arguments equivalence_rec [].
Implicit Arguments equiv_refl [].
Implicit Arguments equiv_trans [].
Implicit Arguments equiv_sym [].
Implicit Arguments PER [].
Implicit Arguments Build_PER [].
Implicit Arguments PER_rect [].
Implicit Arguments PER_ind [].
Implicit Arguments PER_rec [].
Implicit Arguments per_sym [].
Implicit Arguments per_trans [].
Implicit Arguments inclusion [].
Implicit Arguments same_relation [].
Implicit Arguments commut [].
