Unset Elimination Schemes.
Set Printing Universes.

(** In this file we test the generation and naming of elimination schemes. *)

(** * Schemes for inductive SProp *)

  (** Here is an inductive SProp. *)

  Inductive fooSProp : SProp := aSP | bSP.

  (** ** Try Induction into all Sorts *)

       Scheme Induction for fooSProp Sort SProp. (* fooSProp_inds *)
  Fail Scheme Induction for fooSProp Sort Prop.
  Fail Scheme Induction for fooSProp Sort Set.
  Fail Scheme Induction for fooSProp Sort Type.
  Fail Scheme Induction for fooSProp Sort Poly.

  About fooSProp_inds.

  (** ** Try Minimality into all Sorts *)

       Scheme Minimality for fooSProp Sort SProp. (* fooSProp_inds_nodep *)
  Fail Scheme Minimality for fooSProp Sort Prop.
  Fail Scheme Minimality for fooSProp Sort Set.
  Fail Scheme Minimality for fooSProp Sort Type.
  Fail Scheme Minimality for fooSProp Sort Poly.

  About fooSProp_inds_nodep.

  (** ** Try Elimination into all Sorts *)

       Scheme Elimination for fooSProp Sort SProp. (* fooSProp_cases *)
  Fail Scheme Elimination for fooSProp Sort Prop.
  Fail Scheme Elimination for fooSProp Sort Set.
  Fail Scheme Elimination for fooSProp Sort Type.
  Fail Scheme Elimination for fooSProp Sort Poly.

  About fooSProp_cases.

  (** ** Try Case into all Sorts *)

       Scheme Case for fooSProp Sort SProp. (* fooSProp_cases_nodep *)
  Fail Scheme Case for fooSProp Sort Prop.
  Fail Scheme Case for fooSProp Sort Set.
  Fail Scheme Case for fooSProp Sort Type.
  Fail Scheme Case for fooSProp Sort Poly.

  About fooSProp_cases_nodep.

  (** ** Scheme Equality *)

  Fail Scheme Equality for fooSProp.

(** * Schemes for inductive Prop *)

  (** Here is an inductive Prop. *)

  Inductive fooProp : Prop := aP | bP.

  (** ** Try Induction into all Sorts *)

       Scheme Induction for fooProp Sort SProp. (* fooProp_inds_dep *)
       Scheme Induction for fooProp Sort Prop.  (* fooProp_ind_dep *)
  Fail Scheme Induction for fooProp Sort Set.
  Fail Scheme Induction for fooProp Sort Type.
  Fail Scheme Induction for fooProp Sort Poly.

  About fooProp_inds_dep.
  About fooProp_ind_dep.

  (** ** Try Minimality into all Sorts *)

       Scheme Minimality for fooProp Sort SProp. (* fooProp_inds *)
       Scheme Minimality for fooProp Sort Prop.  (* fooProp_ind *)
  Fail Scheme Minimality for fooProp Sort Set.
  Fail Scheme Minimality for fooProp Sort Type.
  Fail Scheme Minimality for fooProp Sort Poly.

  About fooProp_inds.
  About fooProp_ind.

  (** ** Try Elimination into all Sorts *)

       Scheme Elimination for fooProp Sort SProp. (* fooProp_cases_dep *)
       Scheme Elimination for fooProp Sort Prop.  (* fooProp_case_dep *)
  Fail Scheme Elimination for fooProp Sort Set.
  Fail Scheme Elimination for fooProp Sort Type.
  Fail Scheme Elimination for fooProp Sort Poly.

  About fooProp_cases_dep.
  About fooProp_case_dep.

  (** ** Try Case into all Sorts *)

       Scheme Case for fooProp Sort SProp. (* fooProp_cases *)
       Scheme Case for fooProp Sort Prop.  (* fooProp_case *)
  Fail Scheme Case for fooProp Sort Set.
  Fail Scheme Case for fooProp Sort Type.
  Fail Scheme Case for fooProp Sort Poly.

  About fooProp_cases.
  About fooProp_case.

  (** ** Scheme Equality *)

  Fail Scheme Equality for fooProp.

(** * Schemes for inductive Set *)

  (** Here is an inductive Set. *)

  Inductive fooSet : Set := aS | bS.

  (** ** Try Induction into all Sorts *)

  Scheme Induction for fooSet Sort SProp. (* fooSet_inds *)
  Scheme Induction for fooSet Sort Prop.  (* fooSet_ind *)
  Scheme Induction for fooSet Sort Set.   (* fooSet_rec *)
  Scheme Induction for fooSet Sort Type.  (* fooSet_rect *)
  Scheme Induction for fooSet Sort Poly.  (* fooSet_elim *)

  About fooSet_inds.
  About fooSet_ind.
  About fooSet_rec.
  About fooSet_rect.
  About fooSet_elim.

  (** ** Try Minimality into all Sorts *)

  Scheme Minimality for fooSet Sort SProp. (* fooSet_inds_nodep *)
  Scheme Minimality for fooSet Sort Prop.  (* fooSet_ind_nodep *)
  Scheme Minimality for fooSet Sort Set.   (* fooSet_rec_nodep *)
  Scheme Minimality for fooSet Sort Type.  (* fooSet_rect_nodep *)
  Scheme Minimality for fooSet Sort Poly.  (* fooSet_elim_nodep *)

  About fooSet_inds_nodep.
  About fooSet_ind_nodep.
  About fooSet_rec_nodep.
  About fooSet_rect_nodep.
  About fooSet_elim_nodep.

  (** **  Try Elimination into all Sorts *)

  (** Unforunately there is some overlap with names so we need to create a fresh inductive. *)
  Inductive fooSet' : Set := aS' | bS'.

  Scheme Elimination for fooSet Sort SProp. (* fooSet_cases *)
  Scheme Elimination for fooSet Sort Prop.  (* fooSet_case *)
  Scheme Elimination for fooSet' Sort Set.  (* fooSet'_case *)
  Scheme Elimination for fooSet' Sort Type. (* fooSet'_caset *)
  Scheme Elimination for fooSet' Sort Poly. (* fooSet'_casep *)

  About fooSet_cases.
  About fooSet_case.
  About fooSet'_case.
  About fooSet'_caset.
  About fooSet'_casep.

   (** ** Try Case into all Sorts *)

  Scheme Case for fooSet Sort SProp. (* fooSet_cases_nodep *)
  Scheme Case for fooSet Sort Prop.  (* fooSet_case_nodep *)
  Scheme Case for fooSet' Sort Set.  (* fooSet'_case_nodep *)
  Scheme Case for fooSet' Sort Type. (* fooSet'_caset_nodep *)
  Scheme Case for fooSet' Sort Poly. (* fooSet'_casep_nodep *)

  About fooSet_cases_nodep.
  About fooSet_case_nodep.
  About fooSet'_case_nodep.
  About fooSet'_caset_nodep.
  About fooSet'_casep_nodep.

  (** ** Scheme Equality *)

  Scheme Equality for fooSet.

  About fooSet_beq.
  About fooSet_eq_dec.
  About internal_fooSet_dec_bl.
  About internal_fooSet_dec_lb.

(** * Schemes for inductive Type *)

  (** Here is an inductive Type. *)

  Inductive fooType@{u} : Type@{u} := aT | bT.

  (** ** Try Induction into all Sorts *)

  Scheme Induction for fooType Sort SProp. (* fooType_inds *)
  Scheme Induction for fooType Sort Prop.  (* fooType_ind *)
  Scheme Induction for fooType Sort Set.   (* fooType_rec *)
  Scheme Induction for fooType Sort Type.  (* fooType_rect *)
  Scheme Induction for fooType Sort Poly.  (* fooType_elim *)

  About fooType_inds.
  About fooType_ind.
  About fooType_rec.
  About fooType_rect.
  About fooType_elim.

  (** ** Try Minimality into all Sorts *)

  Scheme Minimality for fooType Sort SProp. (* fooType_inds_nodep *)
  Scheme Minimality for fooType Sort Prop.  (* fooType_ind_nodep *)
  Scheme Minimality for fooType Sort Set.   (* fooType_rec_nodep *)
  Scheme Minimality for fooType Sort Type.  (* fooType_rect_nodep *)
  Scheme Minimality for fooType Sort Poly.  (* fooType_elim_nodep *)

  About fooType_inds_nodep.
  About fooType_ind_nodep.
  About fooType_rec_nodep.
  About fooType_rect_nodep.
  About fooType_elim_nodep.

  (** ** Try Elimination into all Sorts *)

  (** Unforunately there is some overlap with names so we need to create a fresh inductive. *)
  Inductive fooType'@{u} : Type@{u} := aT' | bT'.

  Scheme Elimination for fooType Sort SProp. (* fooType_cases *)
  Scheme Elimination for fooType Sort Prop.  (* fooType_case *)
  Scheme Elimination for fooType' Sort Set.  (* fooType'_case *)
  Scheme Elimination for fooType' Sort Type. (* fooType'_caset *)
  Scheme Elimination for fooType' Sort Poly. (* fooType'_casep *)

  About fooType_cases.
  About fooType_case.
  About fooType'_case.
  About fooType'_caset.
  About fooType'_casep.

  (** ** Try Case into all Sorts *)

  Scheme Case for fooType Sort SProp. (* fooType_cases_nodep *)
  Scheme Case for fooType Sort Prop.  (* fooType_case_nodep *)
  Scheme Case for fooType' Sort Set.  (* fooType'_case_nodep *)
  Scheme Case for fooType' Sort Type. (* fooType'_caset_nodep *)
  Scheme Case for fooType' Sort Poly. (* fooType'_casep_nodep *)

  About fooType_cases_nodep.
  About fooType_case_nodep.
  About fooType'_case_nodep.
  About fooType'_caset_nodep.
  About fooType'_casep_nodep.

  (** ** Scheme Equality *)

  Scheme Equality for fooType.

  About fooType_beq.
  About fooType_eq_dec.
  About internal_fooType_dec_bl.
  About internal_fooType_dec_lb.

(** * Schemes for inductive sort poly *)

  (** Here is an inductive Type. *)

  Polymorphic Inductive fooPoly@{q|u|} : Type@{q|u} := aPo | bPo.

  (** ** Try Induction into all Sorts *)

  Fail Scheme Induction for fooPoly Sort SProp.
  Fail Scheme Induction for fooPoly Sort Prop.
  Fail Scheme Induction for fooPoly Sort Set.
  Fail Scheme Induction for fooPoly Sort Type.
  Scheme Induction for fooPoly Sort Poly.  (* fooPoly_elim *)

  About fooPoly_elim.

  (** ** Try Minimality into all Sorts *)

  Fail Scheme Minimality for fooPoly Sort SProp.
  Fail Scheme Minimality for fooPoly Sort Prop.
  Fail Scheme Minimality for fooPoly Sort Set.
  Fail Scheme Minimality for fooPoly Sort Type.
  Scheme Minimality for fooPoly Sort Poly.  (* fooPoly_elim_nodep *)

  About fooPoly_elim_nodep.

  (** ** Try Elimination into all Sorts *)

  (** Unforunately there is some overlap with names so we need to create a fresh inductive. *)
  Polymorphic Inductive fooPoly'@{q|u|} : Type@{q|u} := aPo' | bPo'.

  (* XXX why is the quality of the inductive getting unified with the
     target sort except in the Prop case? *)
  Scheme Elimination for fooPoly Sort SProp. (* fooPoly_cases *)
  Fail Scheme Elimination for fooPoly Sort Prop.
  Scheme Elimination for fooPoly' Sort Set.  (* fooPoly'_case *)
  Scheme Elimination for fooPoly' Sort Type. (* fooPoly'_caset *)
  Scheme Elimination for fooPoly' Sort Poly. (* fooPoly'_casep *)

  About fooPoly_cases.
  About fooPoly_case.
  About fooPoly'_case.
  About fooPoly'_caset.
  About fooPoly'_casep.

  (** ** Try Case into all Sorts *)

  Scheme Case for fooPoly Sort SProp. (* fooPoly_cases_nodep *)
  Fail Scheme Case for fooPoly Sort Prop.  (* fooPoly_case_nodep *)
  Scheme Case for fooPoly' Sort Set.  (* fooPoly'_case_nodep *)
  Scheme Case for fooPoly' Sort Type. (* fooPoly'_caset_nodep *)
  Scheme Case for fooPoly' Sort Poly. (* fooPoly'_casep_nodep *)

  About fooPoly_cases_nodep.
  About fooPoly_case_nodep.
  About fooPoly'_case_nodep.
  About fooPoly'_caset_nodep.
  About fooPoly'_casep_nodep.

  (** ** Scheme Equality *)

  Fail Scheme Equality for fooPoly.
  (* XXX error message claims fooPoly is a proposition *)

Set Elimination Schemes.

Inductive F f := C : f -> F f.
About F_rect.

Inductive PP P := D : P -> PP P.
About PP_rect.
