(* tests of Local versions of Set Printing All/Sugared/Defaults *)

(* an example use *)

Section Example.
  Local Set Printing All.
  Definition foo := id nat.
  Print foo.
End Example.
Print foo.

(* the default printing options *)
Test Printing Allow Match Default Clause.
Test Printing Coercions.
Test Printing Compact Contexts.
Test Printing Existential Instances.
Test Printing Factorizable Match Patterns.
Test Printing Implicit.
Test Printing Implicit Defensive.
Test Printing Matching.
Test Printing Notations.
Test Printing Primitive Projection Compatibility.
Test Printing Primitive Projection Parameters.
Test Printing Projections.
Test Printing Records.
Test Printing Synth.
Test Printing Universes.
Test Printing Wildcard.

Section AllSection.
  Local Set Printing All.
  Test Printing Allow Match Default Clause.
  Test Printing Coercions.
  Test Printing Compact Contexts.
  Test Printing Existential Instances.
  Test Printing Factorizable Match Patterns.
  Test Printing Implicit.
  Test Printing Implicit Defensive.
  Test Printing Matching.
  Test Printing Notations.
  Test Printing Primitive Projection Compatibility.
  Test Printing Primitive Projection Parameters.
  Test Printing Projections.
  Test Printing Records.
  Test Printing Synth.
  Test Printing Universes.
  Test Printing Wildcard.
End AllSection.

(* should see defaults agains *)
Test Printing Allow Match Default Clause.
Test Printing Coercions.
Test Printing Compact Contexts.
Test Printing Existential Instances.
Test Printing Factorizable Match Patterns.
Test Printing Implicit.
Test Printing Implicit Defensive.
Test Printing Matching.
Test Printing Notations.
Test Printing Primitive Projection Compatibility.
Test Printing Primitive Projection Parameters.
Test Printing Projections.
Test Printing Records.
Test Printing Synth.
Test Printing Universes.
Test Printing Wildcard.

Section SugaredSection.
  Local Set Printing Sugared.
  Test Printing Allow Match Default Clause.
  Test Printing Coercions.
  Test Printing Compact Contexts.
  Test Printing Existential Instances.
  Test Printing Factorizable Match Patterns.
  Test Printing Implicit.
  Test Printing Implicit Defensive.
  Test Printing Matching.
  Test Printing Notations.
  Test Printing Primitive Projection Compatibility.
  Test Printing Primitive Projection Parameters.
  Test Printing Projections.
  Test Printing Records.
  Test Printing Synth.
  Test Printing Universes.
  Test Printing Wildcard.
End SugaredSection.

(* should see defaults another time *)
Test Printing Allow Match Default Clause.
Test Printing Coercions.
Test Printing Compact Contexts.
Test Printing Existential Instances.
Test Printing Factorizable Match Patterns.
Test Printing Implicit.
Test Printing Implicit Defensive.
Test Printing Matching.
Test Printing Notations.
Test Printing Primitive Projection Compatibility.
Test Printing Primitive Projection Parameters.
Test Printing Projections.
Test Printing Records.
Test Printing Synth.
Test Printing Universes.
Test Printing Wildcard.

(* should see All options here *)
Set Printing All.
Test Printing Allow Match Default Clause.
Test Printing Coercions.
Test Printing Compact Contexts.
Test Printing Existential Instances.
Test Printing Factorizable Match Patterns.
Test Printing Implicit.
Test Printing Implicit Defensive.
Test Printing Matching.
Test Printing Notations.
Test Printing Primitive Projection Compatibility.
Test Printing Primitive Projection Parameters.
Test Printing Projections.
Test Printing Records.
Test Printing Synth.
Test Printing Universes.
Test Printing Wildcard.

Section DefaultsSection.
  Local Set Printing Defaults.
  Test Printing Allow Match Default Clause.
  Test Printing Coercions.
  Test Printing Compact Contexts.
  Test Printing Existential Instances.
  Test Printing Factorizable Match Patterns.
  Test Printing Implicit.
  Test Printing Implicit Defensive.
  Test Printing Matching.
  Test Printing Notations.
  Test Printing Primitive Projection Compatibility.
  Test Printing Primitive Projection Parameters.
  Test Printing Projections.
  Test Printing Records.
  Test Printing Synth.
  Test Printing Universes.
  Test Printing Wildcard.
End DefaultsSection.

(* should see All options again *)
Test Printing Allow Match Default Clause.
Test Printing Coercions.
Test Printing Compact Contexts.
Test Printing Existential Instances.
Test Printing Factorizable Match Patterns.
Test Printing Implicit.
Test Printing Implicit Defensive.
Test Printing Matching.
Test Printing Notations.
Test Printing Primitive Projection Compatibility.
Test Printing Primitive Projection Parameters.
Test Printing Projections.
Test Printing Records.
Test Printing Synth.
Test Printing Universes.
Test Printing Wildcard.
