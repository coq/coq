theories/ZArith/Zsyntax.vo: theories/ZArith/Zsyntax.v theories/ZArith/fast_integer.vo theories/ZArith/zarith_aux.vo
theories/ZArith/Zmisc.vo: theories/ZArith/Zmisc.v theories/ZArith/fast_integer.vo theories/ZArith/zarith_aux.vo theories/ZArith/auxiliary.vo theories/ZArith/Zsyntax.vo theories/Bool/Bool.vo
theories/ZArith/Zhints.vo: theories/ZArith/Zhints.v theories/ZArith/zarith_aux.vo theories/ZArith/auxiliary.vo theories/ZArith/Zsyntax.vo theories/ZArith/Zmisc.vo theories/ZArith/Wf_Z.vo
theories/ZArith/ZArith.vo: theories/ZArith/ZArith.v theories/ZArith/fast_integer.vo theories/ZArith/zarith_aux.vo theories/ZArith/auxiliary.vo theories/ZArith/Zsyntax.vo theories/ZArith/ZArith_dec.vo theories/ZArith/Zmisc.vo theories/ZArith/Wf_Z.vo theories/ZArith/Zhints.vo
theories/ZArith/ZArith_dec.vo: theories/ZArith/ZArith_dec.v theories/Bool/Sumbool.vo theories/ZArith/fast_integer.vo theories/ZArith/zarith_aux.vo theories/ZArith/auxiliary.vo theories/ZArith/Zsyntax.vo
theories/ZArith/zarith_aux.vo: theories/ZArith/zarith_aux.v theories/Arith/Arith.vo theories/ZArith/fast_integer.vo
theories/ZArith/Wf_Z.vo: theories/ZArith/Wf_Z.v theories/ZArith/fast_integer.vo theories/ZArith/zarith_aux.vo theories/ZArith/auxiliary.vo theories/ZArith/Zsyntax.vo
theories/ZArith/fast_integer.vo: theories/ZArith/fast_integer.v theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Plus.vo theories/Arith/Mult.vo theories/Arith/Minus.vo
theories/ZArith/auxiliary.vo: theories/ZArith/auxiliary.v theories/Arith/Arith.vo theories/ZArith/fast_integer.vo theories/ZArith/zarith_aux.vo theories/Logic/Decidable.vo theories/Arith/Peano_dec.vo theories/Arith/Compare_dec.vo
theories/Wellfounded/Well_Ordering.vo: theories/Wellfounded/Well_Ordering.v theories/Logic/Eqdep.vo
theories/Wellfounded/Wellfounded.vo: theories/Wellfounded/Wellfounded.v theories/Wellfounded/Disjoint_Union.vo theories/Wellfounded/Inclusion.vo theories/Wellfounded/Inverse_Image.vo theories/Wellfounded/Lexicographic_Exponentiation.vo theories/Wellfounded/Lexicographic_Product.vo theories/Wellfounded/Transitive_Closure.vo theories/Wellfounded/Union.vo theories/Wellfounded/Well_Ordering.vo
theories/Wellfounded/Union.vo: theories/Wellfounded/Union.v theories/Relations/Relation_Operators.vo theories/Relations/Relation_Definitions.vo theories/Wellfounded/Transitive_Closure.vo
theories/Wellfounded/Transitive_Closure.vo: theories/Wellfounded/Transitive_Closure.v theories/Relations/Relation_Definitions.vo theories/Relations/Relation_Operators.vo
theories/Wellfounded/Lexicographic_Product.vo: theories/Wellfounded/Lexicographic_Product.v theories/Logic/Eqdep.vo theories/Relations/Relation_Operators.vo theories/Wellfounded/Transitive_Closure.vo
theories/Wellfounded/Lexicographic_Exponentiation.vo: theories/Wellfounded/Lexicographic_Exponentiation.v theories/Logic/Eqdep.vo theories/Lists/PolyList.vo theories/Lists/PolyListSyntax.vo theories/Relations/Relation_Operators.vo theories/Wellfounded/Transitive_Closure.vo
theories/Wellfounded/Inverse_Image.vo: theories/Wellfounded/Inverse_Image.v
theories/Wellfounded/Inclusion.vo: theories/Wellfounded/Inclusion.v theories/Relations/Relation_Definitions.vo
theories/Wellfounded/Disjoint_Union.vo: theories/Wellfounded/Disjoint_Union.v theories/Relations/Relation_Operators.vo
theories/Sets/Uniset.vo: theories/Sets/Uniset.v theories/Bool/Bool.vo theories/Sets/Permut.vo
theories/Sets/Relations_3.vo: theories/Sets/Relations_3.v theories/Sets/Relations_1.vo theories/Sets/Relations_2.vo
theories/Sets/Relations_3_facts.vo: theories/Sets/Relations_3_facts.v theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Relations_2.vo theories/Sets/Relations_2_facts.vo theories/Sets/Relations_3.vo
theories/Sets/Relations_2.vo: theories/Sets/Relations_2.v theories/Sets/Relations_1.vo
theories/Sets/Relations_2_facts.vo: theories/Sets/Relations_2_facts.v theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Relations_2.vo
theories/Sets/Relations_1.vo: theories/Sets/Relations_1.v
theories/Sets/Relations_1_facts.vo: theories/Sets/Relations_1_facts.v theories/Sets/Relations_1.vo
theories/Sets/Powerset.vo: theories/Sets/Powerset.v theories/Sets/Ensembles.vo theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Partial_Order.vo theories/Sets/Cpo.vo
theories/Sets/Powerset_facts.vo: theories/Sets/Powerset_facts.v theories/Sets/Ensembles.vo theories/Sets/Constructive_sets.vo theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Partial_Order.vo theories/Sets/Cpo.vo theories/Sets/Powerset.vo
theories/Sets/Powerset_Classical_facts.vo: theories/Sets/Powerset_Classical_facts.v theories/Sets/Ensembles.vo theories/Sets/Constructive_sets.vo theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Partial_Order.vo theories/Sets/Cpo.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo
theories/Sets/Permut.vo: theories/Sets/Permut.v
theories/Sets/Partial_Order.vo: theories/Sets/Partial_Order.v theories/Sets/Ensembles.vo theories/Sets/Relations_1.vo
theories/Sets/Multiset.vo: theories/Sets/Multiset.v theories/Sets/Permut.vo theories/Arith/Plus.vo
theories/Sets/Integers.vo: theories/Sets/Integers.v theories/Sets/Finite_sets.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Sets/Powerset_Classical_facts.vo theories/Arith/Gt.vo theories/Arith/Lt.vo theories/Arith/Le.vo theories/Sets/Finite_sets_facts.vo theories/Sets/Image.vo theories/Sets/Infinite_sets.vo theories/Arith/Compare_dec.vo theories/Sets/Relations_1.vo theories/Sets/Partial_Order.vo theories/Sets/Cpo.vo
theories/Sets/Infinite_sets.vo: theories/Sets/Infinite_sets.v theories/Sets/Finite_sets.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Sets/Powerset_Classical_facts.vo theories/Arith/Gt.vo theories/Arith/Lt.vo theories/Arith/Le.vo theories/Sets/Finite_sets_facts.vo theories/Sets/Image.vo
theories/Sets/Image.vo: theories/Sets/Image.v theories/Sets/Finite_sets.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Sets/Powerset_Classical_facts.vo theories/Arith/Gt.vo theories/Arith/Lt.vo theories/Arith/Le.vo theories/Sets/Finite_sets_facts.vo
theories/Sets/Finite_sets.vo: theories/Sets/Finite_sets.v theories/Sets/Ensembles.vo theories/Sets/Constructive_sets.vo
theories/Sets/Finite_sets_facts.vo: theories/Sets/Finite_sets_facts.v theories/Sets/Finite_sets.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Sets/Powerset_Classical_facts.vo theories/Arith/Gt.vo theories/Arith/Lt.vo
theories/Sets/Ensembles.vo: theories/Sets/Ensembles.v
theories/Sets/Cpo.vo: theories/Sets/Cpo.v theories/Sets/Ensembles.vo theories/Sets/Relations_1.vo theories/Sets/Partial_Order.vo
theories/Sets/Constructive_sets.vo: theories/Sets/Constructive_sets.v theories/Sets/Ensembles.vo
theories/Sets/Classical_sets.vo: theories/Sets/Classical_sets.v theories/Sets/Ensembles.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo
theories/Relations/Rstar.vo: theories/Relations/Rstar.v
theories/Relations/Relations.vo: theories/Relations/Relations.v theories/Relations/Relation_Definitions.vo theories/Relations/Relation_Operators.vo theories/Relations/Operators_Properties.vo
theories/Relations/Relation_Operators.vo: theories/Relations/Relation_Operators.v theories/Relations/Relation_Definitions.vo theories/Lists/PolyList.vo theories/Lists/PolyListSyntax.vo
theories/Relations/Relation_Definitions.vo: theories/Relations/Relation_Definitions.v
theories/Relations/Operators_Properties.vo: theories/Relations/Operators_Properties.v theories/Relations/Relation_Definitions.vo theories/Relations/Relation_Operators.vo
theories/Relations/Newman.vo: theories/Relations/Newman.v theories/Relations/Rstar.vo
theories/Reals/TypeSyntax.vo: theories/Reals/TypeSyntax.v
theories/Reals/SplitRmult.vo: theories/Reals/SplitRmult.v theories/Reals/Rbase.vo
theories/Reals/SplitAbsolu.vo: theories/Reals/SplitAbsolu.v theories/Reals/Rbasic_fun.vo
theories/Reals/Rtrigo_fun.vo: theories/Reals/Rtrigo_fun.v theories/Reals/Rseries.vo
theories/Reals/Rsyntax.vo: theories/Reals/Rsyntax.v theories/Reals/Rdefinitions.vo
theories/Reals/Rseries.vo: theories/Reals/Rseries.v theories/Reals/Rderiv.vo theories/Logic/Classical.vo theories/Arith/Compare.vo
theories/Reals/Rlimit.vo: theories/Reals/Rlimit.v theories/Reals/Rbasic_fun.vo theories/Logic/Classical_Prop.vo theories/Reals/DiscrR.vo contrib/fourier/Fourier.vo theories/Reals/SplitAbsolu.vo
theories/Reals/R_Ifp.vo: theories/Reals/R_Ifp.v theories/Reals/Rbase.vo contrib/omega/Omega.vo
theories/Reals/Rfunctions.vo: theories/Reals/Rfunctions.v theories/Reals/Rlimit.vo contrib/omega/Omega.vo
theories/Reals/Reals.vo: theories/Reals/Reals.v theories/Reals/Rdefinitions.vo theories/Reals/TypeSyntax.vo theories/Reals/Raxioms.vo theories/Reals/Rbase.vo theories/Reals/R_Ifp.vo theories/Reals/Rbasic_fun.vo theories/Reals/Rlimit.vo theories/Reals/Rfunctions.vo theories/Reals/Rderiv.vo theories/Reals/Rseries.vo theories/Reals/Rtrigo_fun.vo
theories/Reals/Rderiv.vo: theories/Reals/Rderiv.v theories/Reals/Rfunctions.vo theories/Logic/Classical_Pred_Type.vo contrib/omega/Omega.vo
theories/Reals/Rdefinitions.vo: theories/Reals/Rdefinitions.v theories/ZArith/ZArith.vo theories/Reals/TypeSyntax.vo
theories/Reals/Rbasic_fun.vo: theories/Reals/Rbasic_fun.v theories/Reals/R_Ifp.vo contrib/fourier/Fourier.vo
theories/Reals/Rbase.vo: theories/Reals/Rbase.v theories/Reals/Raxioms.vo contrib/ring/ZArithRing.vo contrib/omega/Omega.vo contrib/field/Field.vo
theories/Reals/Raxioms.vo: theories/Reals/Raxioms.v theories/ZArith/ZArith.vo theories/Reals/Rsyntax.vo theories/Reals/TypeSyntax.vo
theories/Reals/DiscrR.vo: theories/Reals/DiscrR.v theories/Reals/Rbase.vo
theories/Num/SubProps.vo: theories/Num/SubProps.v
theories/Num/Params.vo: theories/Num/Params.v
theories/Num/OppProps.vo: theories/Num/OppProps.v
theories/Num/OppAxioms.vo: theories/Num/OppAxioms.v
theories/Num/NSyntax.vo: theories/Num/NSyntax.v theories/Num/Leibniz/Params.vo
theories/Num/NeqDef.vo: theories/Num/NeqDef.v theories/Num/Leibniz/Params.vo theories/Num/EqParams.vo
theories/Num/LtProps.vo: theories/Num/LtProps.v theories/Num/Nat/Axioms.vo theories/Num/AddProps.vo
theories/Num/LeProps.vo: theories/Num/LeProps.v theories/Num/LtProps.vo theories/Num/LeAxioms.vo
theories/Num/LeAxioms.vo: theories/Num/LeAxioms.v theories/Num/Nat/Axioms.vo theories/Num/LtProps.vo
theories/Num/GtProps.vo: theories/Num/GtProps.v
theories/Num/GtAxioms.vo: theories/Num/GtAxioms.v theories/Num/Nat/Axioms.vo theories/Num/LeProps.vo
theories/Num/GeProps.vo: theories/Num/GeProps.v
theories/Num/GeAxioms.vo: theories/Num/GeAxioms.v theories/Num/Nat/Axioms.vo theories/Num/LtProps.vo
theories/Num/EqParams.vo: theories/Num/EqParams.v theories/Num/Leibniz/Params.vo
theories/Num/EqAxioms.vo: theories/Num/EqAxioms.v theories/Num/Leibniz/Params.vo theories/Num/EqParams.vo theories/Num/Nat/NeqDef.vo theories/Num/Nat/NSyntax.vo
theories/Num/DiscrProps.vo: theories/Num/DiscrProps.v theories/Num/DiscrAxioms.vo theories/Num/LtProps.vo
theories/Num/DiscrAxioms.vo: theories/Num/DiscrAxioms.v theories/Num/Leibniz/Params.vo theories/Num/Nat/NSyntax.vo
theories/Num/Definitions.vo: theories/Num/Definitions.v
theories/Num/Axioms.vo: theories/Num/Axioms.v theories/Num/Leibniz/Params.vo theories/Num/EqParams.vo theories/Num/Nat/NeqDef.vo theories/Num/Nat/NSyntax.vo
theories/Num/AddProps.vo: theories/Num/AddProps.v theories/Num/Nat/Axioms.vo theories/Num/Leibniz/EqAxioms.vo
theories/Logic/JMeq.vo: theories/Logic/JMeq.v
theories/Logic/Eqdep.vo: theories/Logic/Eqdep.v
theories/Logic/Eqdep_dec.vo: theories/Logic/Eqdep_dec.v
theories/Logic/Decidable.vo: theories/Logic/Decidable.v
theories/Logic/Classical.vo: theories/Logic/Classical.v theories/Logic/Classical_Prop.vo theories/Logic/Classical_Pred_Set.vo
theories/Logic/Classical_Type.vo: theories/Logic/Classical_Type.v theories/Logic/Classical_Prop.vo theories/Logic/Classical_Pred_Type.vo
theories/Logic/Classical_Prop.vo: theories/Logic/Classical_Prop.v
theories/Logic/Classical_Pred_Type.vo: theories/Logic/Classical_Pred_Type.v theories/Logic/Classical_Prop.vo
theories/Logic/Classical_Pred_Set.vo: theories/Logic/Classical_Pred_Set.v theories/Logic/Classical_Prop.vo
theories/Lists/TheoryList.vo: theories/Lists/TheoryList.v theories/Lists/PolyList.vo theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Minus.vo theories/Bool/DecBool.vo
theories/Lists/Streams.vo: theories/Lists/Streams.v
theories/Lists/PolyList.vo: theories/Lists/PolyList.v theories/Arith/Le.vo
theories/Lists/PolyListSyntax.vo: theories/Lists/PolyListSyntax.v theories/Lists/PolyList.vo
theories/Lists/List.vo: theories/Lists/List.v theories/Arith/Le.vo
theories/Lists/ListSet.vo: theories/Lists/ListSet.v theories/Lists/PolyList.vo
theories/IntMap/Map.vo: theories/IntMap/Map.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo
theories/IntMap/Mapsubset.vo: theories/IntMap/Mapsubset.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo
theories/IntMap/Maplists.vo: theories/IntMap/Maplists.v theories/IntMap/Addr.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapsubset.vo theories/IntMap/Mapcard.vo theories/IntMap/Mapcanon.vo theories/IntMap/Mapc.vo theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Lists/PolyList.vo theories/Arith/Arith.vo theories/IntMap/Mapiter.vo theories/IntMap/Mapfold.vo
theories/IntMap/Mapiter.vo: theories/IntMap/Mapiter.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Fset.vo theories/Lists/PolyList.vo
theories/IntMap/Mapfold.vo: theories/IntMap/Mapfold.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo theories/IntMap/Lsort.vo theories/IntMap/Mapsubset.vo theories/Lists/PolyList.vo
theories/IntMap/Mapc.vo: theories/IntMap/Mapc.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Fset.vo theories/IntMap/Mapiter.vo theories/IntMap/Mapsubset.vo theories/Lists/PolyList.vo theories/IntMap/Lsort.vo theories/IntMap/Mapcard.vo theories/IntMap/Mapcanon.vo
theories/IntMap/Mapcard.vo: theories/IntMap/Mapcard.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo theories/IntMap/Fset.vo theories/IntMap/Mapsubset.vo theories/Lists/PolyList.vo theories/IntMap/Lsort.vo theories/Arith/Peano_dec.vo
theories/IntMap/Mapcanon.vo: theories/IntMap/Mapcanon.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo theories/IntMap/Fset.vo theories/Lists/PolyList.vo theories/IntMap/Lsort.vo theories/IntMap/Mapsubset.vo theories/IntMap/Mapcard.vo
theories/IntMap/Mapaxioms.vo: theories/IntMap/Mapaxioms.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo
theories/IntMap/Lsort.vo: theories/IntMap/Lsort.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/Lists/PolyList.vo theories/IntMap/Mapiter.vo
theories/IntMap/Fset.vo: theories/IntMap/Fset.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo
theories/IntMap/Allmaps.vo: theories/IntMap/Allmaps.v theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo theories/IntMap/Mapsubset.vo theories/IntMap/Lsort.vo theories/IntMap/Mapfold.vo theories/IntMap/Mapcard.vo theories/IntMap/Mapcanon.vo theories/IntMap/Mapc.vo theories/IntMap/Maplists.vo theories/IntMap/Adalloc.vo
theories/IntMap/Adist.vo: theories/IntMap/Adist.v theories/Bool/Bool.vo theories/ZArith/ZArith.vo theories/Arith/Arith.vo theories/Arith/Min.vo theories/IntMap/Addr.vo
theories/IntMap/Addr.vo: theories/IntMap/Addr.v theories/Bool/Bool.vo theories/ZArith/ZArith.vo
theories/IntMap/Addec.vo: theories/IntMap/Addec.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/ZArith/ZArith.vo theories/IntMap/Addr.vo
theories/IntMap/Adalloc.vo: theories/IntMap/Adalloc.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/ZArith/ZArith.vo theories/Arith/Arith.vo theories/IntMap/Addr.vo theories/IntMap/Adist.vo theories/IntMap/Addec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo
theories/Init/Wf.vo: theories/Init/Wf.v theories/Init/Logic.vo theories/Init/LogicSyntax.vo
theories/Init/Specif.vo: theories/Init/Specif.v theories/Init/Logic.vo theories/Init/LogicSyntax.vo theories/Init/Datatypes.vo
theories/Init/SpecifSyntax.vo: theories/Init/SpecifSyntax.v theories/Init/LogicSyntax.vo theories/Init/Specif.vo
theories/Init/Prelude.vo: theories/Init/Prelude.v theories/Init/Datatypes.vo theories/Init/DatatypesSyntax.vo theories/Init/Logic.vo theories/Init/LogicSyntax.vo theories/Init/Specif.vo theories/Init/SpecifSyntax.vo theories/Init/Peano.vo theories/Init/Wf.vo
theories/Init/Peano.vo: theories/Init/Peano.v theories/Init/Logic.vo theories/Init/LogicSyntax.vo theories/Init/Datatypes.vo
theories/Init/Logic.vo: theories/Init/Logic.v theories/Init/Datatypes.vo
theories/Init/Logic_Type.vo: theories/Init/Logic_Type.v theories/Init/Logic.vo theories/Init/LogicSyntax.vo
theories/Init/Logic_TypeSyntax.vo: theories/Init/Logic_TypeSyntax.v theories/Init/Logic_Type.vo
theories/Init/LogicSyntax.vo: theories/Init/LogicSyntax.v theories/Init/Logic.vo
theories/Init/Datatypes.vo: theories/Init/Datatypes.v
theories/Init/DatatypesSyntax.vo: theories/Init/DatatypesSyntax.v theories/Init/Datatypes.vo
theories/Bool/Zerob.vo: theories/Bool/Zerob.v theories/Arith/Arith.vo theories/Bool/Bool.vo
theories/Bool/Sumbool.vo: theories/Bool/Sumbool.v
theories/Bool/IfProp.vo: theories/Bool/IfProp.v theories/Bool/Bool.vo
theories/Bool/DecBool.vo: theories/Bool/DecBool.v
theories/Bool/Bool.vo: theories/Bool/Bool.v
theories/Bool/BoolEq.vo: theories/Bool/BoolEq.v theories/Bool/Bool.vo
theories/Arith/Wf_nat.vo: theories/Arith/Wf_nat.v theories/Arith/Lt.vo
theories/Arith/Plus.vo: theories/Arith/Plus.v theories/Arith/Le.vo theories/Arith/Lt.vo
theories/Arith/Peano_dec.vo: theories/Arith/Peano_dec.v theories/Logic/Decidable.vo
theories/Arith/Mult.vo: theories/Arith/Mult.v theories/Arith/Plus.vo theories/Arith/Minus.vo theories/Arith/Lt.vo
theories/Arith/Min.vo: theories/Arith/Min.v theories/Arith/Arith.vo
theories/Arith/Minus.vo: theories/Arith/Minus.v theories/Arith/Lt.vo theories/Arith/Le.vo
theories/Arith/Lt.vo: theories/Arith/Lt.v theories/Arith/Le.vo
theories/Arith/Le.vo: theories/Arith/Le.v
theories/Arith/Gt.vo: theories/Arith/Gt.v theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Plus.vo
theories/Arith/Even.vo: theories/Arith/Even.v
theories/Arith/Euclid.vo: theories/Arith/Euclid.v theories/Arith/Mult.vo theories/Arith/Compare_dec.vo theories/Arith/Wf_nat.vo
theories/Arith/EqNat.vo: theories/Arith/EqNat.v
theories/Arith/Div.vo: theories/Arith/Div.v theories/Arith/Le.vo theories/Arith/Compare_dec.vo
theories/Arith/Div2.vo: theories/Arith/Div2.v theories/Arith/Lt.vo theories/Arith/Plus.vo theories/Arith/Compare_dec.vo theories/Arith/Even.vo
theories/Arith/Compare.vo: theories/Arith/Compare.v theories/Arith/Arith.vo theories/Arith/Peano_dec.vo theories/Arith/Compare_dec.vo theories/Arith/Wf_nat.vo theories/Arith/Min.vo
theories/Arith/Compare_dec.vo: theories/Arith/Compare_dec.v theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Gt.vo theories/Logic/Decidable.vo
theories/Arith/Between.vo: theories/Arith/Between.v theories/Arith/Le.vo theories/Arith/Lt.vo
theories/Arith/Arith.vo: theories/Arith/Arith.v theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Plus.vo theories/Arith/Gt.vo theories/Arith/Minus.vo theories/Arith/Mult.vo theories/Arith/Between.vo
test-suite/tactics/TestRefine.vo: test-suite/tactics/TestRefine.v tactics/Refine.vo theories/Init/Wf.vo theories/Arith/Wf_nat.vo theories/Arith/Compare_dec.vo theories/Arith/Lt.vo
test-suite/success/unfold.vo: test-suite/success/unfold.v
test-suite/success/Tauto.vo: test-suite/success/Tauto.v
test-suite/success/mutual_ind.vo: test-suite/success/mutual_ind.v theories/Lists/PolyList.vo
test-suite/success/induct.vo: test-suite/success/induct.v theories/Lists/PolyList.vo
test-suite/success/inds_type_sec.vo: test-suite/success/inds_type_sec.v
test-suite/success/Fourier.vo: test-suite/success/Fourier.v theories/Reals/SplitAbsolu.vo contrib/fourier/Fourier.vo
test-suite/success/fix.vo: test-suite/success/fix.v theories/Bool/Bool.vo theories/ZArith/ZArith.vo
test-suite/success/Field.vo: test-suite/success/Field.v theories/Reals/Reals.vo
test-suite/success/evars.vo: test-suite/success/evars.v
test-suite/success/eqdecide.vo: test-suite/success/eqdecide.v
test-suite/success/eauto.vo: test-suite/success/eauto.v theories/Lists/PolyList.vo
test-suite/success/DiscrR.vo: test-suite/success/DiscrR.v theories/Reals/Reals.vo theories/Reals/DiscrR.vo
test-suite/success/Decompose.vo: test-suite/success/Decompose.v
test-suite/success/Check.vo: test-suite/success/Check.v
test-suite/success/Cases.vo: test-suite/success/Cases.v theories/Bool/Bool.vo theories/Arith/Peano_dec.vo theories/Arith/Arith.vo theories/ZArith/ZArith.vo
test-suite/success/CasesDep.vo: test-suite/success/CasesDep.v theories/Init/Prelude.vo theories/Init/Logic_TypeSyntax.vo theories/Init/Logic_Type.vo
test-suite/success/Case9.vo: test-suite/success/Case9.v
test-suite/success/Case8.vo: test-suite/success/Case8.v
test-suite/success/Case7.vo: test-suite/success/Case7.v
test-suite/success/Case6.vo: test-suite/success/Case6.v
test-suite/success/Case5.vo: test-suite/success/Case5.v
test-suite/success/Case4.vo: test-suite/success/Case4.v
test-suite/success/Case3.vo: test-suite/success/Case3.v
test-suite/success/Case2.vo: test-suite/success/Case2.v
test-suite/success/Case1.vo: test-suite/success/Case1.v
test-suite/success/Case10.vo: test-suite/success/Case10.v
test-suite/success/Apply.vo: test-suite/success/Apply.v
test-suite/failure/Tauto.vo: test-suite/failure/Tauto.v
test-suite/failure/search.vo: test-suite/failure/search.v
test-suite/failure/redef.vo: test-suite/failure/redef.v
test-suite/failure/positivity.vo: test-suite/failure/positivity.v
test-suite/failure/params_ind.vo: test-suite/failure/params_ind.v
test-suite/failure/illtype1.vo: test-suite/failure/illtype1.v
test-suite/failure/fixpoint1.vo: test-suite/failure/fixpoint1.v
test-suite/failure/clash_cons.vo: test-suite/failure/clash_cons.v
test-suite/failure/check.vo: test-suite/failure/check.v
test-suite/failure/Case9.vo: test-suite/failure/Case9.v
test-suite/failure/Case8.vo: test-suite/failure/Case8.v
test-suite/failure/Case7.vo: test-suite/failure/Case7.v
test-suite/failure/Case6.vo: test-suite/failure/Case6.v
test-suite/failure/Case5.vo: test-suite/failure/Case5.v
test-suite/failure/Case4.vo: test-suite/failure/Case4.v
test-suite/failure/Case3.vo: test-suite/failure/Case3.v
test-suite/failure/Case2.vo: test-suite/failure/Case2.v
test-suite/failure/Case1.vo: test-suite/failure/Case1.v
test-suite/failure/Case14.vo: test-suite/failure/Case14.v
test-suite/failure/Case13.vo: test-suite/failure/Case13.v
test-suite/failure/Case12.vo: test-suite/failure/Case12.v
test-suite/failure/Case11.vo: test-suite/failure/Case11.v
test-suite/failure/Case10.vo: test-suite/failure/Case10.v
test-suite/bench/lists-100.vo: test-suite/bench/lists-100.v
test-suite/bench/lists_100.vo: test-suite/bench/lists_100.v
contrib/xml/Xml.vo: contrib/xml/Xml.v contrib/xml/xml.cmo contrib/xml/xmlcommand.cmo contrib/xml/xmlentries.cmo
contrib/setoid/Setoid_replace.vo: contrib/setoid/Setoid_replace.v contrib/setoid/setoid_replace.cmo
contrib/setoid/safe_Setoid_replace.vo: contrib/setoid/safe_Setoid_replace.v contrib/setoid/setoid_replace.cmo
contrib/ring/ZArithRing.vo: contrib/ring/ZArithRing.v contrib/ring/ArithRing.vo theories/ZArith/ZArith.vo theories/Logic/Eqdep_dec.vo
contrib/ring/Setoid_Ring_normalize.vo: contrib/ring/Setoid_Ring_normalize.v contrib/ring/Ring_theory.vo contrib/ring/Quote.vo contrib/setoid/Setoid_replace.vo
contrib/ring/Ring.vo: contrib/ring/Ring.v theories/Bool/Bool.vo contrib/ring/Ring_theory.vo contrib/ring/Quote.vo contrib/ring/Ring_normalize.vo contrib/ring/Ring_abstract.vo contrib/ring/ring.cmo
contrib/ring/Ring_theory.vo: contrib/ring/Ring_theory.v theories/Bool/Bool.vo contrib/setoid/Setoid_replace.vo
contrib/ring/Ring_normalize.vo: contrib/ring/Ring_normalize.v contrib/ring/Ring_theory.vo contrib/ring/Quote.vo
contrib/ring/Ring_abstract.vo: contrib/ring/Ring_abstract.v contrib/ring/Ring_theory.vo contrib/ring/Quote.vo contrib/ring/Ring_normalize.vo
contrib/ring/Quote.vo: contrib/ring/Quote.v contrib/ring/quote.cmo
contrib/ring/false_Ring_normalize.vo: contrib/ring/false_Ring_normalize.v contrib/ring/Ring_theory.vo contrib/ring/Quote.vo contrib/setoid/Setoid_replace.vo
contrib/ring/ArithRing.vo: contrib/ring/ArithRing.v contrib/ring/Ring.vo theories/Arith/Arith.vo theories/Logic/Eqdep_dec.vo
contrib/omega/Zpower.vo: contrib/omega/Zpower.v theories/ZArith/ZArith.vo contrib/omega/Omega.vo contrib/omega/Zcomplements.vo
contrib/omega/Zlogarithm.vo: contrib/omega/Zlogarithm.v theories/ZArith/ZArith.vo contrib/omega/Omega.vo contrib/omega/Zcomplements.vo contrib/omega/Zpower.vo
contrib/omega/Zcomplements.vo: contrib/omega/Zcomplements.v theories/ZArith/ZArith.vo contrib/omega/Omega.vo theories/Arith/Wf_nat.vo
contrib/omega/Omega.vo: contrib/omega/Omega.v theories/ZArith/ZArith.vo theories/Arith/Minus.vo contrib/omega/omega.cmo contrib/omega/coq_omega.cmo contrib/omega/OmegaSyntax.vo
contrib/omega/OmegaSyntax.vo: contrib/omega/OmegaSyntax.v
contrib/interface/Centaur.vo: contrib/interface/Centaur.v contrib/interface/paths.cmo contrib/interface/name_to_ast.cmo contrib/interface/xlate.cmo contrib/interface/vtp.cmo contrib/interface/translate.cmo contrib/interface/pbp.cmo contrib/interface/dad.cmo contrib/interface/showproof_ct.cmo contrib/interface/showproof.cmo contrib/interface/debug_tac.cmo contrib/interface/history.cmo contrib/interface/centaur.cmo
contrib/interface/AddDad.vo: contrib/interface/AddDad.v
contrib/fourier/Fourier.vo: contrib/fourier/Fourier.v contrib/ring/quote.cmo contrib/ring/ring.cmo contrib/fourier/fourier.cmo contrib/fourier/fourierR.cmo contrib/field/field.cmo contrib/fourier/Fourier_util.vo contrib/field/Field.vo theories/Reals/DiscrR.vo
contrib/fourier/Fourier_util.vo: contrib/fourier/Fourier_util.v theories/Reals/Rbase.vo
contrib/field/Field.vo: contrib/field/Field.v contrib/field/Field_Compl.vo contrib/field/Field_Theory.vo contrib/field/Field_Tactic.vo contrib/field/field.cmo
contrib/field/Field_Theory.vo: contrib/field/Field_Theory.v theories/Arith/Peano_dec.vo contrib/ring/Ring.vo contrib/field/Field_Compl.vo
contrib/field/Field_Tactic.vo: contrib/field/Field_Tactic.v contrib/ring/Ring.vo contrib/field/Field_Compl.vo contrib/field/Field_Theory.vo
contrib/field/Field_Compl.vo: contrib/field/Field_Compl.v
contrib/extraction/test_extraction.vo: contrib/extraction/test_extraction.v
contrib/extraction/Extraction.vo: contrib/extraction/Extraction.v
contrib/correctness/Tuples.vo: contrib/correctness/Tuples.v
contrib/correctness/Sorted.vo: contrib/correctness/Sorted.v contrib/correctness/Arrays.vo contrib/correctness/ArrayPermut.vo contrib/ring/ZArithRing.vo contrib/omega/Omega.vo
contrib/correctness/ProgWf.vo: contrib/correctness/ProgWf.v theories/ZArith/ZArith.vo theories/Arith/Wf_nat.vo
contrib/correctness/Programs_stuff.vo: contrib/correctness/Programs_stuff.v contrib/correctness/Arrays_stuff.vo
contrib/correctness/ProgramsExtraction.vo: contrib/correctness/ProgramsExtraction.v contrib/extraction/Extraction.vo contrib/correctness/Correctness.vo contrib/correctness/pextract.cmo
contrib/correctness/ProgInt.vo: contrib/correctness/ProgInt.v theories/ZArith/ZArith.vo theories/ZArith/ZArith_dec.vo
contrib/correctness/ProgBool.vo: contrib/correctness/ProgBool.v theories/Arith/Compare_dec.vo theories/Arith/Peano_dec.vo theories/ZArith/ZArith.vo theories/Bool/Sumbool.vo
contrib/correctness/preuves.vo: contrib/correctness/preuves.v contrib/correctness/Correctness.vo contrib/omega/Omega.vo contrib/correctness/Exchange.vo contrib/correctness/ArrayPermut.vo
contrib/correctness/Exchange.vo: contrib/correctness/Exchange.v contrib/correctness/ProgInt.vo contrib/correctness/Arrays.vo
contrib/correctness/Correctness.vo: contrib/correctness/Correctness.v tactics/Refine.vo contrib/correctness/Tuples.vo contrib/correctness/ProgInt.vo contrib/correctness/ProgBool.vo contrib/correctness/ProgWf.vo contrib/correctness/Arrays.vo
contrib/correctness/Arrays.vo: contrib/correctness/Arrays.v contrib/correctness/ProgInt.vo
contrib/correctness/Arrays_stuff.vo: contrib/correctness/Arrays_stuff.v contrib/correctness/Exchange.vo contrib/correctness/ArrayPermut.vo contrib/correctness/Sorted.vo
contrib/correctness/ArrayPermut.vo: contrib/correctness/ArrayPermut.v contrib/correctness/ProgInt.vo contrib/correctness/Arrays.vo contrib/correctness/Exchange.vo contrib/omega/Omega.vo
tactics/Tauto.vo: tactics/Tauto.v
tactics/Refine.vo: tactics/Refine.v
tactics/Inv.vo: tactics/Inv.v tactics/Equality.vo
tactics/Equality.vo: tactics/Equality.v
tactics/EqDecide.vo: tactics/EqDecide.v
tactics/EAuto.vo: tactics/EAuto.v
tactics/AutoRewrite.vo: tactics/AutoRewrite.v
syntax/PPTactic.vo: syntax/PPTactic.v
syntax/PPConstr.vo: syntax/PPConstr.v
syntax/PPCases.vo: syntax/PPCases.v
syntax/MakeBare.vo: syntax/MakeBare.v
states/MakeInitial.vo: states/MakeInitial.v theories/Init/Prelude.vo theories/Init/Logic_Type.vo theories/Init/Logic_TypeSyntax.vo tactics/Equality.vo test-suite/success/Tauto.vo tactics/Inv.vo tactics/EAuto.vo tactics/AutoRewrite.vo tactics/Refine.vo tactics/EqDecide.vo contrib/extraction/Extraction.vo
