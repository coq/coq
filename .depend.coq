theories/FSets/OrderedType.vo: theories/FSets/OrderedType.v theories/Lists/SetoidList.vo
theories/FSets/OrderedTypeEx.vo: theories/FSets/OrderedTypeEx.v theories/FSets/OrderedType.vo theories/ZArith/ZArith.vo contrib/omega/Omega.vo theories/NArith/NArith.vo theories/NArith/Ndec.vo theories/Arith/Compare_dec.vo
theories/FSets/OrderedTypeAlt.vo: theories/FSets/OrderedTypeAlt.v theories/FSets/OrderedType.vo
theories/FSets/FSetInterface.vo: theories/FSets/FSetInterface.v theories/Bool/Bool.vo theories/FSets/OrderedType.vo
theories/FSets/FSetList.vo: theories/FSets/FSetList.v theories/FSets/FSetInterface.vo
theories/FSets/FSetBridge.vo: theories/FSets/FSetBridge.v theories/FSets/FSetInterface.vo
theories/FSets/FSetFacts.vo: theories/FSets/FSetFacts.v theories/FSets/FSetInterface.vo
theories/FSets/FSetProperties.vo: theories/FSets/FSetProperties.v theories/FSets/FSetInterface.vo theories/FSets/FSetFacts.vo
theories/FSets/FSetEqProperties.vo: theories/FSets/FSetEqProperties.v theories/FSets/FSetProperties.vo theories/Bool/Zerob.vo theories/Bool/Sumbool.vo contrib/omega/Omega.vo
theories/FSets/FSets.vo: theories/FSets/FSets.v theories/FSets/OrderedType.vo theories/FSets/OrderedTypeEx.vo theories/FSets/OrderedTypeAlt.vo theories/FSets/FSetInterface.vo theories/FSets/FSetBridge.vo theories/FSets/FSetProperties.vo theories/FSets/FSetEqProperties.vo theories/FSets/FSetList.vo
theories/FSets/FSetWeakProperties.vo: theories/FSets/FSetWeakProperties.v theories/FSets/FSetWeakInterface.vo theories/FSets/FSetWeakFacts.vo
theories/FSets/FSetWeakInterface.vo: theories/FSets/FSetWeakInterface.v theories/Bool/Bool.vo theories/Logic/DecidableType.vo
theories/FSets/FSetWeakList.vo: theories/FSets/FSetWeakList.v theories/FSets/FSetWeakInterface.vo
theories/FSets/FSetWeakFacts.vo: theories/FSets/FSetWeakFacts.v theories/FSets/FSetWeakInterface.vo
theories/FSets/FSetWeak.vo: theories/FSets/FSetWeak.v theories/Logic/DecidableType.vo theories/Logic/DecidableTypeEx.vo theories/FSets/FSetWeakInterface.vo theories/FSets/FSetWeakFacts.vo theories/FSets/FSetWeakProperties.vo theories/FSets/FSetWeakList.vo
theories/FSets/FMapInterface.vo: theories/FSets/FMapInterface.v theories/FSets/FSetInterface.vo
theories/FSets/FMapList.vo: theories/FSets/FMapList.v theories/FSets/FSetInterface.vo theories/FSets/FMapInterface.vo
theories/FSets/FMaps.vo: theories/FSets/FMaps.v theories/FSets/OrderedType.vo theories/FSets/OrderedTypeEx.vo theories/FSets/OrderedTypeAlt.vo theories/FSets/FMapInterface.vo theories/FSets/FMapList.vo theories/FSets/FMapPositive.vo theories/FSets/FMapIntMap.vo theories/FSets/FMapFacts.vo
theories/FSets/FMapFacts.vo: theories/FSets/FMapFacts.v theories/Bool/Bool.vo theories/FSets/OrderedType.vo theories/FSets/FMapInterface.vo
theories/FSets/FMapWeakFacts.vo: theories/FSets/FMapWeakFacts.v theories/Bool/Bool.vo theories/FSets/OrderedType.vo theories/FSets/FMapWeakInterface.vo
theories/FSets/FMapWeakInterface.vo: theories/FSets/FMapWeakInterface.v theories/FSets/FSetInterface.vo theories/FSets/FSetWeakInterface.vo
theories/FSets/FMapWeakList.vo: theories/FSets/FMapWeakList.v theories/FSets/FSetInterface.vo theories/FSets/FSetWeakInterface.vo theories/FSets/FMapWeakInterface.vo
theories/FSets/FMapWeak.vo: theories/FSets/FMapWeak.v theories/Logic/DecidableType.vo theories/Logic/DecidableTypeEx.vo theories/FSets/FMapWeakInterface.vo theories/FSets/FMapWeakList.vo theories/FSets/FMapWeakFacts.vo
theories/FSets/FMapPositive.vo: theories/FSets/FMapPositive.v theories/Bool/Bool.vo theories/ZArith/ZArith.vo theories/FSets/OrderedType.vo theories/FSets/FMapInterface.vo
theories/FSets/FMapIntMap.vo: theories/FSets/FMapIntMap.v theories/Bool/Bool.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/NArith/Nnat.vo theories/IntMap/Allmaps.vo theories/FSets/OrderedType.vo theories/FSets/OrderedTypeEx.vo theories/FSets/FMapInterface.vo theories/FSets/FMapList.vo
theories/FSets/FSetToFiniteSet.vo: theories/FSets/FSetToFiniteSet.v theories/Sets/Ensembles.vo theories/Sets/Finite_sets.vo theories/FSets/FSetInterface.vo theories/FSets/FSetProperties.vo theories/FSets/OrderedTypeEx.vo
theories/FSets/FMapAVL.vo: theories/FSets/FMapAVL.v theories/FSets/FSetInterface.vo theories/FSets/FMapInterface.vo theories/FSets/FMapList.vo theories/ZArith/ZArith.vo theories/ZArith/Int.vo
theories/FSets/FSetAVL.vo: theories/FSets/FSetAVL.v theories/FSets/FSetInterface.vo theories/FSets/FSetList.vo theories/ZArith/ZArith.vo theories/ZArith/Int.vo
theories/Reals/Rdefinitions.vo: theories/Reals/Rdefinitions.v theories/ZArith/ZArith_base.vo
theories/Reals/Rpow_def.vo: theories/Reals/Rpow_def.v theories/Reals/Rdefinitions.vo
theories/Reals/Raxioms.vo: theories/Reals/Raxioms.v theories/ZArith/ZArith_base.vo theories/Reals/Rdefinitions.vo
theories/Reals/RIneq.vo: theories/Reals/RIneq.v theories/Reals/Raxioms.vo theories/Reals/Rpow_def.vo theories/ZArith/Zpower.vo contrib/setoid_ring/ZArithRing.vo contrib/omega/Omega.vo contrib/setoid_ring/RealField.vo
theories/Reals/DiscrR.vo: theories/Reals/DiscrR.v theories/Reals/RIneq.vo contrib/omega/Omega.vo
theories/Reals/Rbase.vo: theories/Reals/Rbase.v theories/Reals/Rdefinitions.vo theories/Reals/Raxioms.vo theories/Reals/RIneq.vo theories/Reals/DiscrR.vo
theories/Reals/LegacyRfield.vo: theories/Reals/LegacyRfield.v theories/Reals/Raxioms.vo contrib/field/LegacyField.vo
theories/Reals/R_Ifp.vo: theories/Reals/R_Ifp.v theories/Reals/Rbase.vo contrib/omega/Omega.vo
theories/Reals/Rpow_def.vo: theories/Reals/Rpow_def.v theories/Reals/Rdefinitions.vo
theories/Reals/Rbasic_fun.vo: theories/Reals/Rbasic_fun.v theories/Reals/Rbase.vo theories/Reals/R_Ifp.vo contrib/fourier/Fourier.vo
theories/Reals/R_sqr.vo: theories/Reals/R_sqr.v theories/Reals/Rbase.vo theories/Reals/Rbasic_fun.vo
theories/Reals/SplitAbsolu.vo: theories/Reals/SplitAbsolu.v theories/Reals/Rbasic_fun.vo
theories/Reals/SplitRmult.vo: theories/Reals/SplitRmult.v theories/Reals/Rbase.vo
theories/Reals/ArithProp.vo: theories/Reals/ArithProp.v theories/Reals/Rbase.vo theories/Reals/Rbasic_fun.vo theories/Arith/Even.vo theories/Arith/Div2.vo contrib/setoid_ring/ArithRing.vo
theories/Reals/Rfunctions.vo: theories/Reals/Rfunctions.v contrib/setoid_ring/ArithRing.vo theories/Reals/Rbase.vo theories/Reals/Rpow_def.vo theories/Reals/R_Ifp.vo theories/Reals/Rbasic_fun.vo theories/Reals/R_sqr.vo theories/Reals/SplitAbsolu.vo theories/Reals/SplitRmult.vo theories/Reals/ArithProp.vo contrib/omega/Omega.vo theories/ZArith/Zpower.vo
theories/Reals/Rseries.vo: theories/Reals/Rseries.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Logic/Classical.vo theories/Arith/Compare.vo
theories/Reals/SeqProp.vo: theories/Reals/SeqProp.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rseries.vo theories/Logic/Classical.vo theories/Arith/Max.vo
theories/Reals/Rcomplete.vo: theories/Reals/Rcomplete.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rseries.vo theories/Reals/SeqProp.vo theories/Arith/Max.vo
theories/Reals/PartSum.vo: theories/Reals/PartSum.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rseries.vo theories/Reals/Rcomplete.vo theories/Arith/Max.vo
theories/Reals/AltSeries.vo: theories/Reals/AltSeries.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rseries.vo theories/Reals/SeqProp.vo theories/Reals/PartSum.vo theories/Arith/Max.vo
theories/Reals/Binomial.vo: theories/Reals/Binomial.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/PartSum.vo
theories/Reals/Rsigma.vo: theories/Reals/Rsigma.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rseries.vo theories/Reals/PartSum.vo
theories/Reals/Rprod.vo: theories/Reals/Rprod.v theories/Arith/Compare.vo theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rseries.vo theories/Reals/PartSum.vo theories/Reals/Binomial.vo
theories/Reals/Cauchy_prod.vo: theories/Reals/Cauchy_prod.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rseries.vo theories/Reals/PartSum.vo
theories/Reals/Alembert.vo: theories/Reals/Alembert.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rseries.vo theories/Reals/SeqProp.vo theories/Reals/PartSum.vo theories/Arith/Max.vo
theories/Reals/SeqSeries.vo: theories/Reals/SeqSeries.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Arith/Max.vo theories/Reals/Rseries.vo theories/Reals/SeqProp.vo theories/Reals/Rcomplete.vo theories/Reals/PartSum.vo theories/Reals/AltSeries.vo theories/Reals/Binomial.vo theories/Reals/Rsigma.vo theories/Reals/Rprod.vo theories/Reals/Cauchy_prod.vo theories/Reals/Alembert.vo
theories/Reals/Rtrigo_fun.vo: theories/Reals/Rtrigo_fun.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo
theories/Reals/Rtrigo_def.vo: theories/Reals/Rtrigo_def.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo_fun.vo theories/Arith/Max.vo
theories/Reals/Rtrigo_alt.vo: theories/Reals/Rtrigo_alt.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo_def.vo
theories/Reals/Cos_rel.vo: theories/Reals/Cos_rel.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo_def.vo
theories/Reals/Cos_plus.vo: theories/Reals/Cos_plus.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo_def.vo theories/Reals/Cos_rel.vo theories/Arith/Max.vo
theories/Reals/Rtrigo.vo: theories/Reals/Rtrigo.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo_fun.vo theories/Reals/Rtrigo_def.vo theories/Reals/Rtrigo_alt.vo theories/Reals/Cos_rel.vo theories/Reals/Cos_plus.vo theories/ZArith/ZArith_base.vo theories/ZArith/Zcomplements.vo theories/Logic/Classical_Prop.vo
theories/Reals/Rlimit.vo: theories/Reals/Rlimit.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Logic/Classical_Prop.vo contrib/fourier/Fourier.vo
theories/Reals/Rderiv.vo: theories/Reals/Rderiv.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rlimit.vo contrib/fourier/Fourier.vo theories/Logic/Classical_Prop.vo theories/Logic/Classical_Pred_Type.vo contrib/omega/Omega.vo
theories/Reals/RList.vo: theories/Reals/RList.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo
theories/Reals/Ranalysis1.vo: theories/Reals/Ranalysis1.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rlimit.vo theories/Reals/Rderiv.vo
theories/Reals/Ranalysis2.vo: theories/Reals/Ranalysis2.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Ranalysis1.vo
theories/Reals/Ranalysis3.vo: theories/Reals/Ranalysis3.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Ranalysis1.vo theories/Reals/Ranalysis2.vo
theories/Reals/Rtopology.vo: theories/Reals/Rtopology.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Ranalysis1.vo theories/Reals/RList.vo theories/Logic/Classical_Prop.vo theories/Logic/Classical_Pred_Type.vo
theories/Reals/MVT.vo: theories/Reals/MVT.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Ranalysis1.vo theories/Reals/Rtopology.vo
theories/Reals/PSeries_reg.vo: theories/Reals/PSeries_reg.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Ranalysis1.vo theories/Arith/Max.vo theories/Arith/Even.vo
theories/Reals/Exp_prop.vo: theories/Reals/Exp_prop.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo.vo theories/Reals/Ranalysis1.vo theories/Reals/PSeries_reg.vo theories/Arith/Div2.vo theories/Arith/Even.vo theories/Arith/Max.vo
theories/Reals/Rtrigo_reg.vo: theories/Reals/Rtrigo_reg.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo.vo theories/Reals/Ranalysis1.vo theories/Reals/PSeries_reg.vo
theories/Reals/Rsqrt_def.vo: theories/Reals/Rsqrt_def.v theories/Bool/Sumbool.vo theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Ranalysis1.vo
theories/Reals/R_sqrt.vo: theories/Reals/R_sqrt.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rsqrt_def.vo
theories/Reals/Rtrigo_calc.vo: theories/Reals/Rtrigo_calc.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo.vo theories/Reals/R_sqrt.vo
theories/Reals/Rgeom.vo: theories/Reals/Rgeom.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo.vo theories/Reals/R_sqrt.vo
theories/Reals/Sqrt_reg.vo: theories/Reals/Sqrt_reg.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Ranalysis1.vo theories/Reals/R_sqrt.vo
theories/Reals/Ranalysis4.vo: theories/Reals/Ranalysis4.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo.vo theories/Reals/Ranalysis1.vo theories/Reals/Ranalysis3.vo theories/Reals/Exp_prop.vo
theories/Reals/Rpower.vo: theories/Reals/Rpower.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo.vo theories/Reals/Ranalysis1.vo theories/Reals/Exp_prop.vo theories/Reals/Rsqrt_def.vo theories/Reals/R_sqrt.vo theories/Reals/MVT.vo theories/Reals/Ranalysis4.vo
theories/Reals/Ranalysis.vo: theories/Reals/Ranalysis.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Rtrigo.vo theories/Reals/SeqSeries.vo theories/Reals/Ranalysis1.vo theories/Reals/Ranalysis2.vo theories/Reals/Ranalysis3.vo theories/Reals/Rtopology.vo theories/Reals/MVT.vo theories/Reals/PSeries_reg.vo theories/Reals/Exp_prop.vo theories/Reals/Rtrigo_reg.vo theories/Reals/Rsqrt_def.vo theories/Reals/R_sqrt.vo theories/Reals/Rtrigo_calc.vo theories/Reals/Rgeom.vo theories/Reals/RList.vo theories/Reals/Sqrt_reg.vo theories/Reals/Ranalysis4.vo theories/Reals/Rpower.vo
theories/Reals/NewtonInt.vo: theories/Reals/NewtonInt.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo.vo theories/Reals/Ranalysis.vo
theories/Reals/RiemannInt_SF.vo: theories/Reals/RiemannInt_SF.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/Ranalysis.vo theories/Logic/Classical_Prop.vo
theories/Reals/RiemannInt.vo: theories/Reals/RiemannInt.v theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Ranalysis.vo theories/Reals/Rbase.vo theories/Reals/RiemannInt_SF.vo theories/Logic/Classical_Prop.vo theories/Logic/Classical_Pred_Type.vo theories/Arith/Max.vo
theories/Reals/Integration.vo: theories/Reals/Integration.v theories/Reals/NewtonInt.vo theories/Reals/RiemannInt_SF.vo theories/Reals/RiemannInt.vo
theories/Reals/Reals.vo: theories/Reals/Reals.v theories/Reals/Rbase.vo theories/Reals/Rfunctions.vo theories/Reals/SeqSeries.vo theories/Reals/Rtrigo.vo theories/Reals/Ranalysis.vo theories/Reals/Integration.vo
theories/Init/Notations.vo: theories/Init/Notations.v
theories/Init/Datatypes.vo: theories/Init/Datatypes.v theories/Init/Notations.vo theories/Init/Logic.vo
theories/Init/Peano.vo: theories/Init/Peano.v theories/Init/Notations.vo theories/Init/Datatypes.vo theories/Init/Logic.vo
theories/Init/Logic.vo: theories/Init/Logic.v theories/Init/Notations.vo
theories/Init/Specif.vo: theories/Init/Specif.v theories/Init/Notations.vo theories/Init/Datatypes.vo theories/Init/Logic.vo
theories/Init/Logic_Type.vo: theories/Init/Logic_Type.v theories/Init/Datatypes.vo theories/Init/Logic.vo
theories/Init/Wf.vo: theories/Init/Wf.v theories/Init/Notations.vo theories/Init/Logic.vo theories/Init/Datatypes.vo
theories/Init/Tactics.vo: theories/Init/Tactics.v theories/Init/Notations.vo theories/Init/Logic.vo
theories/Init/Prelude.vo: theories/Init/Prelude.v theories/Init/Notations.vo theories/Init/Logic.vo theories/Init/Datatypes.vo theories/Init/Specif.vo theories/Init/Peano.vo theories/Init/Wf.vo theories/Init/Tactics.vo
theories/Init/Notations.vo: theories/Init/Notations.v
theories/Init/Datatypes.vo: theories/Init/Datatypes.v theories/Init/Notations.vo theories/Init/Logic.vo
theories/Init/Peano.vo: theories/Init/Peano.v theories/Init/Notations.vo theories/Init/Datatypes.vo theories/Init/Logic.vo
theories/Init/Logic.vo: theories/Init/Logic.v theories/Init/Notations.vo
theories/Init/Specif.vo: theories/Init/Specif.v theories/Init/Notations.vo theories/Init/Datatypes.vo theories/Init/Logic.vo
theories/Init/Logic_Type.vo: theories/Init/Logic_Type.v theories/Init/Datatypes.vo theories/Init/Logic.vo
theories/Init/Wf.vo: theories/Init/Wf.v theories/Init/Notations.vo theories/Init/Logic.vo theories/Init/Datatypes.vo
theories/Init/Tactics.vo: theories/Init/Tactics.v theories/Init/Notations.vo theories/Init/Logic.vo
theories/Init/Prelude.vo: theories/Init/Prelude.v theories/Init/Notations.vo theories/Init/Logic.vo theories/Init/Datatypes.vo theories/Init/Specif.vo theories/Init/Peano.vo theories/Init/Wf.vo theories/Init/Tactics.vo
theories/Logic/Hurkens.vo: theories/Logic/Hurkens.v
theories/Logic/ProofIrrelevance.vo: theories/Logic/ProofIrrelevance.v theories/Logic/ProofIrrelevanceFacts.vo
theories/Logic/Classical.vo: theories/Logic/Classical.v theories/Logic/Classical_Prop.vo theories/Logic/Classical_Pred_Type.vo
theories/Logic/Classical_Type.vo: theories/Logic/Classical_Type.v theories/Logic/Classical_Prop.vo theories/Logic/Classical_Pred_Type.vo
theories/Logic/Classical_Pred_Set.vo: theories/Logic/Classical_Pred_Set.v theories/Logic/Classical_Pred_Type.vo
theories/Logic/Eqdep.vo: theories/Logic/Eqdep.v theories/Logic/EqdepFacts.vo
theories/Logic/Classical_Prop.vo: theories/Logic/Classical_Prop.v theories/Logic/ClassicalFacts.vo theories/Logic/EqdepFacts.vo
theories/Logic/Classical_Pred_Type.vo: theories/Logic/Classical_Pred_Type.v theories/Logic/Classical_Prop.vo
theories/Logic/ClassicalFacts.vo: theories/Logic/ClassicalFacts.v theories/Logic/Hurkens.vo
theories/Logic/ChoiceFacts.vo: theories/Logic/ChoiceFacts.v theories/Arith/Wf_nat.vo theories/Arith/Compare_dec.vo theories/Logic/Decidable.vo theories/Arith/Arith.vo theories/Setoids/Setoid.vo
theories/Logic/Berardi.vo: theories/Logic/Berardi.v
theories/Logic/Eqdep_dec.vo: theories/Logic/Eqdep_dec.v theories/Logic/EqdepFacts.vo
theories/Logic/Decidable.vo: theories/Logic/Decidable.v
theories/Logic/JMeq.vo: theories/Logic/JMeq.v theories/Logic/Eqdep.vo
theories/Logic/ClassicalChoice.vo: theories/Logic/ClassicalChoice.v theories/Logic/ClassicalUniqueChoice.vo theories/Logic/RelationalChoice.vo theories/Logic/ChoiceFacts.vo
theories/Logic/ClassicalDescription.vo: theories/Logic/ClassicalDescription.v theories/Logic/Classical.vo theories/Logic/ChoiceFacts.vo
theories/Logic/RelationalChoice.vo: theories/Logic/RelationalChoice.v
theories/Logic/Diaconescu.vo: theories/Logic/Diaconescu.v theories/Logic/ClassicalFacts.vo theories/Logic/ChoiceFacts.vo theories/Bool/Bool.vo
theories/Logic/EqdepFacts.vo: theories/Logic/EqdepFacts.v
theories/Logic/ProofIrrelevanceFacts.vo: theories/Logic/ProofIrrelevanceFacts.v theories/Logic/EqdepFacts.vo
theories/Logic/ClassicalEpsilon.vo: theories/Logic/ClassicalEpsilon.v theories/Logic/Classical.vo theories/Logic/ChoiceFacts.vo
theories/Logic/ClassicalUniqueChoice.vo: theories/Logic/ClassicalUniqueChoice.v theories/Logic/Classical.vo theories/Setoids/Setoid.vo
theories/Logic/DecidableType.vo: theories/Logic/DecidableType.v theories/Lists/SetoidList.vo
theories/Logic/DecidableTypeEx.vo: theories/Logic/DecidableTypeEx.v theories/Logic/DecidableType.vo theories/FSets/OrderedType.vo theories/FSets/OrderedTypeEx.vo
theories/Logic/ConstructiveEpsilon.vo: theories/Logic/ConstructiveEpsilon.v theories/Arith/Arith.vo
theories/Arith/Arith.vo: theories/Arith/Arith.v theories/Arith/Arith_base.vo contrib/setoid_ring/ArithRing.vo
theories/Arith/Gt.vo: theories/Arith/Gt.v theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Plus.vo
theories/Arith/Between.vo: theories/Arith/Between.v theories/Arith/Le.vo theories/Arith/Lt.vo
theories/Arith/Le.vo: theories/Arith/Le.v
theories/Arith/Compare.vo: theories/Arith/Compare.v theories/Arith/Arith_base.vo theories/Arith/Peano_dec.vo theories/Arith/Compare_dec.vo theories/Arith/Wf_nat.vo theories/Arith/Min.vo
theories/Arith/Lt.vo: theories/Arith/Lt.v theories/Arith/Le.vo
theories/Arith/Compare_dec.vo: theories/Arith/Compare_dec.v theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Gt.vo theories/Logic/Decidable.vo
theories/Arith/Min.vo: theories/Arith/Min.v theories/Arith/Le.vo
theories/Arith/Div2.vo: theories/Arith/Div2.v theories/Arith/Lt.vo theories/Arith/Plus.vo theories/Arith/Compare_dec.vo theories/Arith/Even.vo
theories/Arith/Minus.vo: theories/Arith/Minus.v theories/Arith/Lt.vo theories/Arith/Le.vo
theories/Arith/Mult.vo: theories/Arith/Mult.v theories/Arith/Plus.vo theories/Arith/Minus.vo theories/Arith/Lt.vo theories/Arith/Le.vo
theories/Arith/Even.vo: theories/Arith/Even.v
theories/Arith/EqNat.vo: theories/Arith/EqNat.v
theories/Arith/Peano_dec.vo: theories/Arith/Peano_dec.v theories/Logic/Decidable.vo
theories/Arith/Euclid.vo: theories/Arith/Euclid.v theories/Arith/Mult.vo theories/Arith/Compare_dec.vo theories/Arith/Wf_nat.vo
theories/Arith/Plus.vo: theories/Arith/Plus.v theories/Arith/Le.vo theories/Arith/Lt.vo
theories/Arith/Wf_nat.vo: theories/Arith/Wf_nat.v theories/Arith/Lt.vo
theories/Arith/Max.vo: theories/Arith/Max.v theories/Arith/Arith.vo
theories/Arith/Bool_nat.vo: theories/Arith/Bool_nat.v theories/Arith/Compare_dec.vo theories/Arith/Peano_dec.vo theories/Bool/Sumbool.vo
theories/Arith/Factorial.vo: theories/Arith/Factorial.v theories/Arith/Plus.vo theories/Arith/Mult.vo theories/Arith/Lt.vo
theories/Arith/Arith_base.vo: theories/Arith/Arith_base.v theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Plus.vo theories/Arith/Gt.vo theories/Arith/Minus.vo theories/Arith/Mult.vo theories/Arith/Between.vo theories/Arith/Peano_dec.vo theories/Arith/Compare_dec.vo theories/Arith/Factorial.vo
theories/Bool/Bool.vo: theories/Bool/Bool.v
theories/Bool/IfProp.vo: theories/Bool/IfProp.v theories/Bool/Bool.vo
theories/Bool/Zerob.vo: theories/Bool/Zerob.v theories/Arith/Arith.vo theories/Bool/Bool.vo
theories/Bool/DecBool.vo: theories/Bool/DecBool.v
theories/Bool/Sumbool.vo: theories/Bool/Sumbool.v
theories/Bool/BoolEq.vo: theories/Bool/BoolEq.v theories/Bool/Bool.vo
theories/Bool/Bvector.vo: theories/Bool/Bvector.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo
theories/NArith/BinPos.vo: theories/NArith/BinPos.v
theories/NArith/Pnat.vo: theories/NArith/Pnat.v theories/NArith/BinPos.vo theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Gt.vo theories/Arith/Plus.vo theories/Arith/Mult.vo theories/Arith/Minus.vo
theories/NArith/BinNat.vo: theories/NArith/BinNat.v theories/NArith/BinPos.vo
theories/NArith/NArith.vo: theories/NArith/NArith.v theories/NArith/BinPos.vo theories/NArith/BinNat.vo contrib/setoid_ring/NArithRing.vo
theories/NArith/Nnat.vo: theories/NArith/Nnat.v theories/Arith/Arith_base.vo theories/Arith/Compare_dec.vo theories/Bool/Sumbool.vo theories/Arith/Div2.vo theories/NArith/BinPos.vo theories/NArith/BinNat.vo theories/NArith/Pnat.vo
theories/NArith/Ndigits.vo: theories/NArith/Ndigits.v theories/Bool/Bool.vo theories/Bool/Bvector.vo theories/NArith/BinPos.vo theories/NArith/BinNat.vo
theories/NArith/Ndec.vo: theories/NArith/Ndec.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/NArith/BinPos.vo theories/NArith/BinNat.vo theories/NArith/Pnat.vo theories/NArith/Nnat.vo theories/NArith/Ndigits.vo
theories/NArith/Ndist.vo: theories/NArith/Ndist.v theories/Arith/Arith.vo theories/Arith/Min.vo theories/NArith/BinPos.vo theories/NArith/BinNat.vo theories/NArith/Ndigits.vo
theories/ZArith/BinInt.vo: theories/ZArith/BinInt.v theories/NArith/BinPos.vo theories/NArith/Pnat.vo theories/NArith/BinNat.vo theories/Arith/Plus.vo theories/Arith/Mult.vo
theories/ZArith/Wf_Z.vo: theories/ZArith/Wf_Z.v theories/ZArith/BinInt.vo theories/ZArith/Zcompare.vo theories/ZArith/Zorder.vo theories/ZArith/Znat.vo theories/ZArith/Zmisc.vo theories/Arith/Wf_nat.vo
theories/ZArith/ZArith.vo: theories/ZArith/ZArith.v theories/ZArith/ZArith_base.vo theories/ZArith/Zcomplements.vo theories/ZArith/Zsqrt.vo theories/ZArith/Zpower.vo theories/ZArith/Zdiv.vo theories/ZArith/Zlogarithm.vo
theories/ZArith/ZArith_dec.vo: theories/ZArith/ZArith_dec.v theories/Bool/Sumbool.vo theories/ZArith/BinInt.vo theories/ZArith/Zorder.vo theories/ZArith/Zcompare.vo
theories/ZArith/auxiliary.vo: theories/ZArith/auxiliary.v theories/Arith/Arith_base.vo theories/ZArith/BinInt.vo theories/ZArith/Zorder.vo theories/Logic/Decidable.vo theories/Arith/Peano_dec.vo theories/Arith/Compare_dec.vo
theories/ZArith/Zmisc.vo: theories/ZArith/Zmisc.v theories/ZArith/BinInt.vo theories/ZArith/Zcompare.vo theories/ZArith/Zorder.vo theories/Bool/Bool.vo
theories/ZArith/Zcompare.vo: theories/ZArith/Zcompare.v theories/NArith/BinPos.vo theories/ZArith/BinInt.vo theories/Arith/Lt.vo theories/Arith/Gt.vo theories/Arith/Plus.vo theories/Arith/Mult.vo
theories/ZArith/Znat.vo: theories/ZArith/Znat.v theories/Arith/Arith_base.vo theories/NArith/BinPos.vo theories/ZArith/BinInt.vo theories/ZArith/Zcompare.vo theories/ZArith/Zorder.vo theories/Logic/Decidable.vo theories/Arith/Peano_dec.vo theories/Arith/Compare_dec.vo
theories/ZArith/Zorder.vo: theories/ZArith/Zorder.v theories/NArith/BinPos.vo theories/ZArith/BinInt.vo theories/Arith/Arith_base.vo theories/Logic/Decidable.vo theories/ZArith/Zcompare.vo
theories/ZArith/Zabs.vo: theories/ZArith/Zabs.v theories/Arith/Arith_base.vo theories/NArith/BinPos.vo theories/ZArith/BinInt.vo theories/ZArith/Zorder.vo theories/ZArith/ZArith_dec.vo
theories/ZArith/Zmin.vo: theories/ZArith/Zmin.v theories/Arith/Arith_base.vo theories/ZArith/BinInt.vo theories/ZArith/Zcompare.vo theories/ZArith/Zorder.vo
theories/ZArith/Zmax.vo: theories/ZArith/Zmax.v theories/Arith/Arith_base.vo theories/ZArith/BinInt.vo theories/ZArith/Zcompare.vo theories/ZArith/Zorder.vo
theories/ZArith/Zminmax.vo: theories/ZArith/Zminmax.v theories/ZArith/Zmin.vo theories/ZArith/Zmax.vo theories/ZArith/BinInt.vo theories/ZArith/Zorder.vo
theories/ZArith/Zeven.vo: theories/ZArith/Zeven.v theories/ZArith/BinInt.vo
theories/ZArith/Zhints.vo: theories/ZArith/Zhints.v theories/ZArith/BinInt.vo theories/ZArith/Zorder.vo theories/ZArith/Zmin.vo theories/ZArith/Zabs.vo theories/ZArith/Zcompare.vo theories/ZArith/Znat.vo theories/ZArith/auxiliary.vo theories/ZArith/Zmisc.vo theories/ZArith/Wf_Z.vo
theories/ZArith/Zlogarithm.vo: theories/ZArith/Zlogarithm.v theories/ZArith/ZArith_base.vo contrib/omega/Omega.vo theories/ZArith/Zcomplements.vo theories/ZArith/Zpower.vo
theories/ZArith/Zpower.vo: theories/ZArith/Zpower.v theories/ZArith/ZArith_base.vo theories/ZArith/Zpow_def.vo contrib/omega/Omega.vo theories/ZArith/Zcomplements.vo
theories/ZArith/Zcomplements.vo: theories/ZArith/Zcomplements.v contrib/setoid_ring/ZArithRing.vo theories/ZArith/ZArith_base.vo contrib/omega/Omega.vo theories/Arith/Wf_nat.vo theories/Lists/List.vo
theories/ZArith/Zdiv.vo: theories/ZArith/Zdiv.v theories/ZArith/ZArith_base.vo theories/ZArith/Zbool.vo contrib/omega/Omega.vo contrib/setoid_ring/ZArithRing.vo theories/ZArith/Zcomplements.vo
theories/ZArith/Zsqrt.vo: theories/ZArith/Zsqrt.v contrib/setoid_ring/ZArithRing.vo contrib/omega/Omega.vo theories/ZArith/ZArith_base.vo
theories/ZArith/Zwf.vo: theories/ZArith/Zwf.v theories/ZArith/ZArith_base.vo theories/Arith/Wf_nat.vo contrib/omega/Omega.vo
theories/ZArith/ZArith_base.vo: theories/ZArith/ZArith_base.v theories/NArith/BinPos.vo theories/NArith/BinNat.vo theories/ZArith/BinInt.vo theories/ZArith/Zcompare.vo theories/ZArith/Zorder.vo theories/ZArith/Zeven.vo theories/ZArith/Zmin.vo theories/ZArith/Zmax.vo theories/ZArith/Zminmax.vo theories/ZArith/Zabs.vo theories/ZArith/Znat.vo theories/ZArith/auxiliary.vo theories/ZArith/ZArith_dec.vo theories/ZArith/Zbool.vo theories/ZArith/Zmisc.vo theories/ZArith/Wf_Z.vo theories/ZArith/Zhints.vo
theories/ZArith/Zbool.vo: theories/ZArith/Zbool.v theories/ZArith/BinInt.vo theories/ZArith/Zeven.vo theories/ZArith/Zorder.vo theories/ZArith/Zcompare.vo theories/ZArith/ZArith_dec.vo theories/Bool/Sumbool.vo
theories/ZArith/Zbinary.vo: theories/ZArith/Zbinary.v theories/Bool/Bvector.vo theories/ZArith/ZArith.vo theories/ZArith/Zpower.vo contrib/omega/Omega.vo
theories/ZArith/Znumtheory.vo: theories/ZArith/Znumtheory.v theories/ZArith/ZArith_base.vo contrib/setoid_ring/ZArithRing.vo theories/ZArith/Zcomplements.vo theories/ZArith/Zdiv.vo theories/NArith/Ndigits.vo theories/Arith/Wf_nat.vo
theories/ZArith/Int.vo: theories/ZArith/Int.v theories/ZArith/ZArith.vo contrib/romega/ROmega.vo
theories/ZArith/Zpow_def.vo: theories/ZArith/Zpow_def.v theories/ZArith/ZArith_base.vo contrib/setoid_ring/Ring_theory.vo
theories/Setoids/Setoid.vo: theories/Setoids/Setoid.v theories/Relations/Relation_Definitions.vo
theories/Lists/MonoList.vo: theories/Lists/MonoList.v theories/Arith/Le.vo
theories/Lists/ListSet.vo: theories/Lists/ListSet.v theories/Lists/List.vo
theories/Lists/Streams.vo: theories/Lists/Streams.v
theories/Lists/TheoryList.vo: theories/Lists/TheoryList.v theories/Lists/List.vo theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Minus.vo theories/Bool/DecBool.vo
theories/Lists/List.vo: theories/Lists/List.v theories/Arith/Le.vo theories/Arith/Gt.vo theories/Arith/Minus.vo theories/Arith/Min.vo theories/Bool/Bool.vo theories/Setoids/Setoid.vo
theories/Lists/SetoidList.vo: theories/Lists/SetoidList.v theories/Lists/List.vo theories/Sorting/Sorting.vo theories/Setoids/Setoid.vo
theories/Lists/ListTactics.vo: theories/Lists/ListTactics.v theories/NArith/BinPos.vo theories/Lists/List.vo
theories/Strings/Ascii.vo: theories/Strings/Ascii.v theories/Bool/Bool.vo theories/NArith/BinPos.vo
theories/Strings/String.vo: theories/Strings/String.v theories/Arith/Arith.vo theories/Strings/Ascii.vo
theories/Sets/Classical_sets.vo: theories/Sets/Classical_sets.v theories/Sets/Ensembles.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo
theories/Sets/Permut.vo: theories/Sets/Permut.v
theories/Sets/Constructive_sets.vo: theories/Sets/Constructive_sets.v theories/Sets/Ensembles.vo
theories/Sets/Powerset.vo: theories/Sets/Powerset.v theories/Sets/Ensembles.vo theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Partial_Order.vo theories/Sets/Cpo.vo
theories/Sets/Cpo.vo: theories/Sets/Cpo.v theories/Sets/Ensembles.vo theories/Sets/Relations_1.vo theories/Sets/Partial_Order.vo
theories/Sets/Powerset_Classical_facts.vo: theories/Sets/Powerset_Classical_facts.v theories/Sets/Ensembles.vo theories/Sets/Constructive_sets.vo theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Partial_Order.vo theories/Sets/Cpo.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo
theories/Sets/Ensembles.vo: theories/Sets/Ensembles.v
theories/Sets/Powerset_facts.vo: theories/Sets/Powerset_facts.v theories/Sets/Ensembles.vo theories/Sets/Constructive_sets.vo theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Partial_Order.vo theories/Sets/Cpo.vo theories/Sets/Powerset.vo
theories/Sets/Finite_sets.vo: theories/Sets/Finite_sets.v theories/Sets/Ensembles.vo theories/Sets/Constructive_sets.vo
theories/Sets/Relations_1.vo: theories/Sets/Relations_1.v
theories/Sets/Finite_sets_facts.vo: theories/Sets/Finite_sets_facts.v theories/Sets/Finite_sets.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Sets/Powerset_Classical_facts.vo theories/Arith/Gt.vo theories/Arith/Lt.vo
theories/Sets/Relations_1_facts.vo: theories/Sets/Relations_1_facts.v theories/Sets/Relations_1.vo
theories/Sets/Image.vo: theories/Sets/Image.v theories/Sets/Finite_sets.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Sets/Powerset_Classical_facts.vo theories/Arith/Gt.vo theories/Arith/Lt.vo theories/Arith/Le.vo theories/Sets/Finite_sets_facts.vo
theories/Sets/Relations_2.vo: theories/Sets/Relations_2.v theories/Sets/Relations_1.vo
theories/Sets/Infinite_sets.vo: theories/Sets/Infinite_sets.v theories/Sets/Finite_sets.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Sets/Powerset_Classical_facts.vo theories/Arith/Gt.vo theories/Arith/Lt.vo theories/Arith/Le.vo theories/Sets/Finite_sets_facts.vo theories/Sets/Image.vo
theories/Sets/Relations_2_facts.vo: theories/Sets/Relations_2_facts.v theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Relations_2.vo
theories/Sets/Integers.vo: theories/Sets/Integers.v theories/Sets/Finite_sets.vo theories/Sets/Constructive_sets.vo theories/Logic/Classical_Type.vo theories/Sets/Classical_sets.vo theories/Sets/Powerset.vo theories/Sets/Powerset_facts.vo theories/Sets/Powerset_Classical_facts.vo theories/Arith/Gt.vo theories/Arith/Lt.vo theories/Arith/Le.vo theories/Sets/Finite_sets_facts.vo theories/Sets/Image.vo theories/Sets/Infinite_sets.vo theories/Arith/Compare_dec.vo theories/Sets/Relations_1.vo theories/Sets/Partial_Order.vo theories/Sets/Cpo.vo
theories/Sets/Relations_3.vo: theories/Sets/Relations_3.v theories/Sets/Relations_1.vo theories/Sets/Relations_2.vo
theories/Sets/Multiset.vo: theories/Sets/Multiset.v theories/Sets/Permut.vo theories/Arith/Plus.vo
theories/Sets/Relations_3_facts.vo: theories/Sets/Relations_3_facts.v theories/Sets/Relations_1.vo theories/Sets/Relations_1_facts.vo theories/Sets/Relations_2.vo theories/Sets/Relations_2_facts.vo theories/Sets/Relations_3.vo
theories/Sets/Partial_Order.vo: theories/Sets/Partial_Order.v theories/Sets/Ensembles.vo theories/Sets/Relations_1.vo
theories/Sets/Uniset.vo: theories/Sets/Uniset.v theories/Bool/Bool.vo theories/Sets/Permut.vo
theories/FSets/OrderedType.vo: theories/FSets/OrderedType.v theories/Lists/SetoidList.vo
theories/FSets/OrderedTypeEx.vo: theories/FSets/OrderedTypeEx.v theories/FSets/OrderedType.vo theories/ZArith/ZArith.vo contrib/omega/Omega.vo theories/NArith/NArith.vo theories/NArith/Ndec.vo theories/Arith/Compare_dec.vo
theories/FSets/OrderedTypeAlt.vo: theories/FSets/OrderedTypeAlt.v theories/FSets/OrderedType.vo
theories/FSets/FSetInterface.vo: theories/FSets/FSetInterface.v theories/Bool/Bool.vo theories/FSets/OrderedType.vo
theories/FSets/FSetList.vo: theories/FSets/FSetList.v theories/FSets/FSetInterface.vo
theories/FSets/FSetBridge.vo: theories/FSets/FSetBridge.v theories/FSets/FSetInterface.vo
theories/FSets/FSetFacts.vo: theories/FSets/FSetFacts.v theories/FSets/FSetInterface.vo
theories/FSets/FSetProperties.vo: theories/FSets/FSetProperties.v theories/FSets/FSetInterface.vo theories/FSets/FSetFacts.vo
theories/FSets/FSetEqProperties.vo: theories/FSets/FSetEqProperties.v theories/FSets/FSetProperties.vo theories/Bool/Zerob.vo theories/Bool/Sumbool.vo contrib/omega/Omega.vo
theories/FSets/FSets.vo: theories/FSets/FSets.v theories/FSets/OrderedType.vo theories/FSets/OrderedTypeEx.vo theories/FSets/OrderedTypeAlt.vo theories/FSets/FSetInterface.vo theories/FSets/FSetBridge.vo theories/FSets/FSetProperties.vo theories/FSets/FSetEqProperties.vo theories/FSets/FSetList.vo
theories/FSets/FSetWeakProperties.vo: theories/FSets/FSetWeakProperties.v theories/FSets/FSetWeakInterface.vo theories/FSets/FSetWeakFacts.vo
theories/FSets/FSetWeakInterface.vo: theories/FSets/FSetWeakInterface.v theories/Bool/Bool.vo theories/Logic/DecidableType.vo
theories/FSets/FSetWeakList.vo: theories/FSets/FSetWeakList.v theories/FSets/FSetWeakInterface.vo
theories/FSets/FSetWeakFacts.vo: theories/FSets/FSetWeakFacts.v theories/FSets/FSetWeakInterface.vo
theories/FSets/FSetWeak.vo: theories/FSets/FSetWeak.v theories/Logic/DecidableType.vo theories/Logic/DecidableTypeEx.vo theories/FSets/FSetWeakInterface.vo theories/FSets/FSetWeakFacts.vo theories/FSets/FSetWeakProperties.vo theories/FSets/FSetWeakList.vo
theories/FSets/FMapInterface.vo: theories/FSets/FMapInterface.v theories/FSets/FSetInterface.vo
theories/FSets/FMapList.vo: theories/FSets/FMapList.v theories/FSets/FSetInterface.vo theories/FSets/FMapInterface.vo
theories/FSets/FMaps.vo: theories/FSets/FMaps.v theories/FSets/OrderedType.vo theories/FSets/OrderedTypeEx.vo theories/FSets/OrderedTypeAlt.vo theories/FSets/FMapInterface.vo theories/FSets/FMapList.vo theories/FSets/FMapPositive.vo theories/FSets/FMapIntMap.vo theories/FSets/FMapFacts.vo
theories/FSets/FMapFacts.vo: theories/FSets/FMapFacts.v theories/Bool/Bool.vo theories/FSets/OrderedType.vo theories/FSets/FMapInterface.vo
theories/FSets/FMapWeakFacts.vo: theories/FSets/FMapWeakFacts.v theories/Bool/Bool.vo theories/FSets/OrderedType.vo theories/FSets/FMapWeakInterface.vo
theories/FSets/FMapWeakInterface.vo: theories/FSets/FMapWeakInterface.v theories/FSets/FSetInterface.vo theories/FSets/FSetWeakInterface.vo
theories/FSets/FMapWeakList.vo: theories/FSets/FMapWeakList.v theories/FSets/FSetInterface.vo theories/FSets/FSetWeakInterface.vo theories/FSets/FMapWeakInterface.vo
theories/FSets/FMapWeak.vo: theories/FSets/FMapWeak.v theories/Logic/DecidableType.vo theories/Logic/DecidableTypeEx.vo theories/FSets/FMapWeakInterface.vo theories/FSets/FMapWeakList.vo theories/FSets/FMapWeakFacts.vo
theories/FSets/FMapPositive.vo: theories/FSets/FMapPositive.v theories/Bool/Bool.vo theories/ZArith/ZArith.vo theories/FSets/OrderedType.vo theories/FSets/FMapInterface.vo
theories/FSets/FMapIntMap.vo: theories/FSets/FMapIntMap.v theories/Bool/Bool.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/NArith/Nnat.vo theories/IntMap/Allmaps.vo theories/FSets/OrderedType.vo theories/FSets/OrderedTypeEx.vo theories/FSets/FMapInterface.vo theories/FSets/FMapList.vo
theories/FSets/FSetToFiniteSet.vo: theories/FSets/FSetToFiniteSet.v theories/Sets/Ensembles.vo theories/Sets/Finite_sets.vo theories/FSets/FSetInterface.vo theories/FSets/FSetProperties.vo theories/FSets/OrderedTypeEx.vo
theories/IntMap/Adalloc.vo: theories/IntMap/Adalloc.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/NArith/Nnat.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo
theories/IntMap/Mapcanon.vo: theories/IntMap/Mapcanon.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/IntMap/Map.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo theories/IntMap/Fset.vo theories/Lists/List.vo theories/IntMap/Lsort.vo theories/IntMap/Mapsubset.vo theories/IntMap/Mapcard.vo
theories/IntMap/Mapfold.vo: theories/IntMap/Mapfold.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo theories/IntMap/Lsort.vo theories/IntMap/Mapsubset.vo theories/Lists/List.vo
theories/IntMap/Mapcard.vo: theories/IntMap/Mapcard.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/IntMap/Map.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo theories/IntMap/Fset.vo theories/IntMap/Mapsubset.vo theories/Lists/List.vo theories/IntMap/Lsort.vo theories/Arith/Peano_dec.vo
theories/IntMap/Mapc.vo: theories/IntMap/Mapc.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/NArith/NArith.vo theories/IntMap/Map.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Fset.vo theories/IntMap/Mapiter.vo theories/IntMap/Mapsubset.vo theories/Lists/List.vo theories/IntMap/Lsort.vo theories/IntMap/Mapcard.vo theories/IntMap/Mapcanon.vo
theories/IntMap/Allmaps.vo: theories/IntMap/Allmaps.v theories/IntMap/Map.vo theories/IntMap/Fset.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo theories/IntMap/Mapsubset.vo theories/IntMap/Lsort.vo theories/IntMap/Mapfold.vo theories/IntMap/Mapcard.vo theories/IntMap/Mapcanon.vo theories/IntMap/Mapc.vo theories/IntMap/Maplists.vo theories/IntMap/Adalloc.vo
theories/IntMap/Mapiter.vo: theories/IntMap/Mapiter.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/IntMap/Map.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Fset.vo theories/Lists/List.vo
theories/IntMap/Fset.vo: theories/IntMap/Fset.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/IntMap/Map.vo
theories/IntMap/Maplists.vo: theories/IntMap/Maplists.v theories/NArith/BinNat.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapsubset.vo theories/IntMap/Mapcard.vo theories/IntMap/Mapcanon.vo theories/IntMap/Mapc.vo theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Lists/List.vo theories/Arith/Arith.vo theories/IntMap/Mapiter.vo theories/IntMap/Mapfold.vo
theories/IntMap/Lsort.vo: theories/IntMap/Lsort.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/IntMap/Map.vo theories/Lists/List.vo theories/IntMap/Mapiter.vo
theories/IntMap/Mapsubset.vo: theories/IntMap/Mapsubset.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/Arith/Arith.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo theories/IntMap/Mapaxioms.vo theories/IntMap/Mapiter.vo
theories/IntMap/Mapaxioms.vo: theories/IntMap/Mapaxioms.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo theories/IntMap/Map.vo theories/IntMap/Fset.vo
theories/IntMap/Map.vo: theories/IntMap/Map.v theories/Bool/Bool.vo theories/Bool/Sumbool.vo theories/NArith/NArith.vo theories/NArith/Ndigits.vo theories/NArith/Ndec.vo
theories/Relations/Newman.vo: theories/Relations/Newman.v theories/Relations/Rstar.vo
theories/Relations/Operators_Properties.vo: theories/Relations/Operators_Properties.v theories/Relations/Relation_Definitions.vo theories/Relations/Relation_Operators.vo
theories/Relations/Relation_Definitions.vo: theories/Relations/Relation_Definitions.v
theories/Relations/Relation_Operators.vo: theories/Relations/Relation_Operators.v theories/Relations/Relation_Definitions.vo theories/Lists/List.vo
theories/Relations/Relations.vo: theories/Relations/Relations.v theories/Relations/Relation_Definitions.vo theories/Relations/Relation_Operators.vo theories/Relations/Operators_Properties.vo
theories/Relations/Rstar.vo: theories/Relations/Rstar.v
theories/Wellfounded/Disjoint_Union.vo: theories/Wellfounded/Disjoint_Union.v theories/Relations/Relation_Operators.vo
theories/Wellfounded/Inclusion.vo: theories/Wellfounded/Inclusion.v theories/Relations/Relation_Definitions.vo
theories/Wellfounded/Inverse_Image.vo: theories/Wellfounded/Inverse_Image.v
theories/Wellfounded/Lexicographic_Exponentiation.vo: theories/Wellfounded/Lexicographic_Exponentiation.v theories/Logic/Eqdep.vo theories/Lists/List.vo theories/Relations/Relation_Operators.vo theories/Wellfounded/Transitive_Closure.vo
theories/Wellfounded/Transitive_Closure.vo: theories/Wellfounded/Transitive_Closure.v theories/Relations/Relation_Definitions.vo theories/Relations/Relation_Operators.vo
theories/Wellfounded/Union.vo: theories/Wellfounded/Union.v theories/Relations/Relation_Operators.vo theories/Relations/Relation_Definitions.vo theories/Wellfounded/Transitive_Closure.vo
theories/Wellfounded/Wellfounded.vo: theories/Wellfounded/Wellfounded.v theories/Wellfounded/Disjoint_Union.vo theories/Wellfounded/Inclusion.vo theories/Wellfounded/Inverse_Image.vo theories/Wellfounded/Lexicographic_Exponentiation.vo theories/Wellfounded/Lexicographic_Product.vo theories/Wellfounded/Transitive_Closure.vo theories/Wellfounded/Union.vo theories/Wellfounded/Well_Ordering.vo
theories/Wellfounded/Well_Ordering.vo: theories/Wellfounded/Well_Ordering.v theories/Logic/Eqdep.vo
theories/Wellfounded/Lexicographic_Product.vo: theories/Wellfounded/Lexicographic_Product.v theories/Logic/Eqdep.vo theories/Relations/Relation_Operators.vo theories/Wellfounded/Transitive_Closure.vo
theories/Reals/Rdefinitions.vo: theories/Reals/Rdefinitions.v theories/ZArith/ZArith_base.vo
theories/Reals/Rpow_def.vo: theories/Reals/Rpow_def.v theories/Reals/Rdefinitions.vo
theories/Reals/Raxioms.vo: theories/Reals/Raxioms.v theories/ZArith/ZArith_base.vo theories/Reals/Rdefinitions.vo
theories/Reals/RIneq.vo: theories/Reals/RIneq.v theories/Reals/Raxioms.vo theories/Reals/Rpow_def.vo theories/ZArith/Zpower.vo contrib/setoid_ring/ZArithRing.vo contrib/omega/Omega.vo contrib/setoid_ring/RealField.vo
theories/Reals/DiscrR.vo: theories/Reals/DiscrR.v theories/Reals/RIneq.vo contrib/omega/Omega.vo
theories/Reals/Rbase.vo: theories/Reals/Rbase.v theories/Reals/Rdefinitions.vo theories/Reals/Raxioms.vo theories/Reals/RIneq.vo theories/Reals/DiscrR.vo
theories/Reals/LegacyRfield.vo: theories/Reals/LegacyRfield.v theories/Reals/Raxioms.vo contrib/field/LegacyField.vo
theories/Sorting/Heap.vo: theories/Sorting/Heap.v theories/Lists/List.vo theories/Sets/Multiset.vo theories/Sorting/Permutation.vo theories/Relations/Relations.vo theories/Sorting/Sorting.vo
theories/Sorting/Permutation.vo: theories/Sorting/Permutation.v theories/Relations/Relations.vo theories/Lists/List.vo theories/Sets/Multiset.vo theories/Arith/Arith.vo
theories/Sorting/Sorting.vo: theories/Sorting/Sorting.v theories/Lists/List.vo theories/Sets/Multiset.vo theories/Sorting/Permutation.vo theories/Relations/Relations.vo
theories/Sorting/PermutSetoid.vo: theories/Sorting/PermutSetoid.v contrib/omega/Omega.vo theories/Relations/Relations.vo theories/Lists/List.vo theories/Sets/Multiset.vo theories/Sorting/Permutation.vo theories/Lists/SetoidList.vo
theories/Sorting/PermutEq.vo: theories/Sorting/PermutEq.v contrib/omega/Omega.vo theories/Relations/Relations.vo theories/Setoids/Setoid.vo theories/Lists/List.vo theories/Sets/Multiset.vo theories/Sorting/Permutation.vo
theories/QArith/QArith_base.vo: theories/QArith/QArith_base.v theories/ZArith/ZArith.vo contrib/setoid_ring/ZArithRing.vo theories/Setoids/Setoid.vo
theories/QArith/Qreduction.vo: theories/QArith/Qreduction.v theories/QArith/QArith_base.vo theories/ZArith/Znumtheory.vo
theories/QArith/Qring.vo: theories/QArith/Qring.v contrib/setoid_ring/Ring.vo theories/QArith/QArith_base.vo
theories/QArith/Qreals.vo: theories/QArith/Qreals.v theories/Reals/Rbase.vo theories/QArith/QArith_base.vo
theories/QArith/QArith.vo: theories/QArith/QArith.v theories/QArith/QArith_base.vo theories/QArith/Qring.vo theories/QArith/Qreduction.vo
theories/QArith/Qcanon.vo: theories/QArith/Qcanon.v contrib/setoid_ring/Field.vo theories/QArith/QArith.vo theories/ZArith/Znumtheory.vo theories/Logic/Eqdep_dec.vo
contrib/omega/OmegaLemmas.vo: contrib/omega/OmegaLemmas.v theories/ZArith/ZArith_base.vo
contrib/omega/Omega.vo: contrib/omega/Omega.v theories/ZArith/ZArith_base.vo contrib/omega/OmegaLemmas.vo theories/ZArith/Zhints.vo
contrib/romega/ReflOmegaCore.vo: contrib/romega/ReflOmegaCore.v theories/Arith/Arith.vo theories/Lists/List.vo theories/Bool/Bool.vo theories/ZArith/ZArith_base.vo contrib/omega/OmegaLemmas.vo theories/Logic/Decidable.vo
contrib/romega/ROmega.vo: contrib/romega/ROmega.v contrib/romega/ReflOmegaCore.vo
contrib/ring/LegacyArithRing.vo: contrib/ring/LegacyArithRing.v theories/Bool/Bool.vo contrib/ring/LegacyRing.vo theories/Arith/Arith.vo theories/Logic/Eqdep_dec.vo
contrib/ring/Ring_normalize.vo: contrib/ring/Ring_normalize.v contrib/ring/LegacyRing_theory.vo contrib/ring/Quote.vo
contrib/ring/LegacyRing_theory.vo: contrib/ring/LegacyRing_theory.v theories/Bool/Bool.vo
contrib/ring/LegacyRing.vo: contrib/ring/LegacyRing.v theories/Bool/Bool.vo contrib/ring/LegacyRing_theory.vo contrib/ring/Quote.vo contrib/ring/Ring_normalize.vo contrib/ring/Ring_abstract.vo
contrib/ring/LegacyNArithRing.vo: contrib/ring/LegacyNArithRing.v theories/Bool/Bool.vo contrib/ring/LegacyRing.vo theories/ZArith/ZArith_base.vo theories/NArith/NArith.vo theories/Logic/Eqdep_dec.vo
contrib/ring/LegacyZArithRing.vo: contrib/ring/LegacyZArithRing.v contrib/ring/LegacyArithRing.vo theories/ZArith/ZArith_base.vo theories/Logic/Eqdep_dec.vo contrib/ring/LegacyRing.vo
contrib/ring/Ring_abstract.vo: contrib/ring/Ring_abstract.v contrib/ring/LegacyRing_theory.vo contrib/ring/Quote.vo contrib/ring/Ring_normalize.vo
contrib/ring/Quote.vo: contrib/ring/Quote.v
contrib/ring/Setoid_ring_normalize.vo: contrib/ring/Setoid_ring_normalize.v contrib/ring/Setoid_ring_theory.vo contrib/ring/Quote.vo
contrib/ring/Setoid_ring.vo: contrib/ring/Setoid_ring.v contrib/ring/Setoid_ring_theory.vo contrib/ring/Quote.vo contrib/ring/Setoid_ring_normalize.vo
contrib/ring/Setoid_ring_theory.vo: contrib/ring/Setoid_ring_theory.v theories/Bool/Bool.vo theories/Setoids/Setoid.vo
contrib/field/LegacyField_Compl.vo: contrib/field/LegacyField_Compl.v theories/Lists/List.vo
contrib/field/LegacyField_Theory.vo: contrib/field/LegacyField_Theory.v theories/Lists/List.vo theories/Arith/Peano_dec.vo contrib/ring/LegacyRing.vo contrib/field/LegacyField_Compl.vo
contrib/field/LegacyField_Tactic.vo: contrib/field/LegacyField_Tactic.v theories/Lists/List.vo contrib/ring/LegacyRing.vo contrib/field/LegacyField_Compl.vo contrib/field/LegacyField_Theory.vo
contrib/field/LegacyField.vo: contrib/field/LegacyField.v contrib/field/LegacyField_Compl.vo contrib/field/LegacyField_Theory.vo contrib/field/LegacyField_Tactic.vo
contrib/fourier/Fourier_util.vo: contrib/fourier/Fourier_util.v theories/Reals/Rbase.vo
contrib/fourier/Fourier.vo: contrib/fourier/Fourier.v contrib/ring/quote.cmo contrib/ring/ring.cmo contrib/fourier/fourier.cmo contrib/fourier/fourierR.cmo contrib/field/field.cmo contrib/fourier/Fourier_util.vo contrib/field/LegacyField.vo theories/Reals/DiscrR.vo
contrib/subtac/SubtacTactics.vo: contrib/subtac/SubtacTactics.v theories/Logic/Eqdep.vo
contrib/subtac/Heq.vo: contrib/subtac/Heq.v theories/Logic/JMeq.vo
contrib/subtac/Utils.vo: contrib/subtac/Utils.v contrib/subtac/SubtacTactics.vo theories/Bool/Sumbool.vo theories/Logic/ProofIrrelevance.vo contrib/subtac/Heq.vo
contrib/subtac/FixSub.vo: contrib/subtac/FixSub.v theories/Init/Wf.vo contrib/subtac/Utils.vo theories/Arith/Wf_nat.vo theories/Arith/Lt.vo
contrib/subtac/Subtac.vo: contrib/subtac/Subtac.v contrib/subtac/Utils.vo contrib/subtac/FixSub.vo
contrib/subtac/FunctionalExtensionality.vo: contrib/subtac/FunctionalExtensionality.v contrib/subtac/Utils.vo contrib/subtac/FixSub.vo
contrib/rtauto/Bintree.vo: contrib/rtauto/Bintree.v theories/Lists/List.vo theories/NArith/BinPos.vo
contrib/rtauto/Rtauto.vo: contrib/rtauto/Rtauto.v theories/Lists/List.vo contrib/rtauto/Bintree.vo theories/Bool/Bool.vo theories/NArith/BinPos.vo
contrib/recdef/Recdef.vo: contrib/recdef/Recdef.v theories/Arith/Compare_dec.vo theories/Arith/Wf_nat.vo
contrib/setoid_ring/BinList.vo: contrib/setoid_ring/BinList.v theories/NArith/BinPos.vo theories/Lists/List.vo theories/Lists/ListTactics.vo
contrib/setoid_ring/Ring_theory.vo: contrib/setoid_ring/Ring_theory.v theories/Setoids/Setoid.vo theories/NArith/BinPos.vo theories/NArith/BinNat.vo
contrib/setoid_ring/Ring_polynom.vo: contrib/setoid_ring/Ring_polynom.v theories/Setoids/Setoid.vo contrib/setoid_ring/BinList.vo theories/NArith/BinPos.vo theories/NArith/BinNat.vo theories/ZArith/BinInt.vo contrib/setoid_ring/Ring_theory.vo
contrib/setoid_ring/Ring_tac.vo: contrib/setoid_ring/Ring_tac.v theories/Setoids/Setoid.vo theories/NArith/BinPos.vo contrib/setoid_ring/Ring_polynom.vo contrib/setoid_ring/BinList.vo contrib/setoid_ring/InitialRing.vo contrib/setoid_ring/newring.cmo
contrib/setoid_ring/Ring_base.vo: contrib/setoid_ring/Ring_base.v contrib/setoid_ring/newring.cmo contrib/setoid_ring/Ring_theory.vo contrib/setoid_ring/Ring_tac.vo contrib/setoid_ring/InitialRing.vo
contrib/setoid_ring/InitialRing.vo: contrib/setoid_ring/InitialRing.v theories/ZArith/ZArith_base.vo theories/ZArith/Zpow_def.vo theories/ZArith/BinInt.vo theories/NArith/BinNat.vo theories/Setoids/Setoid.vo contrib/setoid_ring/Ring_theory.vo contrib/setoid_ring/Ring_polynom.vo
contrib/setoid_ring/Ring_equiv.vo: contrib/setoid_ring/Ring_equiv.v contrib/ring/Setoid_ring_theory.vo contrib/ring/LegacyRing_theory.vo contrib/setoid_ring/Ring_theory.vo
contrib/setoid_ring/Ring.vo: contrib/setoid_ring/Ring.v theories/Bool/Bool.vo contrib/setoid_ring/Ring_theory.vo contrib/setoid_ring/Ring_base.vo contrib/setoid_ring/InitialRing.vo contrib/setoid_ring/Ring_tac.vo
contrib/setoid_ring/ArithRing.vo: contrib/setoid_ring/ArithRing.v theories/Arith/Mult.vo theories/NArith/BinNat.vo theories/NArith/Nnat.vo contrib/setoid_ring/Ring.vo
contrib/setoid_ring/NArithRing.vo: contrib/setoid_ring/NArithRing.v contrib/setoid_ring/Ring.vo theories/NArith/BinPos.vo theories/NArith/BinNat.vo
contrib/setoid_ring/ZArithRing.vo: contrib/setoid_ring/ZArithRing.v contrib/setoid_ring/Ring.vo theories/ZArith/ZArith_base.vo theories/ZArith/Zpow_def.vo
contrib/setoid_ring/Field_theory.vo: contrib/setoid_ring/Field_theory.v contrib/setoid_ring/Ring.vo theories/ZArith/ZArith_base.vo
contrib/setoid_ring/Field_tac.vo: contrib/setoid_ring/Field_tac.v contrib/setoid_ring/Ring_tac.vo contrib/setoid_ring/BinList.vo contrib/setoid_ring/Ring_polynom.vo contrib/setoid_ring/InitialRing.vo contrib/setoid_ring/Field_theory.vo
contrib/setoid_ring/Field.vo: contrib/setoid_ring/Field.v contrib/setoid_ring/Field_theory.vo contrib/setoid_ring/Field_tac.vo
contrib/setoid_ring/RealField.vo: contrib/setoid_ring/RealField.v theories/NArith/Nnat.vo contrib/setoid_ring/ArithRing.vo contrib/setoid_ring/Ring.vo contrib/setoid_ring/Field.vo theories/Reals/Rdefinitions.vo theories/Reals/Rpow_def.vo theories/Reals/Raxioms.vo
