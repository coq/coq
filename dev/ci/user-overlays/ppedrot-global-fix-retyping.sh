# Validation overlays for the global-fix retyping branch.
# mathcomp: 2f70ce6f Adapt divisor membership rewrites to folded fixpoints
# fourcolor: b17cfa1 Adapt membership rewrite to folded fixpoints
# vst: b85d3027f Adapt funspec_sub rewrite to folded fixpoints
# jasmin: 995366f24 Avoid setoid rewriting through folded pointwise_lifting
# fiat_crypto_legacy: 3cc688e65 Make Var parameters explicit with folded interp_flat_type
overlay mathcomp https://github.com/olympichek/math-comp ppedrot-global-fix-retyping-master 22272 ppedrot-global-fix-retyping-master
overlay fourcolor https://github.com/olympichek/fourcolor ppedrot-global-fix-retyping-master 22272 ppedrot-global-fix-retyping-master
overlay vst https://github.com/olympichek/VST ppedrot-global-fix-retyping-master 22272 ppedrot-global-fix-retyping-master
overlay jasmin https://github.com/olympichek/jasmin ppedrot-global-fix-retyping-master 22272 ppedrot-global-fix-retyping-master
overlay fiat_crypto_legacy https://github.com/olympichek/fiat-crypto ppedrot-global-fix-retyping-master 22272 ppedrot-global-fix-retyping-master
