#!/usr/bin/env bash

# This is the basic overlay set for repositories in the CI.

# Maybe we should just use Ruby to have real objects...

# : "${foo:=bar}" sets foo to "bar" if it is unset or null

########################################################################
# MathComp
########################################################################

# Picking:
#
# Before picking this was on 8187ed3b12da2c164f1fc90c634b4330b796ab44
# = Nov 29 2019 master
#   "Return of PR #226: adds relevant theorems when fcycle f (orbit f x) a…"
# - The tag mathcomp-1.10.0 contains only one further editorial commit
#
# There are no Coq version specific tags or branches
#
# The latest tag is mathcomp-1.10.0 from Nov 29 2019
# - This tag works with Coq 8.11 and it is not older than 6 months.
#
# => Use tag mathcomp-1.10.0

: "${mathcomp_CI_REF:=mathcomp-1.10.0}"
: "${mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp}"
: "${mathcomp_CI_ARCHIVEURL:=${mathcomp_CI_GITURL}/archive}"

: "${fourcolor_CI_REF:=4f993514270100bbc7f635bfea33e7e7138adb00}"
: "${fourcolor_CI_GITURL:=https://github.com/math-comp/fourcolor}"
: "${fourcolor_CI_ARCHIVEURL:=${fourcolor_CI_GITURL}/archive}"

: "${oddorder_CI_REF:=4ff7841213b20f1f55c1597804c7986363f57abd}"
: "${oddorder_CI_GITURL:=https://github.com/math-comp/odd-order}"
: "${oddorder_CI_ARCHIVEURL:=${oddorder_CI_GITURL}/archive}"

########################################################################
# UniMath
########################################################################
: "${unimath_CI_REF:=b2eb12b65adeffe8342ca85df135eae87558feb3}"
: "${unimath_CI_GITURL:=https://github.com/UniMath/UniMath}"
: "${unimath_CI_ARCHIVEURL:=${unimath_CI_GITURL}/archive}"

########################################################################
# Unicoq + Mtac2
########################################################################

# Picking:
#
# Before picking this was on c33e66c8f2924449c7b98aab108d97b5ee105bab
# = Nov 4 2019 master
#   "Merge pull request #28 from validsdp/primitive-floats"
# - This commit seems to be required for 8.11 since primitive floats are included in 8.11
#
# There are no 8.11 specific tags or branches
# - there are 8.10 tags and branches => request tag
#
# The latest 8.10 tag v1.3.2-8.10
# - has just 5 commit from Jan 2 2020 since Mar 15 2019
# - does not include a port of the commit used before picking
#   => looks old
#
# The commits on master beyond c33e66c look like adoptions to changes not in 8.11
#
# => Continue to use c33e66c8f2924449c7b98aab108d97b5ee105bab from Nov 4 2019
# => Ask upstream to tag this as 8.11.0

: "${unicoq_CI_REF:=c33e66c8f2924449c7b98aab108d97b5ee105bab}"
: "${unicoq_CI_GITURL:=https://github.com/unicoq/unicoq}"
: "${unicoq_CI_ARCHIVEURL:=${unicoq_CI_GITURL}/archive}"

# Picking:
#
# Before picking this was on master-8.11
# = (as of Jan 13 2020)
#   Nov 4 2019 006dc6966348c54da212d015a61773c2b2a5e921
#   "Force Coq#8.11 branch in CI."
# - This is the latest commit on master-8.11 as of Jan 13 2020
#
# => Choose latest commit on master-8.11
# => Ask upstream to tag this as 8.11.0

: "${mtac2_CI_REF:=006dc6966348c54da212d015a61773c2b2a5e921}"
: "${mtac2_CI_GITURL:=https://github.com/Mtac2/Mtac2}"
: "${mtac2_CI_ARCHIVEURL:=${mtac2_CI_GITURL}/archive}"

########################################################################
# Mathclasses + Corn
########################################################################
: "${math_classes_CI_REF:=3fceaab6b3128e2bfca5546390905c47442c4908}"
: "${math_classes_CI_GITURL:=https://github.com/coq-community/math-classes}"
: "${math_classes_CI_ARCHIVEURL:=${math_classes_CI_GITURL}/archive}"

: "${Corn_CI_REF:=3320b2d138ffe5a47892e695fedf70e09f85a0fa}"
: "${Corn_CI_GITURL:=https://github.com/coq-community/corn}"
: "${Corn_CI_ARCHIVEURL:=${Corn_CI_GITURL}/archive}"

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
: "${stdpp_CI_GITURL:=https://gitlab.mpi-sws.org/iris/stdpp}"
: "${stdpp_CI_ARCHIVEURL:=${stdpp_CI_GITURL}/-/archive}"

: "${Iris_CI_GITURL:=https://gitlab.mpi-sws.org/iris/iris}"
: "${Iris_CI_ARCHIVEURL:=${Iris_CI_GITURL}/-/archive}"

: "${lambdaRust_CI_REF:=c4a08f333e127c8d8af83c608cf8bcb6d01b7871}"
: "${lambdaRust_CI_GITURL:=https://gitlab.mpi-sws.org/iris/lambda-rust}"
: "${lambdaRust_CI_ARCHIVEURL:=${lambdaRust_CI_GITURL}/-/archive}"

########################################################################
# HoTT
########################################################################
: "${HoTT_CI_REF:=35d9de1f587117cafebf7d7b1851bb177f173783}"
: "${HoTT_CI_GITURL:=https://github.com/HoTT/HoTT}"
: "${HoTT_CI_ARCHIVEURL:=${HoTT_CI_GITURL}/archive}"

########################################################################
# CoqHammer
########################################################################
: "${coqhammer_CI_REF:=00725b6ddedd44a08459d96173513a62bdae58e1}"
: "${coqhammer_CI_GITURL:=https://github.com/lukaszcz/coqhammer}"
: "${coqhammer_CI_ARCHIVEURL:=${coqhammer_CI_GITURL}/archive}"

########################################################################
# GeoCoq
########################################################################
: "${GeoCoq_CI_REF:=f5fa21da6199d871ee6d900514f6a6fc740f0a2d}"
: "${GeoCoq_CI_GITURL:=https://github.com/GeoCoq/GeoCoq}"
: "${GeoCoq_CI_ARCHIVEURL:=${GeoCoq_CI_GITURL}/archive}"

########################################################################
# Flocq
########################################################################

# Picking
#
# Before picking this was on 7076cd30f4409b72b7bf852bf6a935eb60ca29b4
# = Nov 19 2019 master
#   "Use standard macros for checking versions."
#
# There are no Coq version specific tags or branches
#
# The latest tag is flocq-3.2.0 from July 17 2019
# - This tag works with Coq 8.11 and it is not older than 6 months.
#
# => Use tag flocq-3.2.0
#
# The linked commit is 3.2.0 plus a patch for Gappa

: "${Flocq_CI_REF:=66482a0775e39770dde8bebc4c896d8d47980e1a}"
: "${Flocq_CI_GITURL:=https://github.com/MSoegtropIMC/flocq}"
: "${Flocq_CI_ARCHIVEURL:=${Flocq_CI_GITURL}/archive}"

# Original source is
# : "${Flocq_CI_GITURL:=https://gitlab.inria.fr/flocq/flocq}"
# : "${Flocq_CI_ARCHIVEURL:=${Flocq_CI_GITURL}/-/archive}"

########################################################################
# Coquelicot
########################################################################

# Picking
#
# Before picking this was on 155e88c47e3793f1f2c4118bc1d4520abe780d74
# = Aug 19 2019 master
#   "Update URL."
#
# There are no Coq version specific tags or branches
#
# The latest tag is coquelicot-3.0.3 from Aug 19 2019
# - This tag works with Coq 8.11 and it is not older than 6 months.
#
# The only change on master after 3.0.3 is the pre-pick commit
# - This commit is purely editorial and helps to follow the examples
#   (the URL for the exercises solved in the sample was inaccessible)
#
# The next commit after this on master is about coq-native libraries
# - This is currently not supportes on WIndows the main target of the picking
#
# A change was require to adjust to PR #11398 Rlist hides standard list constructors cons and nil
#
# => Use coquelicot-3.0.3 + URL fix + fix for RList
# => Ask upstream about opinion for a new tag

: "${coquelicot_CI_REF:=1ec80657ce992fc5aa660dca86d423671f02e33c}"
: "${coquelicot_CI_GITURL:=https://github.com/MSoegtropIMC/coquelicot}"
: "${coquelicot_CI_ARCHIVEURL:=${coquelicot_CI_GITURL}/archive}"

# Original source is
# : "${coquelicot_CI_GITURL:=https://gitlab.inria.fr/coquelicot/coquelicot}"
# : "${coquelicot_CI_ARCHIVEURL:=${coquelicot_CI_GITURL}/-/archive}"

########################################################################
# Coq-interval
########################################################################

# Picking
#
# Before picking this was on 839a03e1bddbafab868fbceee59abe678e32a0f3
# = Jul 20 2019 master
#   "Avoid uncontrolled characters (e.g., 'C:/') as arguments to $(addprefix)."
#
# There are no Coq version specific tags or branches
#
# The latest tag is interval-3.4.1 from "5 months ago"
# - This tag does not compile with Coq 8.11 mostly cause of library incompatibilities
#
# The hash 839a03e1bddbafab868fbceee59abe678e32a0f3 has been patched to work with 8.11
# - This combination has been tested quite a bit during tests for #11321
# - The same patch does not work for the latest commit on
#   master ec99901a45b1acba137a3e0e4230289b4fe9553f
#
# => Use commit 839a03e1bddbafab868fbceee59abe678e32a0f3

: "${interval_CI_REF:=839a03e1bddbafab868fbceee59abe678e32a0f3}"
: "${interval_CI_GITURL:=https://gitlab.inria.fr/coqinterval/interval}"
: "${interval_CI_ARCHIVEURL:=${interval_CI_GITURL}/-/archive}"

########################################################################
# Gappa stand alone tool
########################################################################

# Picking
#
# Before picking this was on f53e105cd73484fc76eb58ba24ead73be502c608
# = Jun 17 2019 master
#   "Fix outdated documentation."
# - This is the latest commit on master
#
# There are no Coq version specific tags or branches
#
# The latest tag is gappa-1.3.5 from May 24 2019 which is more than 6 months old
#
# 8.11 beta has been done with f53e105 (latest on master as of Jan 13 2020)
#
# => use f53e105cd73484fc76eb58ba24ead73be502c608

: "${gappa_tool_CI_REF:=f53e105cd73484fc76eb58ba24ead73be502c608}"
: "${gappa_tool_CI_GITURL:=https://gitlab.inria.fr/gappa/gappa}"
: "${gappa_tool_CI_ARCHIVEURL:=${gappa_tool_CI_GITURL}/-/archive}"

########################################################################
# Gappa plugin
########################################################################

# Picking
#
# Before picking this was on 07b2a6e39256b33f6b0b9f89c1e880dae51f740a
# = Jun 17 2019 master
#   "New release."
# - This is the latest commit on master
#
# There are no Coq version specific tags or branches
#
# The latest tag is gappalib-coq-1.4.2
# - this is the same thing as 07b2a6e and the latest commit on master
# - It does not work with Coq 8.11 (compiles but does not run)
#
# => Use tag gappalib-coq-1.4.2 + patch for Coq 8.11

: "${gappa_plugin_CI_REF:=d6f5177181c35f07ff50bd5c173ee13528e06576}"
: "${gappa_plugin_CI_GITURL:=https://github.com/MSoegtropIMC/gappa-coq}"
: "${gappa_plugin_CI_ARCHIVEURL:=${gappa_plugin_CI_GITURL}/archive}"

# Original source is
# : "${gappa_plugin_CI_GITURL:=https://gitlab.inria.fr/gappa/coq}"
# : "${gappa_plugin_CI_ARCHIVEURL:=${gappa_plugin_CI_GITURL}/-/archive}"

########################################################################
# CompCert
########################################################################

# Picking:
#
# Before picking this was on a99406bbd9c01dc04e79b14681a254fe22c9d424
# = Nov 28 2019 master
#   "Fix for AArch64 alignment problem"
#
# There are no Coq version specific tags or branches
#
# The latest tag is v3.6 from Sep 17 2019
# - This tag does not work with 8.11
# - There is a specific compatibility commit b7374d2 from Oct 2 2019
#
# => Use tag v3.6 with a patch which cherry picks b7374d2
# The cherry picking is done via patch dev/build/windows/patches_coq/compcert-v3.6.patch
# Since CI does not support patches or cherry picking, CI is set to what it was and
# compcert_CI_REF is overriden in the windows build script

: "${compcert_CI_REF:=a99406bbd9c01dc04e79b14681a254fe22c9d424}"
: "${compcert_CI_GITURL:=https://github.com/AbsInt/CompCert}"
: "${compcert_CI_ARCHIVEURL:=${compcert_CI_GITURL}/archive}"

########################################################################
# VST
########################################################################

# Picking:
#
# Before picking this was on a04b451b3ef9fd99007115f7745713f6fc84d1dc
# = Nov 26 2019 master
#   "Update submodules"
#
# There are no Coq version specific tags or branches
#
# The latest tag is v2.5 from Jan 13 2020
#
# => Use tag v2.5

: "${vst_CI_REF:=v2.5}"
: "${vst_CI_GITURL:=https://github.com/PrincetonUniversity/VST}"
: "${vst_CI_ARCHIVEURL:=${vst_CI_GITURL}/archive}"

########################################################################
# cross-crypto
########################################################################
: "${cross_crypto_CI_REF:=d9d278e941b12a49c0b58cfbe0418c85fbf743ee}"
: "${cross_crypto_CI_GITURL:=https://github.com/mit-plv/cross-crypto}"
: "${cross_crypto_CI_ARCHIVEURL:=${cross_crypto_CI_GITURL}/archive}"

########################################################################
# fiat_parsers
########################################################################
: "${fiat_parsers_CI_REF:=1aa83b9a3cd68b00df4a3f69c82ea9881c602836}"
: "${fiat_parsers_CI_GITURL:=https://github.com/mit-plv/fiat}"
: "${fiat_parsers_CI_ARCHIVEURL:=${fiat_parsers_CI_GITURL}/archive}"

########################################################################
# fiat_crypto
########################################################################
: "${fiat_crypto_CI_REF:=e9153f6b2ece3865a8f50675a598a24e23e99590}"
: "${fiat_crypto_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_CI_ARCHIVEURL:=${fiat_crypto_CI_GITURL}/archive}"

########################################################################
# fiat_crypto_legacy
########################################################################
: "${fiat_crypto_legacy_CI_REF:=5bb5aae1b728861f7b05ab42495c7fa0f75b5151}"
: "${fiat_crypto_legacy_CI_GITURL:=https://github.com/mit-plv/fiat-crypto}"
: "${fiat_crypto_legacy_CI_ARCHIVEURL:=${fiat_crypto_legacy_CI_GITURL}/archive}"

########################################################################
# coq_dpdgraph
########################################################################
: "${coq_dpdgraph_CI_REF:=04ab42b2d991f25f73b65307b9ab5ec4cbfa30b6}"
: "${coq_dpdgraph_CI_GITURL:=https://github.com/Karmaki/coq-dpdgraph}"
: "${coq_dpdgraph_CI_ARCHIVEURL:=${coq_dpdgraph_CI_GITURL}/archive}"

########################################################################
# CoLoR
########################################################################
: "${color_CI_REF:=44b6693d71f8ac72b2610f46d97b3c766ffddea5}"
: "${color_CI_GITURL:=https://github.com/fblanqui/color}"
: "${color_CI_ARCHIVEURL:=${color_CI_GITURL}/archive}"

########################################################################
# TLC
########################################################################
: "${tlc_CI_REF:=3a77d66bde6fe9365c7452f082d6fb34d044c771}"
: "${tlc_CI_GITURL:=https://github.com/charguer/tlc}"
: "${tlc_CI_ARCHIVEURL:=${tlc_CI_GITURL}/archive}"

########################################################################
# Bignums
########################################################################

# Picking:
#
# Before picking this was on v8.11
# = (as of Jan 13 2020)
#   Nov 21 2019 c23738415e814257bd14b009c27a27e7579917bc
#   "Merge pull request #30 from ejgallego/v8.11+back_to_dune"
# - This is the latest commit on v8.11 as of Jan 13 2020
#
# => Choose latest commit on master-8.11
# => Ask upstream to tag this as 8.11.0

: "${bignums_CI_REF:=c23738415e814257bd14b009c27a27e7579917bc}"
: "${bignums_CI_GITURL:=https://github.com/coq/bignums}"
: "${bignums_CI_ARCHIVEURL:=${bignums_CI_GITURL}/archive}"

########################################################################
# bedrock2
########################################################################
: "${bedrock2_CI_REF:=3585b23d66ed5b64523d9e4866a65ec23675ac11}"
: "${bedrock2_CI_GITURL:=https://github.com/mit-plv/bedrock2}"
: "${bedrock2_CI_ARCHIVEURL:=${bedrock2_CI_GITURL}/archive}"

########################################################################
# Equations
########################################################################

# Picking:
#
# Before picking this was on b593e3734f01c6f9c05987e4af593d2712025ae3
# = Nov 5 2019 master
#   "Fix Make dependencies of test-suite and examples" on master
#
# There are no 8.11 specific tags or branches
# - there are Coq version specific tags and branches => request tag
#
# The latest tag is v1.2.1-8.10-2
# - it includes a backport of b593e37 (25bed60) and a few more changes.
# - it does NOT compile with Coq 8.11
#
# Choosing b593e37 seems to be arbitrary (latest on master on that day)
# - still 8.11 beta was done with this pick, so keep it.
# - it compiles bot does not work with 8.11 (issues with installation)
#
# Latest master as of Jan 17 2020 is a13f2993f93d41d0cbd3a94e0bb18f927e5913ae
# - does not build with Coq 8.11
#
# => Choose b593e3734f01c6f9c05987e4af593d2712025ae3
# => Hack make_addon_equations in makecoq_mingw.sh to work around the installation issues
# => TODO: remove this hack if a proper picking is found
# => Ask upstream to tag this as 8.11.0

: "${equations_CI_REF:=b593e3734f01c6f9c05987e4af593d2712025ae3}"
: "${equations_CI_GITURL:=https://github.com/mattam82/Coq-Equations}"
: "${equations_CI_ARCHIVEURL:=${equations_CI_GITURL}/archive}"

########################################################################
# Elpi
########################################################################
: "${elpi_CI_REF:=da9ae08fccd43bff6efa44c7450a6b177bb17c0b}"
: "${elpi_CI_GITURL:=https://github.com/LPCIC/coq-elpi}"
: "${elpi_CI_ARCHIVEURL:=${elpi_CI_GITURL}/archive}"

########################################################################
# fcsl-pcm
########################################################################
: "${fcsl_pcm_CI_REF:=5a471724b4bb72e446bc803ddcb6d2a83e0e6077}"
: "${fcsl_pcm_CI_GITURL:=https://github.com/imdea-software/fcsl-pcm}"
: "${fcsl_pcm_CI_ARCHIVEURL:=${fcsl_pcm_CI_GITURL}/archive}"

########################################################################
# ext-lib
########################################################################

# Picking:
#
# Before picking this was on 341323ab3ba1a4941d0944c99fc951b54294f9a7
# = Nov 22 2019 master
#   "[ci skip] update template"
#   This is NOT the latest commit on master
#
# There are no 8.11 specific tags or branches
# - there are Coq version branches up to 8.9 but no tags
#
# The latest tag is v0.10.3 from Oct 17 2029
# - this tag works with 8.11 and is not older than 6 months
#
# => Use latest tag

: "${ext_lib_CI_REF:=v0.10.3}"
: "${ext_lib_CI_GITURL:=https://github.com/coq-ext-lib/coq-ext-lib}"
: "${ext_lib_CI_ARCHIVEURL:=${ext_lib_CI_GITURL}/archive}"

########################################################################
# simple-io
########################################################################
: "${simple_io_CI_REF:=4cefa4b60eb5de1a9fc3be596e5da50da2e901ad}"
: "${simple_io_CI_GITURL:=https://github.com/Lysxia/coq-simple-io}"
: "${simple_io_CI_ARCHIVEURL:=${simple_io_CI_GITURL}/archive}"

########################################################################
# quickchick
########################################################################

# Picking:
#
# Before picking this was on 581d839e7ae989dae311e2669aa2527e6601253f
# = Aug 23 2019 master
#   "Merge pull request #178 from ejgallego/api+varkind"
#   This is NOT the latest commit on master
#   This is behind the latest commit on the 8.10 branch
#
# There are no 8.11 specific tags or branches
# - there are Coq version branches up to 8.10 but tags only up to 8.7
#
# The latest tag is v1.1.0 from Apr 12 2020
# - this tag is older than 6 months and far behind the 8.10 branch
#
# The latest commit on 8.10 branch is
# = Dec 8 2019 1d00ecf673b370cc1fde4bb9c23ba13d4404b0bd
#   "fix STLC example"
# - This does not work with Coq 8.11
#
# Use 581d839e7ae989dae311e2669aa2527e6601253f because
# - it seems to be a Coq specific fix (comes from Coq team)
# - it was used during 8.11 beta
#
# => Use 581d839e7ae989dae311e2669aa2527e6601253f
# => Ask upstream to create a tag (either on this or something newer)

: "${quickchick_CI_REF:=581d839e7ae989dae311e2669aa2527e6601253f}"
: "${quickchick_CI_GITURL:=https://github.com/QuickChick/QuickChick}"
: "${quickchick_CI_ARCHIVEURL:=${quickchick_CI_GITURL}/archive}"

########################################################################
# menhirlib
########################################################################

# Picking:
#
# Before picking this was on ca0655b2f96057a271fb5c9a254a38d195b4a7f9
# = Feb 14 2019 master
#   "Axiom-free development, the interpreter should evaluate inside Coq with reasonnable performance.
#   This is the latest commit on master
#
# There are no Coq version specific tags or branches
#
# => Choose this commit (we also had it in 8.10)
# => Ask upstream to create library tags since we used this untagged commit since a while

: "${menhirlib_CI_REF:=ca0655b2f96057a271fb5c9a254a38d195b4a7f9}"
: "${menhirlib_CI_GITURL:=https://gitlab.inria.fr/fpottier/coq-menhirlib}"
: "${menhirlib_CI_ARCHIVEURL:=${menhirlib_CI_GITURL}/-/archive}"

########################################################################
# aac_tactics
########################################################################

# Picking:
#
# Before picking this was on c57960afb0c9702a8c3c12aec26534e3495bbde9
# = Nov 6 2019 v8.11
#   Merge pull request #51 from vbgl/noomega "
# - This is the latest commit on v8.11 as of Jan 13 2020
#
# => Choose latest commit on v8.11
# => Ask upstream to tag this as 8.11.0

: "${aac_tactics_CI_REF:=c10b948e296e2550ecacf09770da6896549299d4}"
: "${aac_tactics_CI_GITURL:=https://github.com/coq-community/aac-tactics}"
: "${aac_tactics_CI_ARCHIVEURL:=${aac_tactics_CI_GITURL}/archive}"

########################################################################
# paramcoq
########################################################################
: "${paramcoq_CI_REF:=v8.11}"
: "${paramcoq_CI_GITURL:=https://github.com/coq-community/paramcoq}"
: "${paramcoq_CI_ARCHIVEURL:=${paramcoq_CI_GITURL}/archive}"

########################################################################
# relation_algebra
########################################################################
: "${relation_algebra_CI_REF:=aaab2097f7da6f0909f01367e3abd77f87e0005b}"
: "${relation_algebra_CI_GITURL:=https://github.com/damien-pous/relation-algebra}"
: "${relation_algebra_CI_ARCHIVEURL:=${relation_algebra_CI_GITURL}/archive}"

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
: "${struct_tact_CI_REF:=b95f041cb83986fb0fe1f9689d7196e2f09a4839}"
: "${struct_tact_CI_GITURL:=https://github.com/uwplse/StructTact}"
: "${struct_tact_CI_ARCHIVEURL:=${struct_tact_CI_GITURL}/archive}"

: "${inf_seq_ext_CI_REF:=19f6359e65ecb872d49208f60bf8951fb76fe091}"
: "${inf_seq_ext_CI_GITURL:=https://github.com/DistributedComponents/InfSeqExt}"
: "${inf_seq_ext_CI_ARCHIVEURL:=${inf_seq_ext_CI_GITURL}/archive}"

: "${cheerios_CI_REF:=f0c7659c44999c6cfcd484dc3182affc3ff4248a}"
: "${cheerios_CI_GITURL:=https://github.com/uwplse/cheerios}"
: "${cheerios_CI_ARCHIVEURL:=${cheerios_CI_GITURL}/archive}"

: "${verdi_CI_REF:=2b94f5529eb7b8d28ef7e596383b4eec1d8343c5}"
: "${verdi_CI_GITURL:=https://github.com/uwplse/verdi}"
: "${verdi_CI_ARCHIVEURL:=${verdi_CI_GITURL}/archive}"

: "${verdi_raft_CI_REF:=51d8945e16ae976e58677ea3c423ca4b02061449}"
: "${verdi_raft_CI_GITURL:=https://github.com/uwplse/verdi-raft}"
: "${verdi_raft_CI_ARCHIVEURL:=${verdi_raft_CI_GITURL}/archive}"

########################################################################
# stdlib2
########################################################################
: "${stdlib2_CI_REF:=87767e25fbea6b38128d4b16fd62dd2edaad3503}"
: "${stdlib2_CI_GITURL:=https://github.com/coq/stdlib2}"
: "${stdlib2_CI_ARCHIVEURL:=${stdlib2_CI_GITURL}/archive}"

########################################################################
# argosy
########################################################################
: "${argosy_CI_REF:=4e98f348efb797499b06d51958d0654f07e3eb12}"
: "${argosy_CI_GITURL:=https://github.com/mit-pdos/argosy}"
: "${argosy_CI_ARCHIVEURL:=${argosy_CI_GITURL}/archive}"

########################################################################
# perennial
########################################################################
: "${perennial_CI_REF:=b420367026ec5d24b2bf38e7f986ca35af21f073}"
: "${perennial_CI_GITURL:=https://github.com/mit-pdos/perennial}"
: "${perennial_CI_ARCHIVEURL:=${perennial_CI_GITURL}/archive}"

########################################################################
# SF suite
########################################################################
: "${sf_CI_REF:=d41a56ee075259f271ae5288f7860b340cabc3a1}"
: "${sf_CI_GITURL:=https://github.com/DeepSpec/sf}"
: "${sf_CI_ARCHIVEURL:=${sf_CI_GITURL}/archive}"
