#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

mkdir -p ${CI_BUILD_DIR} && cd ${CI_BUILD_DIR}
wget -qO- ${sf_lf_CI_TARURL}  | tar xvz
wget -qO- ${sf_plf_CI_TARURL} | tar xvz
wget -qO- ${sf_vfa_CI_TARURL} | tar xvz

sed -i.bak '1i From Coq Require Extraction.' lf/Extraction.v
sed -i.bak '1i From Coq Require Extraction.' vfa/Extract.v

# Delete useless calls to try omega; unfold
patch vfa/SearchTree.v <<EOF
*** SearchTree.v.bak	2017-09-06 19:12:59.000000000 +0200
--- SearchTree.v	2017-11-21 16:34:41.000000000 +0100
***************
*** 674,683 ****
     forall i j : key, ~ (i > j) -> ~ (i < j) -> i=j.
  Proof.
  intros.
- try omega.  (* Oops! [omega] cannot solve this one.
-     The problem is that [i] and [j] have type [key] instead of type [nat].
-     The solution is easy enough: *)
- unfold key in *.
  omega.

  (** So, if you get stuck on an [omega] that ought to work,
--- 674,679 ----
EOF

( cd lf && make clean && make )

( cd plf && sed -i.bak 's/(K,N)/((K,N))/' LibTactics.v && make clean && make )

( cd vfa && make clean && make )
