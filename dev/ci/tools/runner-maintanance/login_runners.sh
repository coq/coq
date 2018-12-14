#!/bin/bash

###################### COPYRIGHT/COPYLEFT ######################

# (C) 2018 Intel Deutschland GmbH
# Author: Michael Soegtrop
#
# Released to the public by Intel under the
# GNU Lesser General Public License Version 2.1 or later
# See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

###################### CONFIGURE CYGWIN USER PROFILE FOR BUILDING COQ ######################

# login_runners <your_inria_ci_user_id>

# Usage: See ReadMe.md

RUNNERS="coq-windows coq-windows-untrusted coq-windows-untrusted-i01 coq-windows-untrusted-i02 coq-windows-untrusted2 coq-windows-untrusted3 coq-windows-untrusted5"

for runner in $RUNNERS
do
  echo Logging into $runner
  ssh -nNT -L 3380:$runner:3389 "$1"@ci-ssh.inria.fr &
  SSH_PID=$!
  mstsc inria-ci.rdp
  kill -9 $SSH_PID
done
