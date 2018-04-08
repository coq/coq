#!/bin/bash

###################### COPYRIGHT/COPYLEFT ######################

# (C) 2016 Intel Deutschland GmbH
# Author: Michael Soegtrop
#
# Released to the public by Intel under the
# GNU Lesser General Public License Version 2.1 or later
# See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

###################### CONFIGURE CYGWIN USER PROFILE FOR BUILDING COQ ######################

rcfile=~/.bash_profile
donefile=~/.bash_profile.upated

# to learn about `exec >> $file`, see https://www.tldp.org/LDP/abs/html/x17974.html
exec >> $rcfile

if [ ! -f $donefile ] ; then

    if [ "$1" != "" ] && [ "$1" != " " ]; then
      echo export http_proxy="http://$1"
      echo export https_proxy="http://$1"
      echo export ftp_proxy="http://$1"
    fi

    mkdir -p "$RESULT_INSTALLDIR_CFMT/bin"

    # A tightly controlled path helps to avoid issues
    # Note: the order is important: first have the cygwin binaries, then the mingw binaries in the path!
    # Note: /bin is mounted at /usr/bin and /lib at /usr/lib and it is common to use /usr/bin in PATH
    # See cat /proc/mounts
    echo "export PATH=/usr/local/bin:/usr/bin:$RESULT_INSTALLDIR_CFMT/bin:/usr/$TARGET_ARCH/sys-root/mingw/bin:/cygdrive/c/Windows/system32:/cygdrive/c/Windows"

    # find and xargs complain if the environment is larger than (I think) 8k.
    # ORIGINAL_PATH (set by cygwin) can be a few k and exceed the limit
    echo unset ORIGINAL_PATH
    # Other installations of OCaml will mess up things
    echo unset OCAMLLIB

    touch $donefile
fi
