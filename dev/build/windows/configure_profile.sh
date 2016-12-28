#!/bin/bash

rcfile=~/.bash_profile
donefile=~/.bash_profile.upated

if [ ! -f $donefile ] ; then

    echo >> $rcfile
    
    if [ -n "$1" ]; then
      echo export http_proxy="http://$1" >> $rcfile
      echo export https_proxy="http://$1" >> $rcfile
      echo export ftp_proxy="http://$1" >> $rcfile
    fi
    
    mkdir -p $RESULT_INSTALLDIR_CFMT/bin

    # A tightly controlled path helps to avoid issues
    # Note: the order is important: first have the cygwin binaries, then the mingw binaries in the path!
    # Note: /bin is mounted at /usr/bin and /lib at /usr/lib and it is common to use /usr/bin in PATH
    # See cat /proc/mounts
    echo "export PATH=/usr/local/bin:/usr/bin:$RESULT_INSTALLDIR_CFMT/bin:/usr/$TARGET_ARCH/sys-root/mingw/bin:/cygdrive/c/Windows/system32:/cygdrive/c/Windows" >> $rcfile

    # find and xargs complain if the environment is larger than (I think) 8k.
    # ORIGINAL_PATH (set by cygwin) can be a few k and exceed the limit
    echo unset ORIGINAL_PATH >> $rcfile
    
    # Other installations of OCaml will mess up things
    echo unset OCAMLLIB >> $rcfile

    touch $donefile
fi