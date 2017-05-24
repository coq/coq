#!/bin/bash

###################### COPYRIGHT/COPYLEFT ######################

# (C) 2016 Intel Deutschland GmbH
# Author: Michael Soegtrop
#
# Released to the public by Intel under the
# GNU Lesser General Public License Version 2.1 or later
# See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html
#
# With very valuable help on building GTK from
#   https://wiki.gnome.org/Projects/GTK+/Win32/MSVCCompilationOfGTKStack
#   http://www.gaia-gis.it/spatialite-3.0.0-BETA/mingw64_how_to.html

###################### Script safety and debugging settings ######################

set -o nounset
set -o errexit
set -x

# Set this to 1 if all module directories shall be removed before build (no incremental make)
RMDIR_BEFORE_BUILD=1

###################### NOTES #####################

# - This file goes together with MakeCoq_ForMignGW.bat, which sets up cygwin
#   with all required packages and then calls this script.
#
# - This script uses set -o errexit, so if anything fails, the script will stop
#
# - cygwin provided mingw64 packages like mingw64-x86_64-zlib are installed to
#   /usr/$TARGET_ARCH/sys-root/mingw, so we use this as install prefix
#
# - if mingw64-x86_64-pkg-config is installed BEFORE building libpng or pixman,
#   the .pc files are properly created in /usr/$TARGET_ARCH/sys-root/mingw/lib/pkgconfig
#
# - pango and some others uses pkg-config executable names without path, which doesn't work in cross compile mode
#   There are several possible solutions
#     1.) patch build files to get the prefix from pkg-config and use $prefix/bin/ as path
#         - doesn't work for pango because automake goes wild
#         - mingw tools are not able to handle cygwin path (they need absolute windows paths)
#     2.) export PATH=$PATH:/usr/$TARGET_ARCH/sys-root/mingw/bin
#         - a bit dangerous because this exposes much more than required
#         - mingw tools are not able to handle cygwin path (they need absolute windows paths)
#     3.) Install required tools via cygwin modules libglib2.0-devel and libgdk_pixbuf2.0-devel
#         - Possibly version compatibility issues
#         - Possibly mingw/cygwin compatibility issues, e.g. when building font or terminfo databases
#     4.) Build required tools for mingw and cygwin
#         - Possibly mingw/cygwin compatibility issues, e.g. when building font or terminfo databases
#
#   We use method 3 below
#   Method 2 can be tried by putting the cross tools in the path before the cygwin tools (in configure_profile.sh)
#
# - It is tricky to build 64 bit binaries with 32 bit cross tools and vice versa.
#   This is because the linker needs to load DLLs from C:\windows\system32, which contains
#   both 32 bit and 64 bit DLLs, and which one you get depends by some black magic on if the using
#   app is a 32 bit or 64 bit app. So better build 32 bit mingw with 32 bit cygwin and 64 with 64.
#   Alternatively the required 32 bit or 64 bit DLLs need to be copied with a 32 bit/64bit cp to some
#   folder without such black magic.
#
# - The file selection for the Coq Windows Installer is done with make install (unlike the original script)
#   Relocatble builds are first configured with prefix=./ then build and then
#   reconfigured with prefix=<installroot> before make install.


###################### ARCHITECTURES #####################

# The OS on which the build of the tool/lib runs
BUILD=`gcc -dumpmachine`

# The OS on which the tool runs
# "`find /bin -name "*mingw32-gcc.exe"`" -dumpmachine
HOST=$TARGET_ARCH

# The OS for which the tool creates code/for which the libs are
TARGET=$TARGET_ARCH

# Cygwin uses different arch name for 32 bit than mingw/gcc
case $ARCH in
  x86_64) CYGWINARCH=x86_64 ;;
  i686)   CYGWINARCH=x86 ;;
  *)      false ;;
esac

###################### PATHS #####################

# Name and create some 'global' folders
PATCHES=/build/patches
BUILDLOGS=/build/buildlogs
FLAGFILES=/build/flagfiles
TARBALLS=/build/tarballs
FILELISTS=/build/filelists

mkdir -p $BUILDLOGS
mkdir -p $FLAGFILES
mkdir -p $TARBALLS
mkdir -p $FILELISTS
cd /build


# sysroot prefix for the above /build/host/target combination
PREFIX=$CYGWIN_INSTALLDIR_MFMT/usr/$TARGET_ARCH/sys-root/mingw

# Install / Prefix folder for COQ
PREFIXCOQ=$RESULT_INSTALLDIR_MFMT

# Install / Prefix folder for OCaml
if [ "$INSTALLOCAML" == "Y" ]; then
  PREFIXOCAML=$PREFIXCOQ
else
  PREFIXOCAML=$PREFIX
fi

mkdir -p $PREFIX/bin
mkdir -p $PREFIXCOQ/bin
mkdir -p $PREFIXOCAML/bin

###################### Copy Cygwin Setup Info #####################

# Copy Cygwin repo ini file and installed files db to tarballs folder.
# Both files together document the exact selection and version of cygwin packages.
# Do this as early as possible to avoid changes by other setups (the repo folder is shared).

# Escape URL to folder name
CYGWIN_REPO_FOLDER=${CYGWIN_REPOSITORY}/
CYGWIN_REPO_FOLDER=${CYGWIN_REPO_FOLDER//:/%3a}
CYGWIN_REPO_FOLDER=${CYGWIN_REPO_FOLDER//\//%2f}

# Copy files
cp $CYGWIN_LOCAL_CACHE_WFMT/$CYGWIN_REPO_FOLDER/$CYGWINARCH/setup.ini $TARBALLS
cp /etc/setup/installed.db $TARBALLS
  
###################### LOGGING #####################

# The folder which receives log files
mkdir -p buildlogs
LOGS=`pwd`/buildlogs

# The current log target (first part of the log file name)
LOGTARGET=other

log1() {
  "$@" > $LOGS/$LOGTARGET-$1.log 2> $LOGS/$LOGTARGET-$1.err
}

log2() {
  "$@" > $LOGS/$LOGTARGET-$1-$2.log 2> $LOGS/$LOGTARGET-$1-$2.err
}

log_1_3() {
  "$@" > $LOGS/$LOGTARGET-$1-$3.log 2> $LOGS/$LOGTARGET-$1-$3.err
}

logn() {
  LOGTARGETEX=$1
  shift
  "$@" > $LOGS/$LOGTARGET-$LOGTARGETEX.log 2> $LOGS/$LOGTARGET-$LOGTARGETEX.err
}
 
###################### UTILITY FUNCTIONS #####################

# ------------------------------------------------------------------------------
# Get a source tar ball, expand and patch it
# - get source archive from $SOURCE_LOCAL_CACHE_CFMT or online using wget
# - create build folder
# - extract source archive
# - patch source file if patch exists
# 
# Parameters
# $1 file server name including protocol prefix
# $2 file name (without extension)
# $3 file extension
# $4 number of path levels to strip from tar (usually 1)
# $5 module name (if different from archive)
# $6 expand folder name (if different from module name)
# ------------------------------------------------------------------------------

function get_expand_source_tar {
  # Handle optional parameters
  if [ "$#" -ge 4 ] ; then
    strip=$4
  else
    strip=1
  fi

  if [ "$#" -ge 5 ] ; then
    name=$5
  else
    name=$2
  fi
  
  if [ "$#" -ge 6 ] ; then
    folder=$6
  else
    folder=$name
  fi
  
  # Set logging target
  logtargetold=$LOGTARGET
  LOGTARGET=$name
  
  # Get the source archive either from the source cache or online
  if [ ! -f $TARBALLS/$name.$3 ] ; then
    if [ -f $SOURCE_LOCAL_CACHE_CFMT/$name.$3 ] ; then
      cp $SOURCE_LOCAL_CACHE_CFMT/$name.$3 $TARBALLS
    else
      wget $1/$2.$3
      if [ ! "$2.$3" == "$name.$3" ] ; then
        mv $2.$3 $name.$3
      fi
      mv $name.$3 $TARBALLS
      # Save the source archive in the source cache
      if [ -d $SOURCE_LOCAL_CACHE_CFMT ] ; then
        cp $TARBALLS/$name.$3 $SOURCE_LOCAL_CACHE_CFMT
      fi
    fi
  fi
  
  # Remove build directory (clean build)
  if [ $RMDIR_BEFORE_BUILD -eq 1 ] ; then
    rm -f -r $folder
  fi
  
  # Create build directory and cd
  mkdir -p $folder
  cd $folder
  
  # Extract source archive
  if [ "$3" == "zip" ] ; then
    log1 unzip $TARBALLS/$name.$3
    if [ "$strip" == "1" ] ; then
      # Ok, this is dirty, but it works and it fails if there are name clashes
      mv */* .
    else
      echo "Unzip strip count not supported"
      return 1
    fi
  else
    logn untar tar xvaf $TARBALLS/$name.$3 --strip $strip
  fi
  
  # Patch if patch file exists
  if [ -f $PATCHES/$name.patch ] ; then
    log1 patch -p1 -i $PATCHES/$name.patch
  fi
  
  # Go back to base folder
  cd ..

  LOGTARGET=$logtargetold
}

# ------------------------------------------------------------------------------
# Prepare a module build
# - check if build is already done (name.finished file exists) - if so return 1
# - create name.started
# - get source archive from $SOURCE_LOCAL_CACHE_CFMT or online using wget
# - create build folder
# - cd to build folder and extract source archive
# - create bin_special subfolder and add it to $PATH
# - remember things for build_post
# 
# Parameters
# $1 file server name including protocol prefix
# $2 file name (without extension)
# $3 file extension
# $4 [optional] number of path levels to strip from tar (usually 1)
# $5 [optional] module name (if different from archive)
# ------------------------------------------------------------------------------

function build_prep {
  # Handle optional parameters
  if [ "$#" -ge 4 ] ; then
    strip=$4
  else
    strip=1
  fi

  if [ "$#" -ge 5 ] ; then
    name=$5
  else
    name=$2
  fi
  
  # Check if build is already done
  if [ ! -f flagfiles/$name.finished ] ; then
    BUILD_PACKAGE_NAME=$name
    BUILD_OLDPATH=$PATH
    BUILD_OLDPWD=`pwd`
    LOGTARGET=$name

    touch flagfiles/$name.started
    
    get_expand_source_tar $1 $2 $3 $strip $name
    
    cd $name
    
    # Create a folder and add it to path, where we can put special binaries
    # The path is restored in build_post
    mkdir bin_special
    PATH=`pwd`/bin_special:$PATH
    
    return 0
  else  
    return 1
  fi
}

# ------------------------------------------------------------------------------
# Finalize a module build
# - create name.finished
# - go back to base folder
# ------------------------------------------------------------------------------

function build_post {
  if [ ! -f flagfiles/$BUILD_PACKAGE_NAME.finished ]; then
    cd $BUILD_OLDPWD
    touch flagfiles/$BUILD_PACKAGE_NAME.finished
    PATH=$BUILD_OLDPATH
    LOGTARGET=other
  fi
}

# ------------------------------------------------------------------------------
# Build and install a module using the standard configure/make/make install process
# - prepare build (as above)
# - configure
# - make
# - make install
# - finalize build (as above)
#
# parameters
# $1 file server name including protocol prefix
# $2 file name (without extension)
# $3 file extension
# $4 patch function to call between untar and configure (or true if none)
# $5.. extra configure arguments
# ------------------------------------------------------------------------------

function build_conf_make_inst {
  if build_prep $1 $2 $3 ; then
    $4
    logn configure ./configure --build=$BUILD --host=$HOST --target=$TARGET --prefix=$PREFIX "${@:5}"
    log1 make $MAKE_OPT
    log2 make install
    log2 make clean
    build_post
  fi
}

# ------------------------------------------------------------------------------
# Install all files given by a glob pattern to a given folder
#
# parameters
# $1 glob pattern (in '')
# $2 target folder
# ------------------------------------------------------------------------------

function install_glob {
  # Check if any files matching the pattern exist
  if [ "$(echo $1)" != "$1" ] ; then
    install -D -t $2 $1
  fi
}


# ------------------------------------------------------------------------------
# Recursively Install all files given by a glob pattern to a given folder
#
# parameters
# $1 source path
# $2 pattern (in '')
# $3 target folder
# ------------------------------------------------------------------------------

function install_rec {
  ( cd $1 && find -type f -name "$2" -exec install -D -T  $1/{} $3/{} \; )
}

# ------------------------------------------------------------------------------
# Write a file list of the target folder
# The file lists are used to create file lists for the windows installer
#
# parameters
# $1 name of file list
# ------------------------------------------------------------------------------

function list_files {
  if [ ! -e "/build/filelists/$1" ] ; then
    ( cd $PREFIXCOQ && find -type f | sort > /build/filelists/$1 )
  fi
}

# ------------------------------------------------------------------------------
# Compute the set difference of two file lists
#
# parameters
# $1 name of list A-B (set difference of set A minus set B)
# $2 name of list A
# $3 name of list B
# ------------------------------------------------------------------------------

function diff_files {
  # See http://www.catonmat.net/blog/set-operations-in-unix-shell/ for file list set operations
  comm -23 <(sort "/build/filelists/$2") <(sort "/build/filelists/$3") > "/build/filelists/$1"
}

# ------------------------------------------------------------------------------
# Filter a list of files with a regular expression
#
# parameters
# $1 name of output file list
# $2 name of input file list
# $3 name of filter regexp
# ------------------------------------------------------------------------------

function filter_files {
  egrep "$3" "/build/filelists/$2" > "/build/filelists/$1"
}

# ------------------------------------------------------------------------------
# Convert a file list to NSIS installer format
#
# parameters
# $1 name of file list file (output file is the same with extension .nsi)
# ------------------------------------------------------------------------------

function files_to_nsis {
  # Split the path in the file list into path and filename and create SetOutPath and File instructions
  # Note: File /oname cannot be used, because it does not create the paths as SetOutPath does
  # Note: I didn't check if the redundant SetOutPath instructions have a bad impact on installer size or install time
  cat "/build/filelists/$1" | tr '/' '\\' | sed -r 's/^\.(.*)\\([^\\]+)$/SetOutPath $INSTDIR\\\1\nFile ${COQ_SRC_PATH}\\\1\\\2/' > "/build/filelists/$1.nsh"
}


###################### MODULE BUILD FUNCTIONS #####################

##### LIBPNG #####

function make_libpng {
  build_conf_make_inst  http://prdownloads.sourceforge.net/libpng  libpng-1.6.18  tar.gz  true
}

##### PIXMAN #####

function make_pixman {
  build_conf_make_inst  http://cairographics.org/releases  pixman-0.32.8  tar.gz  true
}

##### FREETYPE #####

function make_freetype {
  build_conf_make_inst  http://sourceforge.net/projects/freetype/files/freetype2/2.6.1  freetype-2.6.1  tar.bz2  true
}

##### EXPAT #####

function make_expat {
  build_conf_make_inst  http://sourceforge.net/projects/expat/files/expat/2.1.0  expat-2.1.0  tar.gz  true
}

##### FONTCONFIG #####

function make_fontconfig {
  make_freetype
  make_expat
  # CONFIGURE PARAMETERS
  # build/install fails without --disable-docs 
  build_conf_make_inst  http://www.freedesktop.org/software/fontconfig/release  fontconfig-2.11.94  tar.gz  true  --disable-docs
}

##### ICONV #####

function make_libiconv {
  build_conf_make_inst  http://ftp.gnu.org/pub/gnu/libiconv  libiconv-1.14  tar.gz  true
}

##### UNISTRING #####

function make_libunistring {
  build_conf_make_inst  http://ftp.gnu.org/gnu/libunistring  libunistring-0.9.5  tar.xz  true
}

##### NCURSES #####

function make_ncurses {
  # NOTE: ncurses is not required below. This is just kept for documentary purposes in case I need it later.
  #
  # NOTE: make install fails building the terminfo database because
  # : ${TIC_PATH:=unknown} in run_tic.sh
  # As a result pkg-config .pc files are not generated
  # Also configure of gettext gives two "considers"
  # checking where terminfo library functions come from... not found, consider installing GNU ncurses
  # checking where termcap library functions come from... not found, consider installing GNU ncurses
  # gettext make/make install work anyway
  #
  # CONFIGURE PARAMETERS
  # --enable-term-driver --enable-sp-funcs is rewuired for mingw (see README.MinGW)
  # additional changes 
  # ADD --with-pkg-config
  # ADD --enable-pc-files
  # ADD --without-manpages
  # REM --with-pthread
  build_conf_make_inst  http://ftp.gnu.org/gnu/ncurses  ncurses-5.9  tar.gz  true  --disable-home-terminfo --enable-reentrant --enable-sp-funcs --enable-term-driver --enable-interop --with-pkg-config --enable-pc-files --without-manpages
}

##### GETTEXT #####

function make_gettext {
  # Cygwin packet dependencies: (not 100% sure) libiconv-devel,libunistring-devel,libncurses-devel
  # Cygwin packet dependencies for gettext users: (not 100% sure) gettext-devel,libgettextpo-devel
  # gettext configure complains that ncurses is also required, but it builds without it
  # Ncurses is tricky to install/configure for mingw64, so I dropped ncurses
  make_libiconv
  make_libunistring
  build_conf_make_inst  http://ftp.gnu.org/pub/gnu/gettext  gettext-0.19  tar.gz  true
}

##### LIBFFI #####

function make_libffi {
  # NOTE: The official download server is down  ftp://sourceware.org/pub/libffi/libffi-3.2.1.tar.gz
  build_conf_make_inst  http://www.mirrorservice.org/sites/sourceware.org/pub/libffi  libffi-3.2.1  tar.gz  true
}

##### LIBEPOXY #####

function make_libepoxy {
  build_conf_make_inst  https://github.com/anholt/libepoxy/releases/download/v1.3.1  libepoxy-1.3.1  tar.bz2  true
}

##### LIBPCRE #####

function make_libpcre {
  build_conf_make_inst  ftp://ftp.csx.cam.ac.uk/pub/software/programming/pcre  pcre-8.39    tar.bz2  true
}

function make_libpcre2 {
  build_conf_make_inst  ftp://ftp.csx.cam.ac.uk/pub/software/programming/pcre  pcre2-10.22  tar.bz2  true
}

##### GLIB #####

function make_glib {
  # Cygwin packet dependencies: mingw64-x86_64-zlib
  make_gettext
  make_libffi
  make_libpcre
  # build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/glib/2.46  glib-2.46.0  tar.xz  true
  build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/glib/2.47  glib-2.47.5  tar.xz  true
}

##### ATK #####

function make_atk {
  make_gettext
  make_glib
  build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/atk/2.18  atk-2.18.0  tar.xz  true
}

##### PIXBUF #####

function make_gdk-pixbuf {
  # Cygwin packet dependencies: mingw64-x86_64-zlib
  make_libpng
  make_gettext
  make_glib
  # CONFIGURE PARAMETERS
  # --with-included-loaders=yes statically links the image file format handlers
  # This avoids "Cannot open pixbuf loader module file '/usr/x86_64-w64-mingw32/sys-root/mingw/lib/gdk-pixbuf-2.0/2.10.0/loaders.cache': No such file or directory"
  build_conf_make_inst  http://ftp.gnome.org/pub/GNOME/sources/gdk-pixbuf/2.32  gdk-pixbuf-2.32.1  tar.xz  true  --with-included-loaders=yes 
}

##### CAIRO #####

function make_cairo {
  # Cygwin packet dependencies: mingw64-x86_64-zlib
  make_libpng
  make_glib
  make_pixman
  make_fontconfig
  build_conf_make_inst  http://cairographics.org/releases  cairo-1.14.2  tar.xz  true
}

##### PANGO #####

function make_pango {
  make_cairo
  make_glib
  make_fontconfig
  build_conf_make_inst  http://ftp.gnome.org/pub/GNOME/sources/pango/1.38  pango-1.38.0  tar.xz  true
}

##### GTK2 #####

function patch_gtk2 {
  rm gtk/gtk.def
}

function make_gtk2 {
  # Cygwin packet dependencies: gtk-update-icon-cache
  if [ "$GTK_FROM_SOURCES" == "Y" ]; then
    make_glib
    make_atk
    make_pango
    make_gdk-pixbuf
    make_cairo
    build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/gtk+/2.24  gtk+-2.24.28  tar.xz  patch_gtk2
  fi
}

##### GTK3 #####

function make_gtk3 {
  make_glib
  make_atk
  make_pango
  make_gdk-pixbuf
  make_cairo
  make_libepoxy
  build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/gtk+/3.16  gtk+-3.16.7  tar.xz  true

  # make all incl. tests and examples runs through fine
  # make install fails with issue with 
  # 
  # make[5]: Entering directory '/home/soegtrop/GTK/gtk+-3.16.7/demos/gtk-demo'
  # test -n "" || ../../gtk/gtk-update-icon-cache --ignore-theme-index --force "/usr/x86_64-w64-mingw32/sys-root/mingw/share/icons/hicolor"
  # gtk-update-icon-cache.exe: Failed to open file /usr/x86_64-w64-mingw32/sys-root/mingw/share/icons/hicolor/.icon-theme.cache : No such file or directory
  # Makefile:1373: recipe for target 'install-update-icon-cache' failed
  # make[5]: *** [install-update-icon-cache] Error 1
  # make[5]: Leaving directory '/home/soegtrop/GTK/gtk+-3.16.7/demos/gtk-demo'
}

##### LIBXML2 #####

function make_libxml2 {
  # Cygwin packet dependencies: libtool automake
  # Note: latest release version 2.9.2 fails during configuring lzma, so using 2.9.1
  # Note: python binding requires <sys/select.h> which doesn't exist on cygwin
  if build_prep https://git.gnome.org/browse/libxml2/snapshot  libxml2-2.9.1  tar.xz ; then
    # ./autogen.sh --build=$BUILD --host=$HOST --target=$TARGET --prefix=$PREFIX --disable-shared --without-python
    # shared library required by gtksourceview
    ./autogen.sh --build=$BUILD --host=$HOST --target=$TARGET --prefix=$PREFIX --without-python
    log1 make $MAKE_OPT all
    log2 make install
    log2 make clean
    build_post
  fi
}

##### GTK-SOURCEVIEW2 #####

function make_gtk_sourceview2 {
  # Cygwin packet dependencies: intltool
  # gtksourceview-2.11.2 requires GTK2
  # gtksourceview-2.91.9 requires GTK3
  # => We use gtksourceview-2.11.2 which seems to be the newest GTK2 based one
  if [ "$GTK_FROM_SOURCES" == "Y" ]; then
    make_gtk2
    make_libxml2
    build_conf_make_inst  https://download.gnome.org/sources/gtksourceview/2.11  gtksourceview-2.11.2  tar.bz2  true
  fi
}

##### FLEXDLL FLEXLINK #####

# Note: there is a circular dependency between flexlink and ocaml (resolved in Ocaml 4.03.)
# For MinGW it is not even possible to first build an Ocaml without flexlink support,
# Because Makefile.nt doesn't support this. So we have to use a binary flexlink.
# One could of cause do a bootstrap run ...

# Install flexdll objects

function install_flexdll {
  cp flexdll.h /usr/$TARGET_ARCH/sys-root/mingw/include
  if [ "$TARGET_ARCH" == "i686-w64-mingw32" ]; then
    cp flexdll*_mingw.o /usr/$TARGET_ARCH/bin
    cp flexdll*_mingw.o $PREFIXOCAML/bin
  elif [ "$TARGET_ARCH" == "x86_64-w64-mingw32" ]; then
    cp flexdll*_mingw64.o /usr/$TARGET_ARCH/bin
    cp flexdll*_mingw64.o $PREFIXOCAML/bin
  else
    echo "Unknown target architecture"
    return 1
  fi
}

# Install flexlink

function install_flexlink {
  cp flexlink.exe /usr/$TARGET_ARCH/bin
    
  cp flexlink.exe $PREFIXOCAML/bin
}

# Get binary flexdll flexlink for building OCaml
# An alternative is to first build an OCaml without shared library support and build flexlink with it

function get_flex_dll_link_bin {
  if build_prep http://alain.frisch.fr/flexdll flexdll-bin-0.34 zip 1 ; then
    install_flexdll
    install_flexlink
    build_post
  fi
}

# Build flexdll and flexlink from sources after building OCaml

function make_flex_dll_link {
  if build_prep http://alain.frisch.fr/flexdll flexdll-0.34 tar.gz ; then
    if [ "$TARGET_ARCH" == "i686-w64-mingw32" ]; then
      log1 make $MAKE_OPT build_mingw flexlink.exe
    elif [ "$TARGET_ARCH" == "x86_64-w64-mingw32" ]; then
      log1 make $MAKE_OPT build_mingw64 flexlink.exe
    else
      echo "Unknown target architecture"
      return 1
    fi
    install_flexdll
    install_flexlink
    log2 make clean
    build_post
  fi
}

##### LN replacement #####

# Note: this does support symlinks, but symlinks require special user rights on Windows.
# ocamlbuild uses symlinks to link the executables in the build folder to the base folder.
# For this purpose hard links are better.

function make_ln {
  if [ ! -f flagfiles/myln.finished ] ; then
    touch flagfiles/myln.started
    mkdir -p myln
    cd myln
    cp $PATCHES/ln.c .
    $TARGET_ARCH-gcc -DUNICODE -D_UNICODE -DIGNORE_SYMBOLIC -mconsole -o ln.exe ln.c 
    install -D ln.exe $PREFIXCOQ/bin/ln.exe
    cd ..
    touch flagfiles/myln.finished
  fi
}

##### OCAML #####

function make_ocaml {
  get_flex_dll_link_bin
  if build_prep http://caml.inria.fr/pub/distrib/ocaml-4.02 ocaml-4.02.3 tar.gz 1 ; then
  # if build_prep http://caml.inria.fr/pub/distrib/ocaml-4.01 ocaml-4.01.0 tar.gz 1 ; then
    # See README.win32
    cp config/m-nt.h config/m.h
    cp config/s-nt.h config/s.h
    if [ "$TARGET_ARCH" == "i686-w64-mingw32" ]; then
        cp config/Makefile.mingw config/Makefile
    elif [ "$TARGET_ARCH" == "x86_64-w64-mingw32" ]; then
        cp config/Makefile.mingw64 config/Makefile
    else
        echo "Unknown target architecture"
        return 1
    fi

    # Prefix is fixed in make file - replace it with the real one
    sed -i "s|^PREFIX=.*|PREFIX=$PREFIXOCAML|" config/Makefile
    
    # We don't want to mess up Coq's dirctory structure so put the OCaml library in a separate folder
    # If we refer to the make variable ${PREFIX} below, camlp4 ends up having a wrong path:
    # D:\bin\coq64_buildtest_abs_ocaml4\bin>ocamlc -where => D:/bin/coq64_buildtest_abs_ocaml4/libocaml
    # D:\bin\coq64_buildtest_abs_ocaml4\bin>camlp4 -where => ${PREFIX}/libocaml\camlp4
    # So we put an explicit path in there
    sed -i "s|^LIBDIR=.*|LIBDIR=$PREFIXOCAML/libocaml|" config/Makefile
    
    # Note: ocaml doesn't support -j 8, so don't pass MAKE_OPT
    # I verified that 4.02.3 still doesn't support parallel build
    log2 make world -f Makefile.nt
    log2 make bootstrap -f Makefile.nt
    log2 make opt -f Makefile.nt
    log2 make opt.opt -f Makefile.nt
    log2 make install -f Makefile.nt
    # TODO log2 make clean -f Makefile.nt Temporarily disabled for ocamlbuild development
    
    # Move license files and other into into special folder
    if [ "$INSTALLMODE" == "absolute" ] || [ "$INSTALLMODE" == "relocatable" ]; then
      mkdir -p $PREFIXOCAML/license_readme/ocaml
      # 4.01 installs these files, 4.02 doesn't. So delete them and copy them from the sources.
      rm -f *.txt
      cp LICENSE      $PREFIXOCAML/license_readme/ocaml/License.txt
      cp INSTALL      $PREFIXOCAML/license_readme/ocaml/Install.txt
      cp README       $PREFIXOCAML/license_readme/ocaml/ReadMe.txt
      cp README.win32 $PREFIXOCAML/license_readme/ocaml/ReadMeWin32.txt
      cp VERSION      $PREFIXOCAML/license_readme/ocaml/Version.txt
      cp Changes      $PREFIXOCAML/license_readme/ocaml/Changes.txt
    fi

    build_post
  fi
  make_flex_dll_link
}

##### FINDLIB Ocaml library manager #####

function make_findlib {
  make_ocaml
  if build_prep http://download.camlcity.org/download findlib-1.5.6 tar.gz 1 ; then
    ./configure -bindir $PREFIXOCAML\\bin -sitelib $PREFIXOCAML\\libocaml\\site-lib -config $PREFIXOCAML\\etc\\findlib.conf
    # Note: findlib doesn't support -j 8, so don't pass MAKE_OPT
    log2 make all
    log2 make opt
    log2 make install
    log2 make clean
    build_post
  fi
}

##### MENHIR Ocaml Parser Generator #####

function make_menhir {
  make_ocaml
  make_findlib
  # if build_prep http://gallium.inria.fr/~fpottier/menhir menhir-20151112 tar.gz 1 ; then
  # For Ocaml 4.02
  # if build_prep http://gallium.inria.fr/~fpottier/menhir menhir-20151012 tar.gz 1 ; then
  # For Ocaml 4.01
  if build_prep http://gallium.inria.fr/~fpottier/menhir menhir-20140422 tar.gz 1 ; then
    # Note: menhir doesn't support -j 8, so don't pass MAKE_OPT
    log2 make all PREFIX=$PREFIXOCAML
    log2 make install PREFIX=$PREFIXOCAML
    mv $PREFIXOCAML/bin/menhir $PREFIXOCAML/bin/menhir.exe
    build_post
  fi
}

##### CAMLP4 Ocaml Preprocessor #####

function make_camlp4 {
  # OCaml up to 4.01 includes camlp4, from 4.02 it isn't included
  # Check if command camlp4 exists, if not build camlp4
  if ! command camlp4 ; then
    make_ocaml
    make_findlib
    if build_prep https://github.com/ocaml/camlp4/archive 4.02+6 tar.gz 1 camlp4-4.02+6 ; then
      # See https://github.com/ocaml/camlp4/issues/41#issuecomment-112018910
      logn configure ./configure
      # Note: camlp4 doesn't support -j 8, so don't pass MAKE_OPT
      log2 make all
      log2 make install
      log2 make clean
      build_post
    fi
  fi
}

##### CAMLP5 Ocaml Preprocessor #####

function make_camlp5 {
  make_ocaml
  make_findlib
  if build_prep http://camlp5.gforge.inria.fr/distrib/src camlp5-6.14 tgz 1 ; then
    logn configure ./configure 
    # Somehow my virus scanner has the boot.new/SAVED directory locked after the move for a second => repeat until success
    sed -i 's/mv boot.new boot/until mv boot.new boot; do sleep 1; done/' Makefile
    log1 make world.opt $MAKE_OPT
    log2 make install
    # For some reason gramlib.a is not copied, but it is required by Coq
    cp lib/gramlib.a $PREFIXOCAML/libocaml/camlp5/
    log2 make clean
    build_post
  fi
}

##### LABLGTK Ocaml GTK binding #####

# Note: when rebuilding lablgtk by deleting the .finished file,
# also delete <root>\usr\x86_64-w64-mingw32\sys-root\mingw\lib\site-lib
# Otherwise make install fails

function make_lablgtk {
  make_ocaml
  make_findlib
  make_camlp4
  if build_prep https://forge.ocamlcore.org/frs/download.php/1479 lablgtk-2.18.3 tar.gz 1 ; then
    # configure should be fixed to search for $TARGET_ARCH-pkg-config.exe
    cp /bin/$TARGET_ARCH-pkg-config.exe  bin_special/pkg-config.exe
    logn configure ./configure --build=$BUILD --host=$HOST --target=$TARGET --prefix=$PREFIXOCAML
    
    # lablgtk shows occasional errors with -j, so don't pass $MAKE_OPT
    
    # See https://sympa.inria.fr/sympa/arc/caml-list/2015-10/msg00204.html for the make || true + strip
    logn make-world-pre make world || true
    $TARGET_ARCH-strip.exe --strip-unneeded src/dlllablgtk2.dll
    
    log2 make world
    log2 make install
    log2 make clean
    build_post
  fi
}

##### Ocaml Stdint #####

function make_stdint {
  make_ocaml
  make_findlib
  if build_prep https://github.com/andrenth/ocaml-stdint/archive 0.3.0 tar.gz 1 Stdint-0.3.0; then
    # Note: the setup gets the proper install path from ocamlfind, but for whatever reason it wants
    # to create an empty folder in some folder which defaults to C:\Program Files.
    # The --preifx overrides this. Id didn't see any files created in /tmp/extra.
    log_1_3 ocaml setup.ml -configure --prefix /tmp/extra
    log_1_3 ocaml setup.ml -build
    log_1_3 ocaml setup.ml -install
    log_1_3 ocaml setup.ml -clean
    build_post
  fi
}

##### COQ #####

# Copy one DLLfrom cygwin MINGW packages to Coq install folder

function copy_coq_dll {
  if [ "$INSTALLMODE" == "absolute" ] || [ "$INSTALLMODE" == "relocatable" ]; then
    cp /usr/${ARCH}-w64-mingw32/sys-root/mingw/bin/$1 $PREFIXCOQ/bin/$1
  fi
}

# Copy required DLLs from cygwin MINGW packages to Coq install folder

function copy_coq_dlls {
  # HOW TO CREATE THE DLL LIST
  # With the list empty, after the build/install is finished, open coqide in dependency walker.
  # See http://www.dependencywalker.com/
  # Make sure to use the 32 bit / 64 bit version of depends matching the target architecture.
  # Select all missing DLLs from the module list, right click "copy filenames"
  # Delay loaded DLLs from Windows can be ignored (hour-glass icon at begin of line)
  # Do this recursively until there are no further missing DLLs (File close + reopen)
  # For running this quickly, just do "cd coq-<ver> ; call copy_coq_dlls ; cd .." at the end of this script.
  # Do the same for coqc and ocamlc (usually doesn't result in additional files)
  
  copy_coq_dll LIBATK-1.0-0.DLL
  copy_coq_dll LIBCAIRO-2.DLL
  copy_coq_dll LIBEXPAT-1.DLL
  copy_coq_dll LIBFFI-6.DLL
  copy_coq_dll LIBFONTCONFIG-1.DLL
  copy_coq_dll LIBFREETYPE-6.DLL
  copy_coq_dll LIBGDK-WIN32-2.0-0.DLL
  copy_coq_dll LIBGDK_PIXBUF-2.0-0.DLL
  copy_coq_dll LIBGIO-2.0-0.DLL
  copy_coq_dll LIBGLIB-2.0-0.DLL
  copy_coq_dll LIBGMODULE-2.0-0.DLL
  copy_coq_dll LIBGOBJECT-2.0-0.DLL
  copy_coq_dll LIBGTK-WIN32-2.0-0.DLL
  copy_coq_dll LIBINTL-8.DLL
  copy_coq_dll LIBPANGO-1.0-0.DLL
  copy_coq_dll LIBPANGOCAIRO-1.0-0.DLL
  copy_coq_dll LIBPANGOWIN32-1.0-0.DLL
  copy_coq_dll LIBPIXMAN-1-0.DLL
  copy_coq_dll LIBPNG16-16.DLL
  copy_coq_dll LIBXML2-2.DLL
  copy_coq_dll ZLIB1.DLL

  # Depends on if GTK is built from sources  
  if [ "$GTK_FROM_SOURCES" == "Y" ]; then
    copy_coq_dll libiconv-2.dll
    copy_coq_dll libpcre-1.dll
  else
    copy_coq_dll ICONV.DLL
    copy_coq_dll LIBBZ2-1.DLL
    copy_coq_dll LIBGTKSOURCEVIEW-2.0-0.DLL
    copy_coq_dll LIBHARFBUZZ-0.DLL
    copy_coq_dll LIBLZMA-5.DLL
    copy_coq_dll LIBPANGOFT2-1.0-0.DLL
  fi;

  # Architecture dependent files
  case $ARCH in
    x86_64) copy_coq_dll LIBGCC_S_SEH-1.DLL ;;
    i686)   copy_coq_dll LIBGCC_S_SJLJ-1.DLL ;;
    *)      false ;;
  esac
  
  # Win pthread version change
  copy_coq_dll LIBWINPTHREAD-1.DLL
}

function copy_coq_objects {
  # copy objects only from folders which exist in the target lib directory
  find . -type d | while read FOLDER ; do
    if [ -e $PREFIXCOQ/lib/$FOLDER ] ; then
      install_glob $FOLDER/'*.cmxa' $PREFIXCOQ/lib/$FOLDER 
      install_glob $FOLDER/'*.cmi'  $PREFIXCOQ/lib/$FOLDER 
      install_glob $FOLDER/'*.cma'  $PREFIXCOQ/lib/$FOLDER 
      install_glob $FOLDER/'*.cmo'  $PREFIXCOQ/lib/$FOLDER 
      install_glob $FOLDER/'*.a'    $PREFIXCOQ/lib/$FOLDER 
      install_glob $FOLDER/'*.o'    $PREFIXCOQ/lib/$FOLDER 
    fi
  done
}

# Copy required GTK config and suport files

function copq_coq_gtk {
  echo 'gtk-theme-name = "MS-Windows"'     >  $PREFIX/etc/gtk-2.0/gtkrc
  echo 'gtk-fallback-icon-theme = "Tango"' >> $PREFIX/etc/gtk-2.0/gtkrc

  if [ "$INSTALLMODE" == "absolute" ] || [ "$INSTALLMODE" == "relocatable" ]; then
    install_glob $PREFIX/etc/gtk-2.0/'*'                            $PREFIXCOQ/gtk-2.0
    install_glob $PREFIX/share/gtksourceview-2.0/language-specs/'*' $PREFIXCOQ/share/gtksourceview-2.0/language-specs
    install_glob $PREFIX/share/gtksourceview-2.0/styles/'*'         $PREFIXCOQ/share/gtksourceview-2.0/styles
    install_rec  $PREFIX/share/themes/ '*'                          $PREFIXCOQ/share/themes
    
    # This below item look like a bug in make install
    if [[ ! $COQ_VERSION == 8.4* ]] ; then
      mv $PREFIXCOQ/share/coq/*.lang $PREFIXCOQ/share/gtksourceview-2.0/language-specs
      mv $PREFIXCOQ/share/coq/*.xml  $PREFIXCOQ/share/gtksourceview-2.0/styles
    fi
    mkdir -p $PREFIXCOQ/ide
    mv $PREFIXCOQ/share/coq/*.png  $PREFIXCOQ/ide
    rmdir $PREFIXCOQ/share/coq
  fi
}

# Copy license and other info files

function copy_coq_license {
  if [ "$INSTALLMODE" == "absolute" ] || [ "$INSTALLMODE" == "relocatable" ]; then
    install -D doc/LICENSE                    $PREFIXCOQ/license_readme/coq/LicenseDoc.txt
    install -D LICENSE                        $PREFIXCOQ/license_readme/coq/License.txt
    install -D plugins/micromega/LICENSE.sos  $PREFIXCOQ/license_readme/coq/LicenseMicromega.txt
    install -D README                         $PREFIXCOQ/license_readme/coq/ReadMe.txt || true
    install -D README.md                      $PREFIXCOQ/license_readme/coq/ReadMe.md || true
    install -D README.doc                     $PREFIXCOQ/license_readme/coq/ReadMeDoc.txt
    install -D CHANGES                        $PREFIXCOQ/license_readme/coq/Changes.txt
    install -D INSTALL                        $PREFIXCOQ/license_readme/coq/Install.txt
    install -D INSTALL.doc                    $PREFIXCOQ/license_readme/coq/InstallDoc.txt
    install -D INSTALL.ide                    $PREFIXCOQ/license_readme/coq/InstallIde.txt
  fi
}

# Main function for creating Coq

function make_coq {
  make_ocaml
  make_lablgtk
  make_camlp5
  if 
    case $COQ_VERSION in
      git-*) build_prep https://github.com/coq/coq/archive ${COQ_VERSION##git-} zip 1 coq-${COQ_VERSION} ;;
      *)     build_prep https://coq.inria.fr/distrib/V$COQ_VERSION/files coq-$COQ_VERSION tar.gz ;;
    esac
  then
    if [ "$INSTALLMODE" == "relocatable" ]; then
      # HACK: for relocatable builds, first configure with ./, then build but before install reconfigure with the real target path
      logn configure ./configure -debug -with-doc no -prefix ./ -libdir ./lib -mandir ./man
    elif [ "$INSTALLMODE" == "absolute" ]; then
      logn configure ./configure -debug -with-doc no -prefix $PREFIXCOQ -libdir $PREFIXCOQ/lib -mandir $PREFIXCOQ/man
    else
      logn configure ./configure -debug -with-doc no -prefix $PREFIXCOQ
    fi

    # The windows resource compiler binary name is hard coded
    sed -i "s/i686-w64-mingw32-windres/$TARGET_ARCH-windres/" Makefile.build 
    sed -i "s/i686-w64-mingw32-windres/$TARGET_ARCH-windres/" Makefile.ide || true

    # 8.4x doesn't support parallel make
    if [[ $COQ_VERSION == 8.4* ]] ; then
      log1 make
    else
      log1 make $MAKE_OPT
    fi
    
    if [ "$INSTALLMODE" == "relocatable" ]; then
      ./configure -debug -with-doc no -prefix $PREFIXCOQ -libdir $PREFIXCOQ/lib -mandir $PREFIXCOQ/man
    fi

    log2 make install
    log1 copy_coq_dlls
    if [ "$INSTALLOCAML" == "Y" ]; then
      log1 copy_coq_objects
    fi
    
    copq_coq_gtk
    copy_coq_license

    # make clean seems to be broken for 8.5pl2
    # 1.) find | xargs fails on cygwin, can be fixed by sed -i 's|\| xargs rm -f|-exec rm -fv \{\} \+|' Makefile
    # 2.) clean of test suites fails with "cannot run complexity tests (no bogomips found)"
    # make clean
    
    build_post
  fi
}

##### GNU Make for MinGW #####

function make_mingw_make {
  if build_prep http://ftp.gnu.org/gnu/make make-4.2 tar.bz2 ; then
    # The config.h.win32 file is fine - don't edit it
    # We need to copy the mingw gcc here as "gcc" - then the batch file will use it
    cp /usr/bin/${ARCH}-w64-mingw32-gcc-5.4.0.exe ./gcc.exe
    # By some magic cygwin bash can run batch files
    logn build ./build_w32.bat gcc
    # Copy make to Coq folder
    cp GccRel/gnumake.exe $PREFIXCOQ/bin/make.exe
    build_post
  fi
}

##### GNU binutils for native OCaml #####

function make_binutils {
  if build_prep http://ftp.gnu.org/gnu/binutils binutils-2.27 tar.gz ; then
    logn configure ./configure --build=$BUILD --host=$HOST --target=$TARGET --prefix=$PREFIXCOQ --program-prefix=$TARGET-
    log1 make $MAKE_OPT
    log2 make install
    # log2 make clean
    build_post
  fi
}

##### GNU GCC for native OCaml #####

function make_gcc {
  # Note: the bz2 file is smaller, but decompressing bz2 really takes ages
  if build_prep ftp://ftp.fu-berlin.de/unix/languages/gcc/releases/gcc-5.4.0 gcc-5.4.0 tar.gz ; then
    # This is equivalent to "contrib/download_prerequisites" but uses caching
    # Update versions when updating gcc version
    get_expand_source_tar  ftp://gcc.gnu.org/pub/gcc/infrastructure  mpfr-2.4.2 tar.bz2 1 mpfr-2.4.2 mpfr
    get_expand_source_tar  ftp://gcc.gnu.org/pub/gcc/infrastructure  gmp-4.3.2  tar.bz2 1 gmp-4.3.2  gmp
    get_expand_source_tar  ftp://gcc.gnu.org/pub/gcc/infrastructure  mpc-0.8.1  tar.gz  1 mpc-0.8.1  mpc
    get_expand_source_tar  ftp://gcc.gnu.org/pub/gcc/infrastructure  isl-0.14   tar.bz2 1 isl-0.14   isl

    # For whatever reason gcc needs this (although it never puts anything into it)
    # Error: "The directory that should contain system headers does not exist:"
    # mkdir -p /mingw/include    without --with-sysroot
    mkdir -p $PREFIXCOQ/mingw/include

    # See https://gcc.gnu.org/install/configure.html
    logn configure ./configure --build=$BUILD --host=$HOST --target=$TARGET \
        --prefix=$PREFIXCOQ --program-prefix=$TARGET- --disable-win32-registry --with-sysroot=$PREFIXCOQ \
        --enable-languages=c --disable-nls \
        --disable-libsanitizer --disable-libssp --disable-libquadmath --disable-libgomp --disable-libvtv --disable-lto
        # --disable-decimal-float seems to be required
        # --with-sysroot=$PREFIX  results in configure error that this is not an absolute path
    log1 make $MAKE_OPT
    log2 make install
    # log2 make clean
    build_post
  fi
}

##### Get sources for Cygwin MinGW packages #####

function get_cygwin_mingw_sources {
  if [ ! -f flagfiles/cygwin_mingw_sources.finished ] ; then
    touch flagfiles/cygwin_mingw_sources.started

    # Find all installed files with mingw in the name and download the corresponding source code file from cygwin
    # Steps:
    # grep /etc/setup/installed.db for mingw       => mingw64-x86_64-gcc-g++ mingw64-x86_64-gcc-g++-5.4.0-2.tar.bz2 1
    # remove archive ending and trailing number    => mingw64-x86_64-gcc-g++ mingw64-x86_64-gcc-g++-5.4.0-2
    # replace space with /                         => ${ARCHIVE} = mingw64-x86_64-gcc-g++/mingw64-x86_64-gcc-g++-5.4.0-2
    # escape + signs using ${var//pattern/replace} => ${ARCHIVEESC} = mingw64-x86_64-gcc-g++/mingw64-x86_64-gcc-g\+\+-5.4.0-2
    # grep cygwin setup.ini for installed line + next line (the -A 1 option includes and "after context" of 1 line)
    # Note that the folders of the installed binaries and source are different. So we cannot grep just for the source line.
    # We could strip off the path and just grep for the file, though.
    # => install: x86_64/release/mingw64-x86_64-gcc/mingw64-x86_64-gcc-g++/mingw64-x86_64-gcc-g++-5.4.0-2.tar.xz 10163848 2f8cb7ba3e16ac8ce0455af01de490ded09061b1b06a9a8e367426635b5a33ce230e04005f059d4ea7b52580757da1f6d5bae88eba6b9da76d1bd95e8844b705
    #    source: x86_64/release/mingw64-x86_64-gcc/mingw64-x86_64-gcc-5.4.0-2-src.tar.xz 95565368 03f22997b7173b243fff65ea46a39613a2e4e75fc7e6cf0fa73b7bcb86071e15ba6d0ca29d330c047fb556a5e684cad57cd2f5adb6e794249e4b01fe27f92c95
    # Take the 2nd field of the last line          => ${SOURCE} = x86_64/release/mingw64-x86_64-gcc/mingw64-x86_64-gcc-5.4.0-2-src.tar.xz
    # Remove that path part                        => ${SOURCEFILE} = mingw64-x86_64-gcc-5.4.0-2-src.tar.xz

    grep "mingw" /etc/setup/installed.db | sed 's/\.tar\.bz2 [0-1]$//' | sed 's/ /\//'  | while read ARCHIVE ; do
      local ARCHIVEESC=${ARCHIVE//+/\\+}
      local SOURCE=`egrep -A 1 "install: ($CYGWINARCH|noarch)/release/[-+_/a-z0-9]*$ARCHIVEESC" $TARBALLS/setup.ini | tail -1 | cut -d " " -f 2`
      local SOURCEFILE=${SOURCE##*/}

      # Get the source file (either from the source cache or online)
      if [ ! -f $TARBALLS/$SOURCEFILE ] ; then
        if [ -f $SOURCE_LOCAL_CACHE_CFMT/$SOURCEFILE ] ; then
          cp $SOURCE_LOCAL_CACHE_CFMT/$SOURCEFILE $TARBALLS
        else
          wget "$CYGWIN_REPOSITORY/$SOURCE"
          mv $SOURCEFILE $TARBALLS
          # Save the source archive in the source cache
          if [ -d $SOURCE_LOCAL_CACHE_CFMT ] ; then
            cp $TARBALLS/$SOURCEFILE $SOURCE_LOCAL_CACHE_CFMT
          fi
        fi
      fi

    done

    touch flagfiles/cygwin_mingw_sources.finished
  fi
}

##### Coq Windows Installer #####

function make_coq_installer {
  make_coq
  make_mingw_make
  get_cygwin_mingw_sources

  # Prepare the file lists for the installer. We created to file list dumps of the target folder during the build:
  # ocaml: ocaml + menhir + camlp5 + findlib
  # ocal_coq: as above + coq
  
  # Create coq file list as ocaml_coq / ocaml
  diff_files coq ocaml_coq ocaml
  
  # Filter out object files
  filter_files coq_objects coq '\.(cmxa|cmi|cma|cmo|a|o)$' 
  
  # Filter out plugin object files
  filter_files coq_objects_plugins coq_objects '/lib/plugins/.*\.(cmxa|cmi|cma|cmo|a|o)$'
  
  # Coq objects objects required for plugin development = coq objects except those for pre installed plugins
  diff_files coq_plugindev coq_objects coq_objects_plugins
  
  # Coq files, except objects needed only for plugin development
  diff_files coq_base coq coq_plugindev
  
  # Convert section files to NSIS format
  files_to_nsis coq_base
  files_to_nsis coq_plugindev
  files_to_nsis ocaml
  
  # Get and extract NSIS Binaries
  if build_prep http://downloads.sourceforge.net/project/nsis/NSIS%202/2.51 nsis-2.51 zip ; then
    NSIS=`pwd`/makensis.exe
    chmod u+x "$NSIS"
    # Change to Coq folder
    cd ../coq-${COQ_VERSION}
    # Copy patched nsi file
    cp ../patches/coq_new.nsi dev/nsis
    cp ../patches/StrRep.nsh dev/nsis
    cp ../patches/ReplaceInFile.nsh dev/nsis
    VERSION=`grep ^VERSION= config/Makefile | cut -d = -f 2`
    cd dev/nsis
    logn nsis-installer "$NSIS" -DVERSION=$VERSION -DARCH=$ARCH -DCOQ_SRC_PATH=$PREFIXCOQ -DCOQ_ICON=..\\..\\ide\\coq.ico coq_new.nsi
    
    build_post
  fi
}

###################### TOP LEVEL BUILD #####################

make_gtk2
make_gtk_sourceview2

make_ocaml
make_findlib
make_lablgtk
make_camlp4
make_camlp5
make_menhir
make_stdint
list_files ocaml
make_coq

if [ "$INSTALLMAKE" == "Y" ] ; then
  make_mingw_make
fi

list_files ocaml_coq

if [ "$MAKEINSTALLER" == "Y" ] ; then
  make_coq_installer
fi

