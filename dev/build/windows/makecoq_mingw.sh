#!/bin/bash

###################### COPYRIGHT/COPYLEFT ######################

# (C) 2016..2018 Intel Deutschland GmbH
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
# Print current wall time as part of the xtrace
export PS4='+\t '

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
BUILD=$(gcc -dumpmachine)

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

# Create source cache folder
mkdir -p "$SOURCE_LOCAL_CACHE_CFMT"

# sysroot prefix for the above /build/host/target combination
# This must be in MFMT (C:/.../) because the OCaml library path is based on it and OCaml is a MinGW application.
PREFIXMINGW=$CYGWIN_INSTALLDIR_MFMT/usr/$TARGET_ARCH/sys-root/mingw

# Install / Prefix folder for COQ
PREFIXCOQ=$RESULT_INSTALLDIR_MFMT

# Install / Prefix folder for OCaml
if [ "$INSTALLOCAML" == "Y" ]; then
  PREFIXOCAML=$PREFIXCOQ
else
  PREFIXOCAML=$PREFIXMINGW
fi

mkdir -p "$PREFIXMINGW/bin"
mkdir -p "$PREFIXCOQ/bin"
mkdir -p "$PREFIXOCAML/bin"

# This is required for building addons and plugins
# This must be CFMT (/cygdrive/c/...) otherwise coquelicot 3.0.2 configure fails.
# coquelicot uses which ${COQBIN}/coqc to check if coqc exists. This does not work with COQBIN in MFMT.
export COQBIN=$RESULT_INSTALLDIR_CFMT/bin/
# This must be MFMT (C:/) otherwise bignums 68a7a3d7e0b21985913a6c3ee12067f4c5ac4e20 fails
export COQLIB=$RESULT_INSTALLDIR_MFMT/lib/coq/

###################### Copy Cygwin Setup Info #####################

# Copy Cygwin repo ini file and installed files db to tarballs folder.
# Both files together document the exact selection and version of cygwin packages.
# Do this as early as possible to avoid changes by other setups (the repo folder is shared).

# Escape URL to folder name
CYGWIN_REPO_FOLDER=${CYGWIN_REPOSITORY}/
CYGWIN_REPO_FOLDER=${CYGWIN_REPO_FOLDER//:/%3a}
CYGWIN_REPO_FOLDER=${CYGWIN_REPO_FOLDER//\//%2f}

# Copy files
cp "$CYGWIN_LOCAL_CACHE_WFMT/$CYGWIN_REPO_FOLDER/$CYGWINARCH/setup.ini" $TARBALLS
cp /etc/setup/installed.db $TARBALLS

###################### LOGGING #####################

# The folder which receives log files
mkdir -p buildlogs
LOGS=$(pwd)/buildlogs

# The current log target (first part of the log file name)
LOGTARGET=other

# For an explanation of ${COQREGTESTING:-N} search for ${parameter:-word} in
# http://pubs.opengroup.org/onlinepubs/009695399/utilities/xcu_chap02.html

if [ "${COQREGTESTING:-N}" == "Y" ] ; then
  # If COQREGTESTING, log to log files only
  # Log command output - take log target name from command name (like log1 make => log target is "<module>-make")
  log1() {
    { local -; set +x; } 2> /dev/null
    "$@" >"$LOGS/$LOGTARGET-$1_log.txt"  2>"$LOGS/$LOGTARGET-$1_err.txt"
  }

  # Log command output - take log target name from command name and first argument (like log2 make install => log target is "<module>-make-install")
  log2() {
    { local -; set +x; } 2> /dev/null
    "$@" >"$LOGS/$LOGTARGET-$1-$2_log.txt" 2>"$LOGS/$LOGTARGET-$1-$2_err.txt"
  }

  # Log command output - take log target name from command name and second argument (like log_1_3 ocaml setup.ml -configure => log target is "<module>-ocaml--configure")
  log_1_3() {
    { local -; set +x; } 2> /dev/null
    "$@" >"$LOGS/$LOGTARGET-$1-$3_log.txt" 2>"$LOGS/$LOGTARGET-$1-$3_err.txt"
  }

  # Log command output - log target name is first argument (like logn untar tar xvaf ... => log target is "<module>-untar")
  logn() {
    { local -; set +x; } 2> /dev/null
    LOGTARGETEX=$1
    shift
    "$@" >"$LOGS/$LOGTARGET-${LOGTARGETEX}_log.txt" 2>"$LOGS/$LOGTARGET-${LOGTARGETEX}_err.txt"
  }
else
  # If COQREGTESTING, log to log files and console
  # Log command output - take log target name from command name (like log1 make => log target is "<module>-make")
  log1() {
    { local -; set +x; } 2> /dev/null
    "$@" > >(tee "$LOGS/$LOGTARGET-$1_log.txt" | sed -e "s/^/$LOGTARGET-$1_log.txt: /") 2> >(tee "$LOGS/$LOGTARGET-$1_err.txt" | sed -e "s/^/$LOGTARGET-$1_err.txt: /" 1>&2)
  }

  # Log command output - take log target name from command name and first argument (like log2 make install => log target is "<module>-make-install")
  log2() {
    { local -; set +x; } 2> /dev/null
    "$@" > >(tee "$LOGS/$LOGTARGET-$1-$2_log.txt" | sed -e "s/^/$LOGTARGET-$1-$2_log.txt: /") 2> >(tee "$LOGS/$LOGTARGET-$1-$2_err.txt" | sed -e "s/^/$LOGTARGET-$1-$2_err.txt: /" 1>&2)
  }

  # Log command output - take log target name from command name and second argument (like log_1_3 ocaml setup.ml -configure => log target is "<module>-ocaml--configure")
  log_1_3() {
    { local -; set +x; } 2> /dev/null
    "$@" > >(tee "$LOGS/$LOGTARGET-$1-$3_log.txt" | sed -e "s/^/$LOGTARGET-$1-$3_log.txt: /") 2> >(tee "$LOGS/$LOGTARGET-$1-$3_err.txt" | sed -e "s/^/$LOGTARGET-$1-$3_err.txt: /" 1>&2)
  }

  # Log command output - log target name is first argument (like logn untar tar xvaf ... => log target is "<module>-untar")
  logn() {
    { local -; set +x; } 2> /dev/null
    LOGTARGETEX=$1
    shift
    "$@" > >(tee "$LOGS/$LOGTARGET-${LOGTARGETEX}_log.txt" | sed -e "s/^/$LOGTARGET-${LOGTARGETEX}_log.txt: /") 2> >(tee "$LOGS/$LOGTARGET-${LOGTARGETEX}_err.txt" | sed -e "s/^/$LOGTARGET-${LOGTARGETEX}_err.txt: /" 1>&2)
  }
fi

###################### 'UNFIX' SED #####################

# In Cygwin SED used to do CR-LF to LF conversion, but since sed 4.4-1 this was changed
# We replace sed with a shell script which restores the old behavior for piped input

#if [ -f /bin/sed.exe ]
#then
#  mv /bin/sed.exe /bin/sed_orig.exe
#fi
#cat  > /bin/sed << EOF
##!/bin/sh
#dos2unix | /bin/sed_orig.exe "$@"
#EOF
#chmod a+x /bin/sed

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
# $4 [optional] number of path levels to strip from tar (usually 1)
# $5 [optional] module name (if different from archive)
# $6 [optional] expand folder name (if different from module name)
# $7 [optional] module base name (used as 2nd choice for patches, defaults to $5)
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

  if [ "$#" -ge 7 ] ; then
    basename=$7
  else
    basename=$name
  fi

  # Set logging target
  logtargetold=$LOGTARGET
  LOGTARGET=$name

  # Get the source archive either from the source cache or online
  if [ ! -f "$TARBALLS/$name.$3" ] ; then
    if [ -f "$SOURCE_LOCAL_CACHE_CFMT/$name.$3" ] ; then
      cp "$SOURCE_LOCAL_CACHE_CFMT/$name.$3" "$TARBALLS"
    else
      wget --progress=dot:giga "$1/$2.$3"
      if file -i "$2.$3" | grep text/html; then
        echo Download failed: "$1/$2.$3"
        echo The file wget downloaded is an html file:
        cat "$2.$3"
        exit 1
      fi
      if [ ! "$2.$3" == "$name.$3" ] ; then
        mv "$2.$3" "$name.$3"
      fi
      mv "$name.$3" "$TARBALLS"
      # Save the source archive in the source cache
      if [ -d "$SOURCE_LOCAL_CACHE_CFMT" ] ; then
        cp "$TARBALLS/$name.$3" "$SOURCE_LOCAL_CACHE_CFMT"
      fi
    fi
  fi

  # Remove build directory (clean build)
  if [ $RMDIR_BEFORE_BUILD -eq 1 ] ; then
    rm -f -r "$folder"
  fi

  # Create build directory and cd
  mkdir -p "$folder"
  cd "$folder"

  # Extract source archive
  if [ "$3" == "zip" ] ; then
    log1 unzip "$TARBALLS/$name.$3"
    if [ "$strip" == "1" ] ; then
      # move subfolders of root folders one level up
      find "$(ls)" -mindepth 1 -maxdepth 1 -exec mv -- "{}" . \;
    else
      echo "Unzip strip count not supported"
      exit 1
    fi
  else
    logn untar tar xvaf "$TARBALLS/$name.$3" --strip $strip
  fi

  # Patch if patch file exists
  # First try specific patch file name then generic patch file name
  # Note: set -o errexit does not work inside a function called in an if, so exit explicity.
  if [ -f "$PATCHES/$name.patch" ] ; then
    log1 patch -p1 -i "$PATCHES/$name.patch" || exit 1
  elif  [ -f "$PATCHES/$basename.patch" ] ; then
    log1 patch -p1 -i "$PATCHES/$basename.patch" || exit 1
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
# $6 [optional] module base name (used as 2nd choice for patches, defaults to $5)
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

  if [ "$#" -ge 6 ] ; then
    basename=$6
  else
    basename=$name
  fi

  # Set installer section to not set by default
  installersection=

  # Check if build is already done
  if [ ! -f "$FLAGFILES/$name.finished" ] ; then
    BUILD_PACKAGE_NAME=$name
    BUILD_OLDPATH=$PATH
    BUILD_OLDPWD=$(pwd)
    LOGTARGET=$name

    touch "$FLAGFILES/$name.started"

    get_expand_source_tar "$1" "$2" "$3" "$strip" "$name" "$name" "$basename"

    cd "$name"

    # Create a folder and add it to path, where we can put special binaries
    # The path is restored in build_post
    mkdir bin_special
    PATH=$(pwd)/bin_special:$PATH

    return 0
  else
    return 1
  fi
}

# ------------------------------------------------------------------------------
# Like build_prep, but gets the data from an entry in ci-basic-overlay.sh
# This assumes the following definitions exist in ci-basic-overlay.sh,
# or in a file in the user-overlays folder:
# $1_CI_REF
# $1_CI_ARCHIVEURL
# $1_CI_GITURL
# ATTENTION: variables in ci-basic-overlay.sh are loaded by load_overlay_data.
# load_overlay_data is is called at the end of make_coq (even if the build is skipped)
#
# Parameters
# $1 base name of module in ci-basic-overlay.sh, e.g. mathcomp, bignums, ...
# ------------------------------------------------------------------------------

function build_prep_overlay {
  urlvar=$1_CI_ARCHIVEURL
  gitvar=$1_CI_GITURL
  refvar=$1_CI_REF
  url=${!urlvar}
  git=${!gitvar}
  ref=${!refvar}
  ver=$(git ls-remote "$git" "refs/heads/$ref" | cut -f 1)
  if [[ "$ver" == "" ]]; then
      # $1_CI_REF must have been a tag or hash, not a branch
      ver="$ref"
  fi
  build_prep "$url" "$ver" tar.gz 1 "$1-$ver" "$1"
}

# ------------------------------------------------------------------------------
# Load overlay version variables from ci-basic-overlay.sh and user-overlays/*.sh
# ------------------------------------------------------------------------------

function load_overlay_data {
  if [ -n "${GITLAB_CI-}" ]; then
    export CI_BRANCH="$CI_COMMIT_REF_NAME"
    if [[ ${CI_BRANCH#pr-} =~ ^[0-9]*$ ]]; then
      export CI_PULL_REQUEST="${CI_BRANCH#pr-}"
    else
      export CI_PULL_REQUEST=""
    fi
  else
    export CI_BRANCH=""
    export CI_PULL_REQUEST=""
  fi

  for overlay in /build/user-overlays/*.sh; do
    . "$overlay"
  done
  . /build/ci-basic-overlay.sh
}

# ------------------------------------------------------------------------------
# Finalize a module build
# - create name.finished
# - go back to base folder
# ------------------------------------------------------------------------------

function build_post {
  if [ ! -f "$FLAGFILES/$BUILD_PACKAGE_NAME.finished" ]; then
    cd "$BUILD_OLDPWD"
    touch "$FLAGFILES/$BUILD_PACKAGE_NAME.finished"
    PATH=$BUILD_OLDPATH
    LOGTARGET=other
    installer_addon_end
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
  if build_prep "$1" "$2" "$3" ; then
    $4
    logn configure ./configure --build="$BUILD" --host="$HOST" --target="$TARGET" --prefix="$PREFIXMINGW" "${@:5}"
    # shellcheck disable=SC2086
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
# $1 source path
# $2 pattern (in '')
# $3 target folder
# ------------------------------------------------------------------------------

function install_glob {
  SRCDIR=$(realpath -m $1)
  DESTDIR=$(realpath -m $3)
  ( cd "$SRCDIR" && find . -maxdepth 1 -type f -name "$2" -exec install -D -T  "$SRCDIR"/{} "$DESTDIR"/{} \; )
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
  SRCDIR=$(realpath -m $1)
  DESTDIR=$(realpath -m $3)
  ( cd "$SRCDIR" && find . -type f -name "$2" -exec install -D -T  "$SRCDIR"/{} "$DESTDIR"/{} \; )
}

# ------------------------------------------------------------------------------
# Write a file list of the target folder
# The file lists are used to create file lists for the windows installer
# Don't overwrite an existing file list
#
# parameters
# $1 name of file list
# ------------------------------------------------------------------------------

function list_files {
  if [ ! -e "/build/filelists/$1" ] ; then
    ( cd "$PREFIXCOQ" && find . -type f | sort > /build/filelists/"$1" )
  fi
}

# ------------------------------------------------------------------------------
# Write a file list of the target folder
# The file lists are used to create file lists for the windows installer
# Do overwrite an existing file list
#
# parameters
# $1 name of file list
# ------------------------------------------------------------------------------

function list_files_always {
  ( cd "$PREFIXCOQ" && find . -type f | sort > /build/filelists/"$1" )
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
  grep -E "$3" "/build/filelists/$2" > "/build/filelists/$1"
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
  tr '/' '\\' < "/build/filelists/$1" | sed -r 's/^\.(.*)\\([^\\]+)$/SetOutPath $INSTDIR\\\1\nFile ${COQ_SRC_PATH}\\\1\\\2/' > "/build/filelists/$1.nsh"
}

# ------------------------------------------------------------------------------
# Create an nsis installer addon section
#
# parameters
# $1 identifier of installer section and base name of file list files
# $2 human readable name of section
# $3 description of section
# $4 flags (space separated list of keywords): off = default off
#
# $1 must be a valid NSIS identifier!
# ------------------------------------------------------------------------------

function installer_addon_section {
  installersection=$1
  list_files "addon_pre_$installersection"

  echo 'LangString' "DESC_$1" '${LANG_ENGLISH}' "\"$3\"" >> "/build/filelists/addon_strings.nsh"

  echo '!insertmacro MUI_DESCRIPTION_TEXT' '${'"Sec_$1"'}' '$('"DESC_$1"')' >> "/build/filelists/addon_descriptions.nsh"

  local sectionoptions=
  if [[ "$4" == *off* ]] ; then sectionoptions+=" /o" ; fi

  echo "Section $sectionoptions \"$2\" Sec_$1" >> "/build/filelists/addon_sections.nsh"
  echo 'SetOutPath "$INSTDIR\"' >> "/build/filelists/addon_sections.nsh"
  echo '!include "..\..\..\filelists\addon_'"$1"'.nsh"' >> "/build/filelists/addon_sections.nsh"
  echo 'SectionEnd' >> "/build/filelists/addon_sections.nsh"
}

# ------------------------------------------------------------------------------
# Start an installer addon dependency group
#
# parameters
# $1 identifier of the section which depends on other sections
# The parameters must match the $1 parameter of a installer_addon_section call
# ------------------------------------------------------------------------------

dependencysections=

function installer_addon_dependency_beg {
  installer_addon_dependency "$1"
  dependencysections="$1 $dependencysections"
}

# ------------------------------------------------------------------------------
# End an installer addon dependency group
# ------------------------------------------------------------------------------

function installer_addon_dependency_end {
  set -- $dependencysections
  shift
  dependencysections="$*"
}

# ------------------------------------------------------------------------------
# Create an nsis installer addon dependency entry
# This needs to be bracketed with installer_addon_dependencies_beg/end
#
# parameters
# $1 identifier of the section on which other sections might depend
# The parameters must match the $1 parameter of a installer_addon_section call
# ------------------------------------------------------------------------------

function installer_addon_dependency {
  for section in $dependencysections ; do
    echo '${CheckSectionDependency} ${Sec_'"$section"'} ${Sec_'"$1"'} '"'$section' '$1'" >> "/build/filelists/addon_dependencies.nsh"
  done
}

# ------------------------------------------------------------------------------
# Finish an installer section after an addon build
#
# This creates the file list files
#
# parameters: none
# ------------------------------------------------------------------------------

function installer_addon_end {
  if [ -n "$installersection" ]; then
    list_files "addon_post_$installersection"
    diff_files "addon_$installersection" "addon_post_$installersection" "addon_pre_$installersection"
    files_to_nsis "addon_$installersection"
  fi
}

# ------------------------------------------------------------------------------
# Set all timeouts in all .v files to 1000
# Since timeouts can lead to CI failures, this is useful
#
# parameters: none
# ------------------------------------------------------------------------------

function coq_set_timeouts_1000 {
  find . -type f -name '*.v' -print0 | xargs -0 sed -i 's/timeout\s\+[0-9]\+/timeout 1000/g'
}

###################### MODULE BUILD FUNCTIONS #####################

##### SED #####

function make_sed {
  if build_prep https://ftp.gnu.org/gnu/sed/  sed-4.2.2  tar.gz ; then
    logn configure ./configure
    log1 make $MAKE_OPT
    log2 make install
    log2 make clean
    build_post
  fi
}

##### LIBPNG #####

function make_libpng {
  build_conf_make_inst  http://prdownloads.sourceforge.net/libpng  libpng-1.6.34  tar.gz  true
}

##### PIXMAN #####

function make_pixman {
  build_conf_make_inst  http://cairographics.org/releases  pixman-0.34.0  tar.gz  true
}

##### FREETYPE #####

function make_freetype {
  build_conf_make_inst  http://sourceforge.net/projects/freetype/files/freetype2/2.9.1  freetype-2.9.1  tar.bz2  true
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
  build_conf_make_inst  http://www.freedesktop.org/software/fontconfig/release  fontconfig-2.12.93  tar.gz  true  --disable-docs
}

##### ICONV #####

function make_libiconv {
  build_conf_make_inst  http://ftp.gnu.org/pub/gnu/libiconv  libiconv-1.15  tar.gz  true
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
  # --enable-term-driver --enable-sp-funcs is required for mingw (see README.MinGW)
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

  build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/glib/2.57  glib-2.57.1  tar.xz  true

}

##### ATK #####

function make_atk {
  make_gettext
  make_glib
  build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/atk/2.30  atk-2.30.0  tar.xz  true
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
  build_conf_make_inst  http://ftp.gnome.org/pub/GNOME/sources/gdk-pixbuf/2.38  gdk-pixbuf-2.38.0  tar.xz  true  --with-included-loaders=yes
}

##### CAIRO #####

function make_cairo {
  # Cygwin packet dependencies: mingw64-x86_64-zlib
  make_libpng
  make_glib
  make_pixman
  make_fontconfig
  build_conf_make_inst  http://cairographics.org/releases  rcairo-1.16.2  tar.xz  true
}

##### PANGO #####

function make_pango {
  make_cairo
  make_glib
  make_fontconfig
  build_conf_make_inst  http://ftp.gnome.org/pub/GNOME/sources/pango/1.42  pango-1.42.4  tar.xz  true
}

##### GTK3 #####

function make_gtk3 {

  if [ "$GTK_FROM_SOURCES" == "Y" ]; then

      make_glib
      make_atk
      make_pango
      make_gdk-pixbuf
      make_cairo
      make_libepoxy
      build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/gtk+/3.24  gtk+-3.24.5  tar.xz  true
  fi

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
    # ./autogen.sh --build=$BUILD --host=$HOST --target=$TARGET --prefix="$PREFIXMINGW" --disable-shared --without-python
    # shared library required by gtksourceview
    ./autogen.sh --build="$BUILD" --host="$HOST" --target="$TARGET" --prefix="$PREFIXMINGW" --without-python
    # shellcheck disable=SC2086
    log1 make $MAKE_OPT all
    log2 make install
    log2 make clean
    build_post
  fi
}

##### GTK-SOURCEVIEW3 #####

function make_gtk_sourceview3 {
  # Cygwin packet dependencies: intltool
  # Note: this is always built from sources cause of a bug in the cygwin delivery.
  # Just dependencies are only built if we build from sources
  if [ "$GTK_FROM_SOURCES" == "Y" ]; then
    make_gtk3
    make_libxml2
  fi
  build_conf_make_inst  https://download.gnome.org/sources/gtksourceview/3.24  gtksourceview-3.24.11  tar.xz  make_arch_pkg_config
}

##### LN replacement #####

# Note: this does support symlinks, but symlinks require special user rights on Windows.
# ocamlbuild uses symlinks to link the executables in the build folder to the base folder.
# For this purpose hard links are better.

function make_ln {
  if [ ! -f $FLAGFILES/myln.finished ] ; then
    touch $FLAGFILES/myln.started
    mkdir -p myln
    ( cd myln
    cp $PATCHES/ln.c .
    "$TARGET_ARCH-gcc" -DUNICODE -D_UNICODE -DIGNORE_SYMBOLIC -mconsole -o ln.exe ln.c
    install -D ln.exe "$PREFIXCOQ/bin/ln.exe"
    )
    touch $FLAGFILES/myln.finished
  fi
}

##### ARCH-pkg-config replacement #####

# cygwin replaced ARCH-pkg-config with a shell script, which doesn't work e.g. for dune on Windows.
# This builds a binary replacement for the shell script and puts it into the bin_special folder.
# There is no global installation since it is module specific what pkg-config is needed under what name.

function make_arch_pkg_config {
  gcc -DARCH="$TARGET_ARCH" -o bin_special/pkg-config.exe $PATCHES/pkg-config.c
}

##### OCAML #####

function make_ocaml {
  if build_prep https://github.com/ocaml/ocaml/archive 4.08.1 tar.gz 1 ocaml-4.08.1 ; then
    # see https://github.com/ocaml/ocaml/blob/4.08/README.win32.adoc

    # get flexdll sources into folder ./flexdll
    get_expand_source_tar https://github.com/alainfrisch/flexdll/archive 0.37 tar.gz 1 flexdll-0.37 flexdll

    # We don't want to mess up Coq's directory structure so put the OCaml library in a separate folder
    logn configure ./configure --build=i686-pc-cygwin --host="$TARGET_ARCH" --prefix="$PREFIXOCAML" --libdir="$PREFIXOCAML/libocaml"

    log2 make flexdll $MAKE_OPT
    # Note the next command might change after 4.09.x to just make
    # see        https://github.com/ocaml/ocaml/blob/4.09/README.win32.adoc
    # compare to https://github.com/ocaml/ocaml/blob/4.10/README.win32.adoc
    log2 make world.opt $MAKE_OPT
    log2 make flexlink.opt $MAKE_OPT
    log2 make install $MAKE_OPT

    # Move license files and other into into special folder
    if [ "$INSTALLMODE" == "absolute" ] || [ "$INSTALLMODE" == "relocatable" ]; then
      mkdir -p "$PREFIXOCAML/license_readme/ocaml"
      # 4.01 installs these files, 4.02 doesn't. So delete them and copy them from the sources.
      rm -f ./*.txt
      cp LICENSE      "$PREFIXOCAML/license_readme/ocaml/License.txt"
      cp INSTALL.adoc "$PREFIXOCAML/license_readme/ocaml/Install.txt"
      cp README.adoc  "$PREFIXOCAML/license_readme/ocaml/ReadMe.txt"
      cp README.win32.adoc "$PREFIXOCAML/license_readme/ocaml/ReadMeWin32.txt"
      cp VERSION      "$PREFIXOCAML/license_readme/ocaml/Version.txt"
      cp Changes      "$PREFIXOCAML/license_readme/ocaml/Changes.txt"
    fi

    # Since 4.07 this library is part of ocaml
    mkdir -p "$PREFIXOCAML/libocaml/site-lib/seq/"
    cat > "$PREFIXOCAML/libocaml/site-lib/seq/META" <<EOT
name="seq"
version="[distributed with OCaml 4.07 or above]"
description="dummy backward-compatibility package for iterators"
requires=""
EOT

    build_post
  fi
}

##### OCAML EXTRA TOOLS #####

function make_ocaml_tools {
  make_findlib
}

##### OCAML EXTRA LIBRARIES #####

function make_ocaml_libs {
  make_num
  make_findlib
  make_lablgtk
}

##### Ocaml num library #####
function make_num {
  make_ocaml
  # We need this commit due to windows fixed, IMHO this is better than patching v1.1.
  if build_prep https://github.com/ocaml/num/archive 7dd5e935aaa2b902585b3b2d0e55ad9b2442fff0 zip 1 num-1.1-7d; then
    log2 make all
    # log2 make test
    log2 make install
    log2 make clean
    build_post
  fi
}

##### OCAMLBUILD #####

function make_ocamlbuild {
  make_ocaml
  if build_prep https://github.com/ocaml/ocamlbuild/archive 0.14.0 tar.gz 1 ocamlbuild-0.14.0; then
    log2 make configure OCAML_NATIVE=true OCAMLBUILD_PREFIX=$PREFIXOCAML OCAMLBUILD_BINDIR=$PREFIXOCAML/bin OCAMLBUILD_LIBDIR=$PREFIXOCAML/lib
    log1 make $MAKE_OPT
    log2 make install
    build_post
  fi
}

##### FINDLIB Ocaml library manager #####

function make_findlib {
  make_ocaml
  make_ocamlbuild
  # Note: latest is 1.8.1 but http://projects.camlcity.org/projects/dl/findlib-1.8.1/doc/README says this is for OCaml 4.09
  if build_prep https://opam.ocaml.org/1.2.2/archives ocamlfind.1.8.0+opam tar.gz 1 ; then
    logn configure ./configure -bindir "$PREFIXOCAML\\bin" -sitelib "$PREFIXOCAML\\libocaml\\site-lib" -config "$PREFIXOCAML\\etc\\findlib.conf"
    # Note: findlib doesn't support -j 8, so don't pass MAKE_OPT
    log2 make all
    log2 make opt
    log2 make install
    log2 make clean
    # Add Coq install library path to ocamlfind config file
    # $(ocamlfind printconf conf | tr -d '\r') is the name of the config file
    # printf "%q" "$PREFIXCOQ/lib" | sed -e 's/\\/\\\\/g' is the coq lib path double escaped for sed
    sed -i -e 's|path="\(.*\)"|path="\1;'$(printf "%q" "$PREFIXCOQ/lib" | sed -e 's/\\/\\\\/g')'"|' $(ocamlfind printconf conf | tr -d '\r')
    build_post
  fi
}

##### Dune build system #####

function make_dune {
  make_ocaml

  if build_prep https://github.com/ocaml/dune/archive/ 2.0.0 tar.gz 1 dune-2.0.0 ; then

    log2 make release
    log2 make install

    # Dune support libs, we don't install glob and action-plugin as
    # they are not needed by Coq
    logn dune-private-build dune build -p dune-private-libs @install
    logn dune-private-install dune install dune-private-libs

    logn dune-configurator-build dune build -p dune-configurator @install
    logn dune-configurator-install dune install dune-configurator

    logn dune-build-info dune build -p dune-build-info @install
    logn dune-build-info dune install dune-build-info

    build_post
  fi
}

##### MENHIR Ocaml Parser Generator #####

function make_menhir {
  make_ocaml
  make_findlib
  make_ocamlbuild
  if build_prep https://gitlab.inria.fr/fpottier/menhir/-/archive/20200525 menhir-20200525 tar.gz 1 ; then
    # ToDo: don't know if this is the intended / most reliable to do it, but it works
    log2 dune build @install
    log2 dune install menhir menhirSdk menhirLib
    build_post
  fi
}

##### CAMLP5 Ocaml Preprocessor #####

function make_camlp5 {
  make_ocaml
  make_findlib

  if build_prep https://github.com/camlp5/camlp5/archive rel711 tar.gz 1 camlp5-rel711; then
    logn configure ./configure
    # Somehow my virus scanner has the boot.new/SAVED directory locked after the move for a second => repeat until success
    sed -i 's/mv boot.new boot/until mv boot.new boot; do sleep 1; done/' Makefile
    # shellcheck disable=SC2086
    log1 make world.opt $MAKE_OPT
    log2 make install
    cp lib/*.a "$PREFIXOCAML/libocaml/camlp5/"
    log2 make clean
    # For some reason META is not built / copied, but it is required
    log2 make -C etc META
    mkdir -p "$PREFIXOCAML/libocaml/site-lib/camlp5/"
    cp etc/META "$PREFIXOCAML/libocaml/site-lib/camlp5/"
    log2 make clean
    build_post
  fi
}

##### LABLGTK Ocaml GTK binding #####

# Note: when rebuilding lablgtk by deleting the .finished file,
# also delete <root>\usr\x86_64-w64-mingw32\sys-root\mingw\lib\site-lib
# Otherwise make install fails

function make_ocaml_cairo2 {
  if build_prep https://github.com/Chris00/ocaml-cairo/archive 0.6 tar.gz 1 ocaml_cairo2-0.6; then
    make_arch_pkg_config

    log2 dune build cairo2.install
    log2 dune install cairo2
    # See https://github.com/ocaml/dune/issues/2921
    # log2 dune clean
    build_post

  fi
}

function make_lablgtk {
  make_ocaml
  make_findlib
  make_dune
  make_gtk3
  make_gtk_sourceview3
  make_ocaml_cairo2

  if build_prep https://github.com/garrigue/lablgtk/archive  3.0.beta5  tar.gz 1 lablgtk-3.0.beta5 ; then
    make_arch_pkg_config

    # lablgtk3 includes more packages that are not relevant for Coq,
    # such as gtkspell
    log2 dune build -p lablgtk3
    log2 dune install lablgtk3

    log2 dune build -p lablgtk3-sourceview3
    log2 dune install lablgtk3-sourceview3

    # See https://github.com/ocaml/dune/issues/2921
    # log2 dune clean
    build_post
  fi
}

##### Elpi #####

function make_seq {
  make_ocaml
  # since 4.07 this package is part of ocaml

}

function make_re {
  make_ocaml
  make_dune
  make_seq

  if build_prep https://github.com/ocaml/ocaml-re/archive 1.9.0 tar.gz 1 ocaml-re; then

    log2 dune build -p re
    log2 dune install re

    build_post
  fi

}

function make_elpi {
  make_ocaml
  make_findlib
  make_camlp5
  make_dune
  make_re

  if build_prep https://github.com/LPCIC/elpi/archive v1.11.0 tar.gz; then

    log2 make build DUNE_OPTS="-p elpi"
    log2 make install DUNE_OPTS="-p elpi"

    build_post

  fi

}

##### COQ #####

# Copy one DLLfrom cygwin MINGW packages to Coq install folder

function copy_coq_dll {
  if [ "$INSTALLMODE" == "absolute" ] || [ "$INSTALLMODE" == "relocatable" ]; then
    cp "$PREFIXMINGW/bin/$1" "$PREFIXCOQ/bin/$1"
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
  # For running this quickly, just do "cd coq-<ver> ; copy_coq_dlls ; cd .." at the end of this script.
  # Do the same for coqc and ocamlc (usually doesn't result in additional files)

  copy_coq_dll LIBCAIRO-2.DLL
  copy_coq_dll LIBFONTCONFIG-1.DLL
  copy_coq_dll LIBFREETYPE-6.DLL
  copy_coq_dll LIBGDK-3-0.DLL
  copy_coq_dll LIBGDK_PIXBUF-2.0-0.DLL
  copy_coq_dll LIBGLIB-2.0-0.DLL
  copy_coq_dll LIBGOBJECT-2.0-0.DLL
  copy_coq_dll LIBGTK-3-0.DLL
  copy_coq_dll LIBGTKSOURCEVIEW-3.0-1.DLL
  copy_coq_dll LIBPANGO-1.0-0.DLL
  copy_coq_dll LIBATK-1.0-0.DLL
  copy_coq_dll LIBBZ2-1.DLL
  copy_coq_dll LIBCAIRO-GOBJECT-2.DLL
  copy_coq_dll LIBEPOXY-0.DLL
  copy_coq_dll LIBEXPAT-1.DLL
  copy_coq_dll LIBFFI-6.DLL
  copy_coq_dll LIBGIO-2.0-0.DLL
  copy_coq_dll LIBGMODULE-2.0-0.DLL
  copy_coq_dll LIBINTL-8.DLL
  copy_coq_dll LIBPANGOCAIRO-1.0-0.DLL
  copy_coq_dll LIBPANGOWIN32-1.0-0.DLL
  copy_coq_dll LIBPCRE-1.DLL
  copy_coq_dll LIBPIXMAN-1-0.DLL
  copy_coq_dll LIBPNG16-16.DLL
  copy_coq_dll LIBXML2-2.DLL
  copy_coq_dll ZLIB1.DLL
  copy_coq_dll ICONV.DLL
  copy_coq_dll LIBLZMA-5.DLL
  copy_coq_dll LIBPANGOFT2-1.0-0.DLL
  copy_coq_dll LIBHARFBUZZ-0.DLL

  # Depends on if GTK is built from sources
  if [ "$GTK_FROM_SOURCES" == "Y" ]; then
    echo "Building GTK from sources is currently not supported"
    exit 1
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
  find . -type d | while read -r FOLDER ; do
    if [ -e "$PREFIXCOQ/lib/coq/$FOLDER" ] ; then
      install_glob "$FOLDER" '*.cmxa' "$PREFIXCOQ/lib/coq/$FOLDER"
      install_glob "$FOLDER" '*.cmi'  "$PREFIXCOQ/lib/coq/$FOLDER"
      install_glob "$FOLDER" '*.cma'  "$PREFIXCOQ/lib/coq/$FOLDER"
      install_glob "$FOLDER" '*.cmo'  "$PREFIXCOQ/lib/coq/$FOLDER"
      install_glob "$FOLDER" '*.a'    "$PREFIXCOQ/lib/coq/$FOLDER"
      install_glob "$FOLDER" '*.o'    "$PREFIXCOQ/lib/coq/$FOLDER"
    fi
  done
}

# Copy required GTK config and support files
# This must be called from inside the coq build folder!

function copy_coq_gtk {

  glib-compile-schemas $PREFIXMINGW/share/glib-2.0/schemas/
  echo 'gtk-theme-name = "Default"'     >  "$PREFIXMINGW/etc/gtk-3.0/gtkrc"

  if [ "$INSTALLMODE" == "absolute" ] || [ "$INSTALLMODE" == "relocatable" ]; then
    install_glob  "$PREFIXMINGW/etc/gtk-3.0" '*'                                 "$PREFIXCOQ/gtk-3.0"
    install -D -T "$PREFIXMINGW/share/glib-2.0/schemas/gschemas.compiled"        "$PREFIXCOQ/share/glib-2.0/schemas/gschemas.compiled"

    install_glob  "$PREFIXMINGW/share/gtksourceview-3.0/language-specs" '*'      "$PREFIXCOQ/share/gtksourceview-3.0/language-specs"
    install -D -T "ide/coq.lang"                                                 "$PREFIXCOQ/share/gtksourceview-3.0/language-specs/coq.lang"
    install -D -T "ide/coq-ssreflect.lang"                                       "$PREFIXCOQ/share/gtksourceview-3.0/language-specs/coq-ssreflect.lang"

    install_glob  "$PREFIXMINGW/share/gtksourceview-3.0/styles" '*'              "$PREFIXCOQ/share/gtksourceview-3.0/styles"
    install -D -T "ide/coq_style.xml"                                            "$PREFIXCOQ/share/gtksourceview-3.0/styles/coq_style.xml"

    install_rec   "$PREFIXMINGW/share/themes" '*'                                "$PREFIXCOQ/share/themes"

    FOLDERS=""
    # The sizes include all default sizes given in index.theme
    # The types used haven been recorded with ProcMon in an installation with all icons present
    for SIZE in 16x16 22x22 32x32 48x48; do
      for TYPE in \
        actions/bookmark actions/document devices/drive actions/format-text actions/go actions/list \
        actions/media actions/pan actions/process actions/system actions/window \
        mimetypes/text places/folder places/user status/dialog
      do
        CLASS=$(dirname $TYPE)
        ICON=$(basename $TYPE)
        if [[ ! "$FOLDERS" =~ "$SIZE/$CLASS" ]] ;then
          FOLDERS="$FOLDERS$SIZE/$CLASS,"
        fi
        install_rec "/usr/share/icons/Adwaita/$SIZE/$CLASS" "$ICON*"  "$PREFIXCOQ/share/icons/Adwaita/$SIZE/$CLASS"
      done
    done
    echo Folders=$FOLDERS
    install -D -T "/usr/share/icons/Adwaita/index.theme" "$PREFIXCOQ/share/icons/Adwaita/index.theme"
    sed -i "s|^Directories=.*|Directories=$FOLDERS|" "$PREFIXCOQ/share/icons/Adwaita/index.theme"
    gtk-update-icon-cache -f "$PREFIXCOQ/share/icons/Adwaita/"

    # This below item look like a bug in make install
    # if [ -d "$PREFIXCOQ/share/coq/" ] ; then
    #   COQSHARE="$PREFIXCOQ/share/coq/"
    # else
    #   COQSHARE="$PREFIXCOQ/share/"
    # fi

    # mkdir -p "$PREFIXCOQ/ide"
    # mv "$COQSHARE"*.png  "$PREFIXCOQ/ide"
    # rmdir "$PREFIXCOQ/share/coq" || true
  fi
}

# Copy license and other info files

function copy_coq_license {
  if [ "$INSTALLMODE" == "absolute" ] || [ "$INSTALLMODE" == "relocatable" ]; then
    install -D doc/LICENSE                    "$PREFIXCOQ/license_readme/coq/LicenseDoc.txt"
    install -D LICENSE                        "$PREFIXCOQ/license_readme/coq/License.txt"
    install -D plugins/micromega/LICENSE.sos  "$PREFIXCOQ/license_readme/coq/LicenseMicromega.txt"
    # FIXME: this is not the micromega license
    # It only applies to code that was copied into one single file!
    install -D README.md                      "$PREFIXCOQ/license_readme/coq/ReadMe.md"
    install -D INSTALL.md                     "$PREFIXCOQ/license_readme/coq/Install.txt"
    install -D doc/README.md                  "$PREFIXCOQ/license_readme/coq/ReadMeDoc.md" || true
  fi
}

# Main function for creating Coq

function make_coq {
  make_ocaml
  make_num
  make_findlib
  make_lablgtk
  if
    case $COQ_VERSION in
      # e.g. git-v8.6 => download from https://github.com/coq/coq/archive/v8.6.zip
      # e.g. git-trunk => download from https://github.com/coq/coq/archive/trunk.zip
      git-*)
        COQ_BUILD_PATH=/build/coq-${COQ_VERSION}
        build_prep https://github.com/coq/coq/archive "${COQ_VERSION##git-}" zip 1 "coq-${COQ_VERSION}"
        ;;

      # e.g. /cygdrive/d/coqgit
      /*)
        # Todo: --exclude-vcs-ignores doesn't work because tools/coqdoc/coqdoc.sty is excluded => fix .gitignore
        # But this is not a big deal, only 2 files are removed with --exclude-vcs-ignores from a fresch clone
        COQ_BUILD_PATH=/build/coq-local
        tar -zcf $TARBALLS/coq-local.tar.gz --exclude-vcs -C "${COQ_VERSION%/*}" "${COQ_VERSION##*/}"
        build_prep NEVER-DOWNLOADED coq-local tar.gz
        ;;

      # e.g. 8.6 => https://coq.inria.fr/distrib/8.6/files/coq-8.6.tar.gz
      *)
        COQ_BUILD_PATH=/build/coq-$COQ_VERSION
        build_prep "https://coq.inria.fr/distrib/V$COQ_VERSION/files" "coq-$COQ_VERSION" tar.gz
        ;;
    esac
  then
    if [ "$INSTALLMODE" == "relocatable" ]; then
      # HACK: for relocatable builds, first configure with ./, then build but before install reconfigure with the real target path
      logn configure ./configure -with-doc no -prefix ./ -libdir ./lib/coq -mandir ./man
    elif [ "$INSTALLMODE" == "absolute" ]; then
      logn configure ./configure -with-doc no -prefix "$PREFIXCOQ" -libdir "$PREFIXCOQ/lib/coq" -mandir "$PREFIXCOQ/man"
    else
      logn configure ./configure -with-doc no -prefix "$PREFIXCOQ"
    fi

    # The windows resource compiler binary name is hard coded
    sed -i "s/i686-w64-mingw32-windres/$TARGET_ARCH-windres/" Makefile.build
    sed -i "s/i686-w64-mingw32-windres/$TARGET_ARCH-windres/" Makefile.ide || true

    # 8.4x doesn't support parallel make
    if [[ $COQ_VERSION == 8.4* ]] ; then
      log1 make
    else
      # shellcheck disable=SC2086
      log1 make $MAKE_OPT
    fi

    if [ "$INSTALLMODE" == "relocatable" ]; then
      logn reconfigure ./configure -with-doc no -prefix "$PREFIXCOQ" -libdir "$PREFIXCOQ/lib/coq" -mandir "$PREFIXCOQ/man"
    fi

    log2 make install
    log1 copy_coq_dlls
    log1 copy_coq_gtk

    if [ "$INSTALLOCAML" == "Y" ]; then
      copy_coq_objects
    fi

    log1 copy_coq_license

    # make clean seems to be broken for 8.5pl2
    # 1.) find | xargs fails on cygwin, can be fixed by sed -i 's|\| xargs rm -f|-exec rm -fv \{\} \+|' Makefile
    # 2.) clean of test suites fails with "cannot run complexity tests (no bogomips found)"
    # make clean

    # Copy these files somewhere the plugin builds can find them
    logn copy-basic-overlays cp dev/ci/ci-basic-overlay.sh /build/
    logn copy-user-overlays cp -r dev/ci/user-overlays /build/

    build_post
  fi

  load_overlay_data
}

##### GNU Make for MinGW #####

function make_mingw_make {
  if build_prep http://ftp.gnu.org/gnu/make make-4.2 tar.bz2 ; then
    # The config.h.win32 file is fine - don't edit it
    # We need to copy the mingw gcc here as "gcc" - then the batch file will use it
    cp "/usr/bin/${ARCH}-w64-mingw32-gcc-6.4.0.exe" ./gcc.exe
    # By some magic cygwin bash can run batch files
    logn build ./build_w32.bat gcc
    # Copy make to Coq folder
    cp GccRel/gnumake.exe "$PREFIXCOQ/bin/make.exe"
    build_post
  fi
}

##### GNU binutils for native OCaml #####

function make_binutils {
  if build_prep http://ftp.gnu.org/gnu/binutils binutils-2.27 tar.gz ; then
    logn configure ./configure --build="$BUILD" --host="$HOST" --target="$TARGET" --prefix="$PREFIXCOQ" --program-prefix="$TARGET-"
    # shellcheck disable=SC2086
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
    mkdir -p "$PREFIXCOQ/mingw/include"

    # See https://gcc.gnu.org/install/configure.html
    logn configure ./configure --build="$BUILD" --host="$HOST" --target="$TARGET" \
        --prefix="$PREFIXCOQ" --program-prefix="$TARGET-" --disable-win32-registry --with-sysroot="$PREFIXCOQ" \
        --enable-languages=c --disable-nls \
        --disable-libsanitizer --disable-libssp --disable-libquadmath --disable-libgomp --disable-libvtv --disable-lto
        # --disable-decimal-float seems to be required
        # --with-sysroot="$PREFIXMINGW"  results in configure error that this is not an absolute path
    # shellcheck disable=SC2086
    log1 make $MAKE_OPT
    log2 make install
    # log2 make clean
    build_post
  fi
}

##### Get sources for Cygwin MinGW packages #####

function get_cygwin_mingw_sources {
  if [ ! -f $FLAGFILES/cygwin_mingw_sources.finished ] ; then
    touch $FLAGFILES/cygwin_mingw_sources.started

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

    grep "mingw" /etc/setup/installed.db | sed 's/\.tar\.bz2 [0-1]$//' | sed 's/ /\//'  | while read -r ARCHIVE ; do
      local ARCHIVEESC=${ARCHIVE//+/\\+}
      local SOURCE
      SOURCE=$(grep -E -A 1 "install: ($CYGWINARCH|noarch)/release/[-+_/a-z0-9]*$ARCHIVEESC" $TARBALLS/setup.ini | tail -1 | cut -d " " -f 2)
      local SOURCEFILE=${SOURCE##*/}

      # Get the source file (either from the source cache or online)
      if [ ! -f "$TARBALLS/$SOURCEFILE" ] ; then
        if [ -f "$SOURCE_LOCAL_CACHE_CFMT/$SOURCEFILE" ] ; then
          cp "$SOURCE_LOCAL_CACHE_CFMT/$SOURCEFILE" $TARBALLS
        else
          wget --progress=dot:giga "$CYGWIN_REPOSITORY/$SOURCE"
          mv "$SOURCEFILE" "$TARBALLS"
          # Save the source archive in the source cache
          if [ -d "$SOURCE_LOCAL_CACHE_CFMT" ] ; then
            cp "$TARBALLS/$SOURCEFILE" "$SOURCE_LOCAL_CACHE_CFMT"
          fi
        fi
      fi

    done

    touch $FLAGFILES/cygwin_mingw_sources.finished
  fi
}

##### Coq Windows Installer #####

function make_coq_installer {
  make_coq
  get_cygwin_mingw_sources

  # Prepare the file lists for the installer. We created to file list dumps of the target folder during the build:
  # ocaml: ocaml + menhir + camlp5 + findlib
  # ocaml_coq: as above + coq
  # ocaml_coq_addons: as above + lib/user-contrib/*

  # Create coq file list as ocaml_coq / ocaml
  diff_files coq ocaml_coq ocaml

  # Filter out object files
  filter_files coq_objects coq '\.(cmxa|cmi|cma|cmo|a|o)$'

  # Filter out plugin object files
  filter_files coq_objects_plugins coq_objects '/lib/coq/plugins/.*\.(cmxa|cmi|cma|cmo|a|o)$'

  # Coq objects objects required for plugin development = coq objects except those for pre installed plugins
  diff_files coq_plugindev coq_objects coq_objects_plugins

  # Addons (TODO: including objects that could go to the plugindev thing, but
  # then one would have to make that package depend on this one, so not
  # implemented yet)
  diff_files coq_addons ocaml_coq_addons ocaml_coq

  # Coq files, except objects needed only for plugin development
  diff_files coq_base coq coq_plugindev

  # Convert section files to NSIS format
  files_to_nsis coq_base
  files_to_nsis coq_addons
  files_to_nsis coq_plugindev
  files_to_nsis ocaml

  # Get and extract NSIS Binaries
  if build_prep http://downloads.sourceforge.net/project/nsis/NSIS%202/2.51 nsis-2.51 zip ; then
    NSIS=$(pwd)/makensis.exe
    chmod u+x "$NSIS"
    # Change to Coq folder
    cd "$COQ_BUILD_PATH"
    # Copy patched nsi file
    cp ../patches/coq_new.nsi dev/nsis
    cp ../patches/StrRep.nsh dev/nsis
    cp ../patches/ReplaceInFile.nsh dev/nsis
    VERSION=$(grep '^VERSION=' config/Makefile | cut -d = -f 2 | tr -d '\r')
    cd dev/nsis
    logn nsis-installer "$NSIS" -DVERSION="$VERSION" -DARCH="$ARCH" -DCOQ_SRC_PATH="$PREFIXCOQ" -DCOQ_ICON=..\\..\\ide\\coq.ico -DCOQ_ADDONS="$COQ_ADDONS" coq_new.nsi

    build_post
  fi
}

###################### ADDON COQ LIBRARIES / PLUGINS / TOOLS #####################

# The bignums library
# Provides BigN, BigZ, BigQ that used to be part of Coq standard library

function make_addon_bignums {
  installer_addon_dependency bignums
  if build_prep_overlay bignums; then
    installer_addon_section bignums "Bignums" "Coq library for fast arbitrary size numbers" ""
    # To make command lines shorter :-(
    echo 'COQ_SRC_SUBDIRS:=$(filter-out plugins/%,$(COQ_SRC_SUBDIRS)) plugins/syntax' >> Makefile.coq.local
    log1 make $MAKE_OPT all
    log2 make install
    build_post
  fi
}

# Equations plugin
# A function definition plugin

function make_addon_equations {
  installer_addon_dependency equations
  if build_prep_overlay equations; then
    installer_addon_section equations "Equations" "Coq plugin for defining functions by equations" ""
    # Note: PATH is automatically saved/restored by build_prep / build_post
    PATH=$COQBIN:$PATH
    logn coq_makefile ${COQBIN}coq_makefile -f _CoqProject -o Makefile
    log1 make $MAKE_OPT
    log2 make install
    build_post
  fi
}

# mathcomp - ssreflect and mathematical components library

function make_addon_mathcomp {
  installer_addon_dependency mathcomp
  if build_prep_overlay mathcomp; then
    installer_addon_section mathcomp "Math-Components" "Coq library with mathematical components" ""
    cd mathcomp
    log1 make $MAKE_OPT
    log2 make install
    build_post
  fi
}

# ssreflect part of mathcomp

function make_addon_ssreflect {
  # if mathcomp addon is requested, build this instead
  if [[ "$COQ_ADDONS" == *mathcomp* ]]; then
    make_addon_mathcomp
  else
    # Note: since either mathcomp or ssreflect is defined, it is fine to name both mathcomp
    installer_addon_dependency ssreflect
    if build_prep_overlay mathcomp; then
      installer_addon_section ssreflect "SSReflect" "Coq support library for small scale reflection plugin" ""
      cd mathcomp
      logn make-makefile  make Makefile.coq
      logn make-ssreflect make $MAKE_OPT -f Makefile.coq ssreflect/all_ssreflect.vo
      logn make-install   make -f Makefile.coq install
      build_post
    fi
  fi
}

# UniCoq plugin
# An alternative unification algorithm
function make_addon_unicoq {
  installer_addon_dependency unicoq
  if build_prep_overlay unicoq; then
    installer_addon_section unicoq "Unicoq" "Coq plugin for an enhanced unification algorithm" ""
    log1 coq_makefile -f Make -o Makefile
    log1 make $MAKE_OPT
    log2 make install
    build_post
  fi
}

# Mtac2 plugin
# An alternative typed tactic language
function make_addon_mtac2 {
  installer_addon_dependency_beg mtac2
  make_addon_unicoq
  installer_addon_dependency_end
  if build_prep_overlay mtac2; then
    installer_addon_section mtac2 "Mtac-2" "Coq plugin for a typed tactic language for Coq." ""
    log1 coq_makefile -f _CoqProject -o Makefile
    log1 make $MAKE_OPT
    log2 make install
    build_post
  fi
}

# Menhir parser generator

function make_addon_menhir {
  make_menhir
  # If COQ and OCaml are installed to the same folder, there is nothing to do
  installer_addon_dependency menhir
  if [ "$PREFIXOCAML" != "$PREFIXCOQ" ] ; then
    # Just install menhir files required for COQ to COQ target folder
    if [ ! -f "$FLAGFILES/menhir-addon.finished" ] ; then
      installer_addon_section menhir "Menhir" "Menhir parser generator windows executable and libraries" ""
      LOGTARGET=menhir-addon
      touch "$FLAGFILES/menhir-addon.started"
      # Menhir executable
      install_glob "$PREFIXOCAML/bin" 'menhir.exe' "$PREFIXCOQ/bin/"
      # Menhir PDF doc
      install_glob "$PREFIXOCAML/doc/menhir/" '*.pdf' "$PREFIXCOQ/doc/menhir/"
      touch "$FLAGFILES/menhir-addon.finished"
      LOGTARGET=other
      installer_addon_end
    fi
  fi
}

# COQ library for Menhir

function make_addon_menhirlib {
  installer_addon_dependency menhirlib
  if build_prep_overlay menhirlib; then
    installer_addon_section menhirlib "Menhirlib" "Coq support library for using Menhir generated parsers in Coq" ""
    # The supplied makefiles don't work in any way on cygwin
    # ToDo: dune also doesn't seem to work for the coq files
    cd coq-menhirlib/src
    echo -R . MenhirLib > _CoqProject
    ls -1 *.v >> _CoqProject
    log1 coq_makefile -f _CoqProject -o Makefile.coq
    log1 make -f Makefile.coq $MAKE_OPT all
    logn make-install make -f Makefile.coq install
    build_post
  fi
}

# CompCert

function make_addon_compcert {
  installer_addon_dependency_beg compcert
  make_menhir
  make_addon_menhirlib
  installer_addon_dependency_end
  if build_prep_overlay compcert; then
    installer_addon_section compcert "CompCert" "ATTENTION: THIS IS NOT OPEN SOURCE! CompCert verified C compiler and Clightgen (required for using VST for your own code)" "off"
    logn configure ./configure -ignore-coq-version -clightgen -prefix "$PREFIXCOQ" -coqdevdir "$PREFIXCOQ/lib/coq/user-contrib/compcert" x86_32-cygwin
    log1 make $MAKE_OPT
    log2 make install
    logn install-license-1 install -D -T  "LICENSE" "$PREFIXCOQ/lib/coq/user-contrib/compcert/LICENSE"
    logn install-license-2 install -D -T  "LICENSE" "$PREFIXCOQ/lib/compcert/LICENSE"
    build_post
  fi
}

# Princeton VST

function install_addon_vst {
    VSTDEST="$PREFIXCOQ/lib/coq/user-contrib/VST"

    # Install VST .v, .vo, .c and .h files
    install_rec compcert '*.v' "$VSTDEST/compcert/"
    install_rec compcert '*.vo' "$VSTDEST/compcert/"
    install_glob "msl" '*.v' "$VSTDEST/msl/"
    install_glob "msl" '*.vo' "$VSTDEST/msl/"
    install_glob "sepcomp" '*.v' "$VSTDEST/sepcomp/"
    install_glob "sepcomp" '*.vo' "$VSTDEST/sepcomp/"
    install_glob "floyd" '*.v' "$VSTDEST/floyd/"
    install_glob "floyd" '*.vo' "$VSTDEST/floyd/"
    install_glob "progs" '*.v' "$VSTDEST/progs/"
    install_glob "progs" '*.c' "$VSTDEST/progs/"
    install_glob "progs" '*.h' "$VSTDEST/progs/"
    install_glob "veric" '*.v' "$VSTDEST/veric/"
    install_glob "veric" '*.vo' "$VSTDEST/veric/"

    # Install VST documentation files
    install_glob "." 'LICENSE' "$VSTDEST"
    install_glob "." '*.md' "$VSTDEST"
    install_glob "compcert" '*' "$VSTDEST/compcert"
    install_glob "doc" '*.pdf' "$VSTDEST/doc"

    # Install VST _CoqProject files
    install_glob "." '_CoqProject*' "$VSTDEST"
    install_glob "." '_CoqProject-export' "$VSTDEST/progs"
}

function vst_patch_compcert_refs {
  find . -type f -name '*.v' -print0 | xargs -0 sed -E -i \
    -e 's/(Require\s+(Import\s+|Export\s+)*)compcert\./\1VST.compcert./g' \
    -e 's/From compcert Require/From VST.compcert Require/g'
}

function make_addon_vst {
  installer_addon_dependency vst
  if build_prep_overlay vst; then
    installer_addon_section vst "VST" "ATTENTION: SOME INCLUDED COMPCERT PARTS ARE NOT OPEN SOURCE! Verified Software Toolchain for verifying C code" "off"
    # log1 coq_set_timeouts_1000
    log1 vst_patch_compcert_refs
    # The usage of the shell variable ARCH in VST collides with the usage in this shellscript
    logn make env -u ARCH make IGNORECOQVERSION=true $MAKE_OPT
    log1 install_addon_vst
    build_post
  fi
}

# coquelicot Real analysis

function make_addon_coquelicot {
  installer_addon_dependency_beg coquelicot
  make_addon_ssreflect
  installer_addon_dependency_end
  if build_prep_overlay coquelicot; then
    installer_addon_section coquelicot "Coquelicot" "Coq library for real analysis" ""
    logn autogen ./autogen.sh
    logn configure ./configure --libdir="$PREFIXCOQ/lib/coq/user-contrib/Coquelicot"
    logn remake ./remake
    logn remake-install ./remake install
    build_post
  fi
}

# AAC associative / commutative rewriting

function make_addon_aactactics {
  installer_addon_dependency aac
  if build_prep_overlay aac_tactics; then
    installer_addon_section aac "AAC" "Coq plugin for extensible associative and commutative rewriting" ""
    log1 make $MAKE_OPT
    log2 make install
    build_post
  fi
}

# extlib

function make_addon_extlib {
  installer_addon_dependency extlib
  if build_prep_overlay ext_lib; then
    installer_addon_section extlib "Ext-Lib" "Coq library with many reusable general purpose components" ""
    log1 make $MAKE_OPT
    log2 make install
    build_post
  fi
}

# SimpleIO

function make_addon_simple_io {
  installer_addon_dependency simpleIO
  if build_prep_overlay simple_io; then
    installer_addon_section simpleIO "SimpleIO" "Coq plugin for reading and writing files directly from Coq code" ""
    log1 make $MAKE_OPT
    log2 make install
    build_post
  fi
}

# Quickchick Randomized Property-Based Testing Plugin for Coq

function make_addon_quickchick {
  installer_addon_dependency_beg quickchick
  make_addon_ssreflect
  make_addon_extlib
  make_addon_simple_io
  make_ocamlbuild
  installer_addon_dependency_end
  if build_prep_overlay quickchick; then
    installer_addon_section quickchick "QuickChick" "Coq plugin for randomized testing and counter example search" ""
    log1 make $MAKE_OPT
    log2 make install
    build_post
  fi
}

# Flocq: Floating point library

function make_addon_flocq {
  if build_prep_overlay flocq; then
    installer_addon_section flocq "Flocq" "Coq library for floating point arithmetic" ""
    log1 autoconf
    logn configure ./configure
    logn remake ./remake --jobs=$MAKE_THREADS
    logn install ./remake install
    build_post
  fi
}

# Coq-Interval: interval arithmetic and inequality proofs

function make_addon_interval {
  installer_addon_dependency_beg interval
  make_addon_mathcomp
  make_addon_coquelicot
  make_addon_bignums
  make_addon_flocq
  installer_addon_dependency_end
  if build_prep_overlay interval; then
    installer_addon_section interval "Interval" "Coq library and tactic for proving real inequalities" ""
    logn autogen ./autogen.sh
    logn configure ./configure
    logn remake ./remake --jobs=$MAKE_THREADS
    logn install ./remake install
    build_post
  fi
}

# Gappa: Automatic generation of arithmetic proofs (mostly on limited precision arithmetic)

function install_boost {
  # The extra tar parameter extracts only the boost headers, not the boost library source code (which is huge and takes a long time)
  if build_prep https://dl.bintray.com/boostorg/release/1.69.0/source boost_1_69_0 tar.gz 1 boost_1_69_0 boost boost_1_69_0/boost; then
    # Move extracted boost folder where mingw-gcc can find it
    mv boost /usr/$TARGET_ARCH/sys-root/mingw/include
    build_post
  fi
}

function copy_gappa_dlls {
  copy_coq_dll LIBGMP-10.DLL
  copy_coq_dll LIBMPFR-6.DLL
  copy_coq_dll LIBSTDC++-6.DLL
}

function make_addon_gappa_tool {
  install_boost
  if build_prep_overlay gappa_tool; then
    installer_addon_section gappa_tool "Gappa tool" "Stand alone tool for automated generation of numerical arithmetic proofs" ""
    logn autogen ./autogen.sh
    logn configure ./configure --build="$HOST" --host="$HOST" --target="$TARGET" --prefix="$PREFIXCOQ"
    logn remake ./remake --jobs=$MAKE_THREADS
    logn install ./remake -d install
    log1 copy_gappa_dlls
    build_post
  fi
}

function make_addon_gappa {
  make_camlp5
  installer_addon_dependency_beg gappa
  make_addon_gappa_tool
  make_addon_flocq
  installer_addon_dependency_end
  if build_prep_overlay gappa_plugin ; then
    installer_addon_section gappa "Gappa plugin" "Coq plugin for the Gappa tool" ""
    logn autogen ./autogen.sh
    logn configure ./configure
    logn remake ./remake
    logn install ./remake install
    build_post
  fi
}

# Elpi: extension language for Coq based. It lets one define commands in tactics
# in a high level programming language with support for binders and unification
# variables.

function make_addon_elpi {
  make_elpi
  installer_addon_dependency elpi
  if build_prep_overlay elpi ; then
    installer_addon_section elpi "Elpi extension language" "Coq plugin for the Elpi extension language" ""
    logn build make
    logn installe make install
    build_post
  fi
}

# Hierarchy Builder: high level language to declare a hierarchy of structures
# compiled down to records and canonical structures.

function make_addon_HB {
  installer_addon_dependency_beg elpi_hb
  make_addon_elpi
  installer_addon_dependency_end
  if build_prep_overlay elpi_hb ; then
    installer_addon_section elpi_hb "Hierarchy Builder" "Coq library to declare algebraic hierarchies" ""
    logn build make
    logn install make install VFILES=structures.v
    build_post
  fi
}

# Main function for building addons

function make_addons {
  # Note: ':' is the empty command, which does not produce any output
  : > "/build/filelists/addon_dependencies.nsh"
  : > "/build/filelists/addon_strings.nsh"
  : > "/build/filelists/addon_descriptions.nsh"
  : > "/build/filelists/addon_sections.nsh"

  for addon in $COQ_ADDONS; do
    "make_addon_$addon"
  done

  sort -u -o "/build/filelists/addon_dependencies.nsh" "/build/filelists/addon_dependencies.nsh"
}

###################### TOP LEVEL BUILD #####################

ocamlfind list || true

make_sed
make_ocaml
make_ocaml_tools
make_ocaml_libs

list_files ocaml

make_coq

if [ "$INSTALLMAKE" == "Y" ] ; then
  make_mingw_make
fi

list_files ocaml_coq

make_addons

list_files_always ocaml_coq_addons

if [ "$MAKEINSTALLER" == "Y" ] ; then
  make_coq_installer
fi
