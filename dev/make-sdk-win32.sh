#!/bin/bash

# To run this script install cygwin by running setup-x86.exe from cygwin.com
# Install the standard packages plus wget.  Then run this script.

# Sworn by Enrico Tassi <enrico.tassi@inra.fr>
# Modified to support other directories and almost support spaces in paths
# by Jason Gross <jgross@mit.edu>
# License: Expat/MIT http://opensource.org/licenses/MIT

# This script reads the following environment variables:
# VERBOSE     - set to non-empty to have wget/this script be more verbose, for debugging purposes
# BASE        - set to non-empty to give a different location for the zip file, e.g., if /cygdrive/c is full or doesn't exist

set -e
if [ ! -z "$VERBOSE" ]
then
  set -x
fi

# Resources
ocaml=ocaml-4.01.0-i686-mingw64-installer3.exe
glib=base-windows-0.18.1.1.13.356@BUILD_ec06e9.txz
gtk=base-gtk-2.24.18.1.58@BUILD_594ca8.txz
lablgtk=lablgtk-2.18.0.tar.gz
camlp5=camlp5-6.11.tgz
nsis=nsis-2.46-setup.exe

ocaml_URL='http://yquem.inria.fr/~protzenk/caml-installer/'$ocaml
lablgtk_URL='https://forge.ocamlcore.org/frs/download.php/1261/'$lablgtk
glib_URL='http://dl.arirux.de/5/binaries32/'$glib
gtk_URL='http://dl.arirux.de/5/binaries32/'$gtk
camlp5_URL='http://pauillac.inria.fr/~ddr/camlp5/distrib/src/'$camlp5
nsis_URL='http://netcologne.dl.sourceforge.net/project/nsis/NSIS%202/2.46/'$nsis

cygwin=setup-${HOSTTYPE/i6/x}.exe
cygwin_URL='http://cygwin.com/'$cygwin
cygwin_PKGS=p7zip,zip,sed,make,mingw64-i686-gcc-g++,mingw64-i686-gcc-core,mingw64-i686-gcc,patch,rlwrap,libreadline6,diffutils

has_spaces() {
    test -z "$2"
}
# utilities
# http://www.dependencywalker.com/depends22_x86.zip

# The SDK itself
REVISION=85-1
# support for working on computers that don't have a C: drive
if [ -z "$BASE" ]
then
  TRUE_BASE=/cygdrive/c
else
  # get absolute path
  TRUE_BASE="$(readlink -f "$BASE")"
fi
BASE="$TRUE_BASE/CoqSDK-$REVISION"

if [ -z "$VERBOSE" ]
then
  WGET_ARGS="-N -q"
else
  WGET_ARGS="-N"
fi

# Windows has a version of FIND in C:/Windows/system32/find, and we don't want to use that
if [ -x /usr/bin/find ]
then
  FIND=/usr/bin/find
else
  echo "WARNING: /usr/bin/find does not exist.  Falling back on:"
  which find
  FIND=find
fi

WGET_ARGS="-N -q"

if [ "$(has_spaces $BASE; echo $?)" -ne 0 ]; then
  echo "ERROR: The current base directory ($BASE) has spaces."
  echo "ERROR: building lablgtk would fail."
  exit 1
fi

cyg_install() {
  if [ ! -e "$cygwin" ]; then wget $WGET_ARGS "$cygwin_URL"; fi
  chmod a+x "$cygwin"
  cygstart -w "$cygwin" -q -P $@
}

sanity_check() {
  echo "Check: wget."
  (which wget) || \
	  (echo "Please install wget using the cygwin installer and retry.";\
	   exit 1)
  echo "Check: 7z, gcc.  If it fails wait for cygwin to complete and retry"
  (which 7z && which i686-w64-mingw32-gcc) || \
	  (echo "Some cygwin package is not installed.";\
	   echo "Please wait for cygwin to finish and retry.";\
	   cyg_install $cygwin_PKGS;\
	   exit 1)
}

install_base() {
  echo "Setting up $BASE"
  rm -rf "$BASE"
  mkdir -p "$BASE"
}

make_environ() {
  echo "Setting up $BASE/environ"
  pushd "$BASE" >/dev/null
  cat > environ <<- EOF
	cyg_install() {
	  if [ ! -e "$cygwin" ]; then wget $WGET_ARGS "$cygwin_URL"; fi
	  chmod a+x "$cygwin"
	  cygstart -w "$cygwin" -q -P \$@
	}
	# Sanity checks: is the mingw64-i686-gcc package installed?
	(which i686-w64-mingw32-gcc && which make && which sed) || \\
		(echo "Some cygwin package is not installed.";\\
	         echo "Please wait for cygwin to finish and retry.";\\
	 	 cyg_install $cygwin_PKGS;\\
		 exit 1) || exit 1

	export BASE="\$( cd "\$( dirname "\${BASH_SOURCE[0]}" )" && pwd )"
	export PATH="\$BASE/bin:\$PATH"
	export OCAMLLIB="\$(cygpath -m "\$BASE")/lib"
	export OCAMLFIND_CONF="\$(cygpath -m "\$BASE")/etc/findlib.conf"
	sed s"|@BASE@|\$(cygpath -m "\$BASE")|g" "\$BASE/lib/ld.conf.in" \\
	        > "\$BASE/lib/ld.conf"
	sed s"|@BASE@|\$(cygpath -m "\$BASE")|g" "\$BASE/lib/topfind.in" \\
	        > "\$BASE/lib/topfind"
	sed s"|@BASE@|\$(cygpath -m "\$BASE")|g" "\$BASE/etc/findlib.conf.in" \\
	        > "\$BASE/etc/findlib.conf"
	echo "Good.  You can now build Coq and Coqide from cygwin."
	EOF
  popd >/dev/null
}

download() {
  echo "Downloading some software:"
  if [ ! -e "$ocaml" ]; then
    echo "- downloading OCaml..."
    wget $WGET_ARGS "$ocaml_URL"
  fi
  chmod a+x "$ocaml"
  if [ ! -e "$lablgtk" ]; then
    echo "- downloading lablgtk..."
    wget $WGET_ARGS --no-check-certificate "$lablgtk_URL"
  fi
  if [ ! -e "$gtk" ]; then
    echo "- downloading gtk..."
    wget $WGET_ARGS "$gtk_URL"
  fi
  if [ ! -e "$glib" ]; then
    echo "- downloading glib..."
    wget $WGET_ARGS "$glib_URL"
  fi
  if [ ! -e "$camlp5" ]; then
    echo "- downloading camlp5..."
    wget $WGET_ARGS "$camlp5_URL"
  fi
  if [ ! -e "$nsis" ]; then
    echo "- downloading nsis..."
    wget $WGET_ARGS "$nsis_URL"
  fi
}

cleanup() {
  rm -rf tmp build
}

install_gtk() {
  echo "Installing $glib"
  tar -xJf "$glib" -C "$BASE"
  echo "Installing $gtk"
  tar -xJf "$gtk" -C "$BASE"
}

install_ocaml() {
  echo "Installing $ocaml"
  mkdir -p tmp
  7z -otmp x "$ocaml" >/dev/null
  cp -r tmp/\$_OUTDIR/bin "$BASE/"
  cp -r tmp/bin "$BASE/"
  cp -r tmp/\$_OUTDIR/lib "$BASE/"
  cp -r tmp/lib "$BASE/"
  cp -r tmp/\$_OUTDIR/etc "$BASE/"
  "$FIND" "$BASE" -name '*.dll' -o -name '*.exe' | tr '\n' '\0' \
	  | xargs -0 chmod a+x
  mv "$BASE/lib/topfind" "$BASE/lib/topfind.in"
  sed -i 's|@SITELIB@|@BASE@/lib/site-lib|g' "$BASE/lib/topfind.in"
  cat > "$BASE/lib/ld.conf.in" <<- EOF
	@BASE@/lib
	@BASE@/lib/stublibs
	EOF
  cat > "$BASE/etc/findlib.conf.in" <<- EOF
	destdir="@BASE@/lib/site-lib"
	path="@BASE@/lib/site-lib"
	stdlib="@BASE@/lib"
	ldconf="@BASE@/lib/ld.conf"
	ocamlc="ocamlc.opt"
	ocamlopt="ocamlopt.opt"
	ocamldep="ocamldep.opt"
	ocamldoc="ocamldoc.opt"
	EOF
  cp "$BASE/lib/topdirs.cmi" "$BASE/lib/compiler-libs/"
}

build_install_lablgtk() {
  echo "Building $lablgtk"
  mkdir -p build
  tar -xzf "$lablgtk" -C build
  cd build/lablgtk-*
  patch -p1 <<EOT
--- lablgtk-2.18.0/src/glib.mli	2013-10-01 01:31:50.000000000 -0700
+++ lablgtk-2.18.0.new/src/glib.mli	2013-12-06 11:57:34.203675200 -0800
@@ -75,6 +75,7 @@
   type condition = [ \`ERR | \`HUP | \`IN | \`NVAL | \`OUT | \`PRI]
   type id
   val channel_of_descr : Unix.file_descr -> channel
+  val channel_of_descr_socket : Unix.file_descr -> channel
   val add_watch :
     cond:condition list -> callback:(condition list -> bool) -> ?prio:int -> channel -> id
   val remove : id -> unit
--- lablgtk-2.18.0/src/glib.ml	2013-10-01 01:31:50.000000000 -0700
+++ lablgtk-2.18.0.new/src/glib.ml	2013-12-06 11:57:53.070804800 -0800
@@ -72,6 +72,8 @@
   type id
   external channel_of_descr : Unix.file_descr -> channel
     = "ml_g_io_channel_unix_new"
+  external channel_of_descr_socket : Unix.file_descr -> channel
+    = "ml_g_io_channel_unix_new_socket"
   external remove : id -> unit = "ml_g_source_remove"
   external add_watch :
     cond:condition list -> callback:(condition list -> bool) -> ?prio:int -> channel -> id
--- lablgtk-2.18.0/src/ml_glib.c	2013-10-01 01:31:50.000000000 -0700
+++ lablgtk-2.18.0.new/src/ml_glib.c	2013-12-10 02:03:33.940371800 -0800
@@ -25,6 +25,8 @@
 #include <string.h>
 #include <locale.h>
 #ifdef _WIN32
+/* to kill a #warning: include winsock2.h before windows.h */
+#include <winsock2.h>
 #include "win32.h"
 #include <wtypes.h>
 #include <io.h>
@@ -38,6 +40,11 @@
 #include <caml/callback.h>
 #include <caml/threads.h>

+#ifdef _WIN32
+/* for Socket_val */
+#include <caml/unixsupport.h>
+#endif
+
 #include "wrappers.h"
 #include "ml_glib.h"
 #include "glib_tags.h"
@@ -325,14 +332,23 @@

 #ifndef _WIN32
 ML_1 (g_io_channel_unix_new, Int_val, Val_GIOChannel_noref)
+CAMLprim value ml_g_io_channel_unix_new_socket (value arg1) {
+  return Val_GIOChannel_noref (g_io_channel_unix_new (Int_val (arg1)));
+}

 #else
 CAMLprim value ml_g_io_channel_unix_new(value wh)
 {
   return Val_GIOChannel_noref
-    (g_io_channel_unix_new
+    (g_io_channel_win32_new_fd
      (_open_osfhandle((long)*(HANDLE*)Data_custom_val(wh), O_BINARY)));
 }
+
+CAMLprim value ml_g_io_channel_unix_new_socket(value wh)
+{
+  return Val_GIOChannel_noref
+    (g_io_channel_win32_new_socket(Socket_val(wh)));
+}
 #endif

 static gboolean ml_g_io_channel_watch(GIOChannel *s, GIOCondition c,
EOT
  #sed -i s'/$PKG_CONFIG/"$PKG_CONFIG"/g' configure
  #sed -i s'/""$PKG_CONFIG""/"$PKG_CONFIG"/g' configure
  ./configure --disable-gtktest --prefix="$(cygpath -m "$BASE")" \
	  >log-configure 2>&1
  sed -i 's?\\?/?g' config.make
  make >log-make 2>&1
  make opt >>log-make 2>&1
  #echo "Testing $lablgtk"
  #cd src
  #./lablgtk2 ../examples/calc.ml
  #./lablgtk2 -all ../examples/calc.ml
  #cd ..
  echo "Installing $lablgtk"
  make install >>log-make 2>&1
  cd ../..
}

build_install_camlp5() {
  echo "Building $camlp5"
  mkdir -p build
  tar -xzf "$camlp5" -C build
  cd build/camlp5-*
  ./configure >log-configure 2>&1
  sed -i 's/EXT_OBJ=.obj/EXT_OBJ=.o/' config/Makefile
  sed -i 's/EXT_LIB=.lib/EXT_LIB=.a/' config/Makefile
  make world.opt >log-make 2>&1
  echo "Installing $camlp5"
  make install >>log-make 2>&1
  cd ../..
}

install_nsis() {
  echo "Installing $nsis"
  rm -rf tmp
  mkdir -p tmp
  7z -otmp x $nsis >/dev/null
  mkdir "$BASE/NSIS"
  cp -r tmp/\$_OUTDIR/* "$BASE/NSIS"
  rm -rf tmp/\$_OUTDIR
  rm -rf tmp/\$PLUGINSDIR
  cp -r tmp/* "$BASE/NSIS"
}

zip_sdk() {
  echo "Generating CoqSDK-${REVISION}.zip"
  here="`pwd`"
  cd "$BASE/.."
  rm -f "$here/CoqSDK-${REVISION}.zip"
  zip -q -r "$here/CoqSDK-${REVISION}.zip" "$(basename "$BASE")"
  cd "$here"
}

diet_sdk() {
  rm -rf "$BASE"/+*
  rm -rf "$BASE"/bin/camlp4*
  rm -rf "$BASE"/lib/camlp4/
  rm -rf "$BASE"/lib/site-lib/camlp4/
}

victory(){
  echo "Output file: CoqSDK-${REVISION}.zip "\
	  "(`du -sh CoqSDK-${REVISION}.zip | cut -f 1`)"
  echo "Usage: unpack and source the environ file at its root"
}

if [ -z "$1" ]; then
  sanity_check
  download
  cleanup
  install_base
  install_nsis
  install_ocaml
  install_gtk
  make_environ
  . "$BASE/environ"
  build_install_lablgtk
  build_install_camlp5
  diet_sdk
  make_environ
  zip_sdk
  cleanup
  victory
else
  # just one step
  $1
fi
