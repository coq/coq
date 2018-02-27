(C) 2016 Intel Deutschland GmbH
Author: Michael Soegtrop

Released to the public by Intel under the
GNU Lesser General Public License Version 2.1 or later
See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

This license also applies to all files in the patches_coq subfolder.

==================== Purpose / Goal ====================

The main purpose of these scripts is to build Coq for Windows in a reproducible
and at least by this script documented way without using binary libraries and
executables from various sources. These scripts use only MinGW libraries
provided by Cygwin or compile things from sources. For some libraries there are
options to build them from sources or to use the Cygwin version.

Another goal (which is not yet achieved) is to have a Coq installer for
Windows, which includes all tools required for native compute and Coq plugin
development without Cygwin.

Coq requires OCaml for this and OCaml requires binutils, gcc and a posix shell.
Since the standard Windows OCaml installation requires Cygwin to deliver some of
these components, you might be able to imagine that this is not so easy.

These scripts can produce the following:

- Coq running on MinGW

- OCaml producing MinGW code and running on MinGW

- GCC producing MinGW code and running on MinGW

- binutils producing MinGW code and running on MinGW

With "running on MinGW" I mean that the tools accept paths like
"C:\myfolder\myfile.txt" and that they don't link to a Cygwin or msys DLL. The
MinGW gcc and binutils provided by Cygwin produce MinGW code, but they run only
on Cygwin.

With "producing MinGW code" I mean that the programs created by the tools accept
paths like "C:\myfolder\myfile.txt" and that they don't link to a Cygwin or msys
DLL.

The missing piece is a posix shell running on plain Windows (without msys or
Cygwin DLL) and not beeing a binary from obscure sources. I am working on it ...

Since compiling gcc and binutils takes a while and it is not of much use without
a shell, the building of these components is currently disabled. OCaml is built
anyway, because this MinGW/MinGW OCaml (rather than a Cygwin/MinGW OCaml) is
used to compile Coq.

Until the shell is there, the Cygwin created by these scripts is required to run
OCaml tools. When everything is finished, this will no longer be required.

==================== Usage ====================

The Script MakeCoq_MinGW does:
- download Cygwin (except the Setup.exe or Setup64.exe)
- install Cygwin
- either installs MinGW GTK via Cygwin or compiles it fom sources
- download, compile and install OCaml, CamlP5, Menhir, lablgtk
- download, compile and install Coq
- download, compile and install selected addons
- create a Windows installer (NSIS based)

The parameters are described below. Mostly paths and the HTTP proxy need to be
set.

There are two main usages:

- Compile and install OCaml and Coq in a given folder

  This works reliably, because absolute library paths can be compiled into Coq
  and OCaml.
  
  WARNING: See the "Purpose / Goal" section above for status.
  
  See MakeCoq_85pl2_abs_ocaml.bat for parameters.

- Create a Windows installer.

  This works well for Coq but not so well for OCaml.

  WARNING: See the "Purpose / Goal" section above for status.
  
  See MakeCoq_85pl2_installer.bat for parameters.

There is also an option to compile OCaml and Coq inside Cygwin, but this is
currently not recommended. The resulting Coq and OCaml work, but Coq is slow
because it scans the largish Cygwin share folder. This will be fixed in a future
version.

Procedure:

- Unzip contents of CoqSetup.zip in a folder

- Adjust parameters in MakeCoq_85pl2_abs_ocaml.bat or in MakeCoq_85pl2_installer.bat.

- Download Cygwin setup from https://Cygwin.com/install.html
  For 32 bit Coq : setup-x86.exe    (https://Cygwin.com/setup-x86.exe)
  For 64 bit Coq : setup-x86_64.exe (https://Cygwin.com/setup-x86_64.exe)

- Run MakeCoq_85pl3_abs_ocaml.bat or MakeCoq_85pl3_installer.bat

- Check MakeCoq_regtests.bat to see what combinations of options are tested

==================== MakeCoq_MinGW Parameters ====================

===== -arch =====

Set the target architecture.

Possible values:

32: Install/build Cygwin, ocaml and coq for 32 bit windows

64: Install/build Cygwin, ocaml and coq for 64 bit windows

Default value: 64


===== -mode =====

Set the installation mode / target folder structure.
  
Possible values:

mingwinCygwin: Install coq in the default Cygwin mingw sysroot folder.
               This is %DESTCYG%\usr\%ARCH%-w64-mingw32\sys-root\mingw.
               Todo: The coq share folder should be configured to e.g. /share/coq.
               As is, coqc scans the complete share folder, which slows it down 5x for short files.
               
absoloute:     Install coq in the absolute path given with -destcoq.
               The resulting Coq will not be relocatable.
               That is the root folder must not be renamed/moved.

relocatable:   Install coq in the absolute path given with -destcoq.
               The resulting Coq will be relocatable.
               That is the root folder may be renamed/moved.
               If OCaml is installed, please note that OCaml cannot be build really relocatable.
               If the root folder is moved, the environment variable OCAMLLIB must be set to the libocaml sub folder.
               Also the file <root>\libocaml\ld.conf must be adjusted.

Default value: absolute


===== -installer =====

Create a Windows installer (it will be in build/coq-8.xplx/dev/nsis)

Possible values:

Y: Create a windows installer - this forces -mode=relocatable.

N: Don't create a windows installer - use the created Coq installation as is.

Default value: N


===== -ocaml =====

Install OCaml for later use with Coq or just for building.

Possible values:

Y: Install OCaml in the same root as Coq (as given with -coqdest)
   This also copies all .o, .cmo, .a, .cmxa files in the lib folder required for compiling plugins.

N: Install OCaml in the default Cygwin mingw sysroot folder.
   This is %DESTCYG%\usr\%ARCH%-w64-mingw32\sys-root\mingw.

Default value: N


===== -make =====

Build and install MinGW GNU make

Possible values:

Y: Install MinGW GNU make in the same root as Coq (as given with -coqdest).

N: Don't build or install MinGW GNU make.
   For building everything always Cygwin GNU make is used.

Default value: Y


===== -destcyg =====

Destination folder in which Cygwin is installed.

This must be an absolute path in Windows format (with drive letter and \\).

>>>>> This folder may be deleted after the Coq build is finished! <<<<<

Default value: C:\bin\Cygwin_coq


===== -destcoq =====

Destination folder in which Coq is installed.

This must be an absolute path in Windows format (with drive letter and \\).

This option is not required if -mode mingwinCygwin is used.

Default value: C:\bin\coq


===== -setup =====

Name/path of the Cygwin setup program.

The Cygwin setup program is called setup-x86.exe or setup-x86_64.exe.
It can be downloaded from: https://Cygwin.com/install.html.

Default value: setup-x86.exe or setup-x86_64.exe, depending on -arch.


===== -proxy =====

Internet proxy setting for downloading Cygwin, ocaml and coq.

The format is <server>:<port>, e.g. proxy.mycompany.com:911

The same proxy is used for HTTP, HTTPS and FTP.
If you need separate proxies for separate protocols, you please put your proxies directly into configure_profile.sh (line 11..13).

Default value: Value of HTTP_PROXY environment variable or none if this variable does not exist.

ATTENTION: With the --proxy setting of the Cygwin setup, it is possible to
supply a proxy server, but if this parameter is "", Cygwin setup might use proxy
settings from previous setups. If you once did a Cygwin setup behind a firewall
and now want to do a Cygwin setup without a firewall, use the -cygquiet=N
setting to perform a GUI install, where you can adjust the proxy setting.

===== -cygrepo =====

The online repository, from which Cygwin packages are downloaded.

Note: although most repositories end with Cygwin32, they are good for 32 and 64 bit Cygwin.

Default value: http://ftp.inf.tu-dresden.de/software/windows/Cygwin32

>>>>> If you are not in Europe, you might want to change this! <<<<<


===== -cygcache =====

The local cache folder for Cygwin repositories.

You can also copy files here from a backup/reference and set -cyglocal.
The setup will then not download/update from the internet but only use the local cache.

Default value: <folder of MakeCoq_MinGW.bat>\Cygwin_cache


===== -cyglocal =====

Control if the Cygwin setup uses the latest version from the internet or the version as is in the local folder.

Possible values:

Y: Install exactly the Cygwin version from the local repository cache.
   Don't update from the internet.

N: Download the latest Cygwin version from the internet.
   Update the local repository cache with the latest version.

Default value: N


===== -cygquiet =====

Control if the Cygwin setup runs quitely or interactive.

Possible values:

Y: Install Cygwin quitely without user interaction.

N: Install Cygwin interactively (allows to select additional packages).

Default value: Y


===== -srccache =====

The local cache folder for ocaml/coq/... sources.

Default value: <folder of MakeCoq_MinGW.bat>\source_cache


===== -coqver =====

The version of Coq to download and compile.

Possible values: 8.4pl6, 8.5pl2, 8.5pl3, 8.6
                 (download from https://coq.inria.fr/distrib/V$COQ_VERSION/files/coq-<version>.tar.gz)
                 Others versions might work, but are untested.
                 8.4 is only tested in mode=absoloute
                 
                 git-v8.6, git-trunk
                 (download from https://github.com/coq/coq/archive/<version without git->.zip)
                 
                 /cygdrive/....
                 Use local folder. The sources are archived as coq-local.tar.gz

Default value: 8.5pl3

If git- is prepended, the Coq sources are loaded from git.

ATTENTION: with default options, the scripts cache source tar balls in two
places, the <destination>/build/tarballs folder and the <scripts>/source_cache
folder. If you modified something in git, you need to delete the cached tar ball
in both places!

===== -gtksrc =====

Control if GTK and its prerequisites are build from sources or if binary MinGW packages from Cygwin are used

Possible values:

Y: Build GTK from sources, takes about 90 minutes extra.
   This is useful, if you want to debug/fix GTK or library issues.

N: Use prebuilt MinGW libraries from Cygwin


===== -threads =====

Control the maximum number of make threads for modules which support parallel make.

Possible values: 1..N. 
                 Should not be more than 1.5x the number of cores.
                 Should not be more than available RAM/2GB (e.g. 4 for 8GB)

===== -addon =====

Enable build and installation of selected Coq package (can be repeated for
selecting more packages)

==================== TODO ====================

- Check for spaces in destination paths
- Check for = signs in all paths (DOS commands don't work with pathes with = in it, possibly even when quoted)
- Installer doesn't remove OCAMLLIB environment variables (it is in the script, but doesn't seem to work)
- CoqIDE doesn't find theme files
- Finish / test mingw_in_Cygwin mode (coqide doesn't start, coqc slow cause of scanning complete share folder)
- Possibly create/login as specific user to bash (not sure if it makes sense - nead to create additional bash login link then)
- maybe move share/doc/menhir somehwere else (reduces coqc startup time)
- Use original installed file list for removing files in uninstaller 

==================== Issues with relocation ====================

Coq and OCaml are built in a specific folder and are not really intended for relocation e.g. by an installer.
Some absolute paths in config files are patched in coq_new.nsi.

Coq is made fairly relocatable by first configuring it with PREFIX=./ and then PREFIX=<installdir>.
OCaml is made relocatable mostly by defining the OCAMLLIB environment variable and by patching some files.
If you have issues with one of the remaining (unpatched) files below, please let me know.

Text files patched by the installer:

./ocamllib/ld.conf
./etc/findlib.conf:destdir="D:\\bin\\coq64_buildtest_reloc_ocaml20\\libocaml\\site-lib"
./etc/findlib.conf:path="D:\\bin\\coq64_buildtest_reloc_ocaml20\\libocaml\\site-lib"

Text files containing the install folder path after install:

./bin/mkcamlp5:LIB=D:/bin/coq64_buildtest_reloc_ocaml20/libocaml/camlp5
./bin/mkcamlp5.opt:LIB=D:/bin/coq64_buildtest_reloc_ocaml20/libocaml/camlp5
./libocaml/Makefile.config:PREFIX=D:/bin/coq64_buildtest_reloc_ocaml20
./libocaml/Makefile.config:LIBDIR=D:/bin/coq64_buildtest_reloc_ocaml20/libocaml
./libocaml/site-lib/findlib/Makefile.config:OCAML_CORE_BIN=/cygdrive/d/bin/coq64_buildtest_reloc_ocaml20/bin
./libocaml/site-lib/findlib/Makefile.config:OCAML_SITELIB=D:/bin/coq64_buildtest_reloc_ocaml20\libocaml\site-lib
./libocaml/site-lib/findlib/Makefile.config:OCAMLFIND_BIN=D:/bin/coq64_buildtest_reloc_ocaml20\bin
./libocaml/site-lib/findlib/Makefile.config:OCAMLFIND_CONF=D:/bin/coq64_buildtest_reloc_ocaml20\etc\findlib.conf
./libocaml/topfind:#directory "D:\\bin\\coq64_buildtest_reloc_ocaml20\\libocaml\\site-lib/findlib";;
./libocaml/topfind:  Topdirs.dir_load Format.err_formatter "D:\\bin\\coq64_buildtest_reloc_ocaml20\\libocaml\\site-lib/findlib/findlib.cma";
./libocaml/topfind:  Topdirs.dir_load Format.err_formatter "D:\\bin\\coq64_buildtest_reloc_ocaml20\\libocaml\\site-lib/findlib/findlib_top.cma";
./libocaml/topfind:(* #load "D:\\bin\\coq64_buildtest_reloc_ocaml20\\libocaml\\site-lib/findlib/findlib.cma";; *)
./libocaml/topfind:(* #load "D:\\bin\\coq64_buildtest_reloc_ocaml20\\libocaml\\site-lib/findlib/findlib_top.cma";; *)
./man/man1/camlp5.1:These files are installed in the directory D:/bin/coq64_buildtest_reloc_ocaml20/libocaml/camlp5.
./man/man1/camlp5.1:D:/bin/coq64_buildtest_reloc_ocaml20/libocaml/camlp5

Binary files containing the build folder path after install:

$ find . -type f -exec grep "Cygwin_coq64_buildtest_reloc_ocaml20" {} /dev/null \;
Binary file ./bin/coqtop.byte.exe matches
Binary file ./bin/coqtop.exe matches
Binary file ./bin/ocamldoc.exe matches
Binary file ./bin/ocamldoc.opt.exe matches
Binary file ./libocaml/ocamldoc/odoc_info.a matches
Binary file ./libocaml/ocamldoc/odoc_info.cma matches

Binary files containing the install folder path after install:

$ find . -type f -exec grep "coq64_buildtest_reloc_ocaml20" {} /dev/null \;
Binary file ./bin/camlp4.exe matches
Binary file ./bin/camlp4boot.exe matches
Binary file ./bin/camlp4o.exe matches
Binary file ./bin/camlp4o.opt.exe matches
Binary file ./bin/camlp4of.exe matches
Binary file ./bin/camlp4of.opt.exe matches
Binary file ./bin/camlp4oof.exe matches
Binary file ./bin/camlp4oof.opt.exe matches
Binary file ./bin/camlp4orf.exe matches
Binary file ./bin/camlp4orf.opt.exe matches
Binary file ./bin/camlp4r.exe matches
Binary file ./bin/camlp4r.opt.exe matches
Binary file ./bin/camlp4rf.exe matches
Binary file ./bin/camlp4rf.opt.exe matches
Binary file ./bin/camlp5.exe matches
Binary file ./bin/camlp5o.exe matches
Binary file ./bin/camlp5o.opt matches
Binary file ./bin/camlp5r.exe matches
Binary file ./bin/camlp5r.opt matches
Binary file ./bin/camlp5sch.exe matches
Binary file ./bin/coqc.exe matches
Binary file ./bin/coqchk.exe matches
Binary file ./bin/coqdep.exe matches
Binary file ./bin/coqdoc.exe matches
Binary file ./bin/coqide.exe matches
Binary file ./bin/coqtop.byte.exe matches
Binary file ./bin/coqtop.exe matches
Binary file ./bin/coqworkmgr.exe matches
Binary file ./bin/coq_makefile.exe matches
Binary file ./bin/menhir matches
Binary file ./bin/mkcamlp4.exe matches
Binary file ./bin/ocaml.exe matches
Binary file ./bin/ocamlbuild.byte.exe matches
Binary file ./bin/ocamlbuild.exe matches
Binary file ./bin/ocamlbuild.native.exe matches
Binary file ./bin/ocamlc.exe matches
Binary file ./bin/ocamlc.opt.exe matches
Binary file ./bin/ocamldebug.exe matches
Binary file ./bin/ocamldep.exe matches
Binary file ./bin/ocamldep.opt.exe matches
Binary file ./bin/ocamldoc.exe matches
Binary file ./bin/ocamldoc.opt.exe matches
Binary file ./bin/ocamlfind.exe matches
Binary file ./bin/ocamlmklib.exe matches
Binary file ./bin/ocamlobjinfo.exe matches
Binary file ./bin/ocamlopt.exe matches
Binary file ./bin/ocamlopt.opt.exe matches
Binary file ./bin/ocamlprof.exe matches
Binary file ./bin/ocamlrun.exe matches
Binary file ./bin/ocpp5.exe matches
Binary file ./lib/config/coq_config.cmo matches
Binary file ./lib/config/coq_config.o matches
Binary file ./lib/grammar/grammar.cma matches
Binary file ./lib/ide/ide_win32_stubs.o matches
Binary file ./lib/lib/clib.a matches
Binary file ./lib/lib/clib.cma matches
Binary file ./lib/libcoqrun.a matches
Binary file ./libocaml/camlp4/camlp4fulllib.a matches
Binary file ./libocaml/camlp4/camlp4fulllib.cma matches
Binary file ./libocaml/camlp4/camlp4lib.a matches
Binary file ./libocaml/camlp4/camlp4lib.cma matches
Binary file ./libocaml/camlp4/camlp4o.cma matches
Binary file ./libocaml/camlp4/camlp4of.cma matches
Binary file ./libocaml/camlp4/camlp4oof.cma matches
Binary file ./libocaml/camlp4/camlp4orf.cma matches
Binary file ./libocaml/camlp4/camlp4r.cma matches
Binary file ./libocaml/camlp4/camlp4rf.cma matches
Binary file ./libocaml/camlp5/odyl.cma matches
Binary file ./libocaml/compiler-libs/ocamlcommon.a matches
Binary file ./libocaml/compiler-libs/ocamlcommon.cma matches
Binary file ./libocaml/dynlink.cma matches
Binary file ./libocaml/expunge.exe matches
Binary file ./libocaml/extract_crc.exe matches
Binary file ./libocaml/libcamlrun.a matches
Binary file ./libocaml/ocamlbuild/ocamlbuildlib.a matches
Binary file ./libocaml/ocamlbuild/ocamlbuildlib.cma matches
Binary file ./libocaml/ocamldoc/odoc_info.a matches
Binary file ./libocaml/ocamldoc/odoc_info.cma matches
Binary file ./libocaml/site-lib/findlib/findlib.a matches
Binary file ./libocaml/site-lib/findlib/findlib.cma matches
Binary file ./libocaml/site-lib/findlib/findlib.cmxs matches
