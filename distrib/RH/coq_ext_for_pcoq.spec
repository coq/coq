Name: coq_ext_for_pcoq
Version: 8.0cdrom
Release: 1
Summary: The Coq Extension for Pcoq
Copyright: freely redistributable
Group: Applications/Math
Vendor: INRIA & LRI
URL: http://coq.inria.fr
Source: ftp://ftp.inria.fr/INRIA/coq/V8.0/coq_ext_for_pcoq-8.0cdrom.tar.gz
Icon: petit-coq.gif
Requires: coq = 8.0cdrom

%description
The Coq Extension for Pcoq provides all facilities to interface Coq with
Pcoq

%prep
%setup

%build
./configure -prefix /usr -emacs emacs -emacslib /usr/share/emacs/site-lisp -opt -reals all -coqide no       # Need ocamlc.opt and ocamlopt.opt
make pcoq                   # Use native coq to compile theories


%clean
make clean

%install
make -e COQINSTALLPREFIX=$RPM_BUILD_ROOT/ BASETEXDIR=$RPM_BUILD_ROOT/ install-pcoq
# To install only locally the binaries compiled with absolute paths

%files -f ../../coq-pcoq.list
# the spec file is moved to distrib/RH/src/SPECS but coq.list is in distrib/RH
%defattr(-,root,root)

