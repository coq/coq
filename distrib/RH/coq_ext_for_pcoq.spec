Name: coq_ext_for_pcoq
Version: 8.0
Release: 1
Summary: The Coq Extension for Pcoq
Copyright: freely redistributable
Group: Applications/Math
Vendor: INRIA & LRI
URL: http://coq.inria.fr
Source: ftp://ftp.inria.fr/INRIA/coq/V8.0/coq-8.0.tar.gz
Icon: petit-coq.gif
Requires: coq = 8.0

%description
The Coq Extension for Pcoq provides all facilities to interface Coq with
Pcoq

%prep
%setup -n coq-8.0

%build
./configure -prefix /usr -emacslib /usr/share/emacs/site-lisp -opt -reals all -coqide no       # Need ocamlc.opt and ocamlopt.opt
make pcoq      # Use native coq to compile theories


%clean
make clean

%install
make -e COQINSTALLPREFIX=$RPM_BUILD_ROOT/ install-pcoq
# To install only locally the binaries compiled with absolute paths

# the spec file is read from distrib/RH/src/SOURCES/coqX.Y
# but pcoq.list is in distrib/RH/src
%files -f ../../pcoq.list
%defattr(-,root,root)

