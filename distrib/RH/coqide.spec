Name: coqide
Version: 8.0
Release: 1
Summary: The Coq Integrated Development Interface
Copyright: freely redistributable
Group: Applications/Math
Vendor: INRIA & LRI
URL: http://coq.inria.fr
Source: ftp://ftp.inria.fr/INRIA/coq/V8.0beta/coq-8.0.tar.gz
Icon: petit-coq.gif
Requires: coq = 8.0

%description
The Coq Integrated Development Interface is a graphical interface for the 
Coq proof assistant 

%prep
%setup -n coq-8.0cdrom

%build
./configure -prefix /usr -emacslib /usr/share/emacs/site-lisp -opt -reals all   # Need ocamlc.opt and ocamlopt.opt
make coqide  # Use native coq to compile theories

%clean
make clean

%install
make -e COQINSTALLPREFIX=$RPM_BUILD_ROOT/ install-coqide
# To install only locally the binaries compiled with absolute paths

# the spec file is read from distrib/RH/src/SOURCES/coqX.Y
# but coqide.list is in distrib/RH/src
%files -f ../../coqide.list
%defattr(-,root,root)
