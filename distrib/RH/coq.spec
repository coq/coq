Name: coq
Version: 8.0pl2
Release: 1
Summary: The Coq Proof Assistant
Copyright: freely redistributable
Group: Applications/Math
Vendor: INRIA & LRI
URL: http://coq.inria.fr
Source: ftp://ftp.inria.fr/INRIA/coq/V8.0pl2/coq-8.0pl2.tar.gz
Icon: petit-coq.gif
BuildRoot: /var/tmp/coq

%description
Coq is a proof assistant which: 
  - allows to handle calculus assertions, 
  - check mechanically proofs of these assertions, 
  - helps to find formal proofs, 
  - extracts a certified program from the constructive proof
    of its formal specification, 

Requires: ocaml >= 3.06

%define debug_package %{nil}
                                                                               
%prep
%setup

%build
./configure -bindir %{_bindir} -libdir %{_libdir}/coq -mandir %{_mandir} \
   -emacslib %{_datadir}/emacs/site-lisp \
   -coqdocdir %{_datadir}/texmf/tex/latex/misc \
   -opt -reals all -coqide no
make coq


%clean
rm -rf %{buildroot}
make clean

%install
rm -rf %{buildroot}
make -e COQINSTALLPREFIX=%{buildroot} install-coq

# compress man pages but don't strip at packaging time (rpm 3.0 to rpm 4.2)
%define __spec_install_post /usr/lib/rpm/brp-compress

# Don't strip at unpackaging time for rpm 4.3.x ??
%define __os_install_post       %{nil}

%files
%defattr(-,root,root)
%{_bindir}/*
%{_libdir}/coq
%{_mandir}/man1/*
%{_datadir}/emacs/site-lisp/*
%{_datadir}/texmf/tex/latex/misc/*
