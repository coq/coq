Name: coq_ext_for_pcoq
Version: 8.0pl1
Release: 1
Summary: The Coq Extension for Pcoq
Copyright: freely redistributable
Group: Applications/Math
Vendor: INRIA & LRI
URL: http://coq.inria.fr
Source: ftp://ftp.inria.fr/INRIA/coq/V8.0pl1/coq-8.0pl1.tar.gz
Icon: petit-coq.gif
Requires: coq = 8.0pl1
BuildRoot: /var/tmp/pcoq

%description
The Coq Extension for Pcoq provides all facilities to interface Coq with
Pcoq

%define debug_package %{nil}

%prep
%setup -n coq-8.0pl1

%build
./configure -bindir %{_bindir} -libdir %{_libdir}/coq -mandir %{_mandir} \
   -emacslib %{_datadir}/emacs/site-lisp \
   -coqdocdir %{_datadir}/texmf/tex/latex/misc \
   -opt -reals all -coqide no
make pcoq

%clean
rm -rf %{buildroot}
make clean

%install
rm -rf %{buildroot}
make -e COQINSTALLPREFIX=%{buildroot} install-pcoq

# compress man pages but don't strip at packaging time (rpm 3.0 to rpm 4.2)
%define __spec_install_post /usr/lib/rpm/brp-compress

# Don't strip at unpackaging time for rpm 4.3.x ??
%define __os_install_post       %{nil}

%files
%defattr(-,root,root)
%{_bindir}/*
%{_libdir}/coq/contrib/interface
%{_mandir}/man1/*

