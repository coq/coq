Name: coqide
Version: 8.0pl2
Release: 1
Summary: The Coq Integrated Development Interface
Copyright: freely redistributable
Group: Applications/Math
Vendor: INRIA & LRI
URL: http://coq.inria.fr
Source: ftp://ftp.inria.fr/INRIA/coq/V8.0pl2/coq-8.0pl2.tar.gz
Icon: petit-coq.gif
Requires: coq = 8.0pl1
BuildRoot: /var/tmp/coqide

%description
The Coq Integrated Development Interface is a graphical interface for the 
Coq proof assistant 

%define debug_package %{nil}

%prep
%setup -n coq-8.0pl2

%build
./configure -bindir %{_bindir} -libdir %{_libdir}/coq -mandir %{_mandir} \
   -emacslib %{_datadir}/emacs/site-lisp \
   -coqdocdir %{_datadir}/texmf/tex/latex/misc -opt -reals all
make coqide

%clean
rm -rf %{buildroot}
make clean

%install
rm -rf %{buildroot}
make -e COQINSTALLPREFIX=%{buildroot} install-coqide

# compress man pages but don't strip at packaging time (rpm 3.0 to rpm 4.2)
%define __spec_install_post /usr/lib/rpm/brp-compress

# Don't strip at unpackaging time for rpm 4.3.x ??
%define __os_install_post       %{nil}

%files
%defattr(-,root,root)
%{_bindir}/*
%{_libdir}/coq/ide
