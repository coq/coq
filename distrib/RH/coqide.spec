Name: coqide
Version: 8.0cdrom
Release: 1
Summary: The Coq Integrated Development Interface
Copyright: freely redistributable
Group: Applications/Math
Vendor: INRIA & LRI
URL: http://coq.inria.fr
Source: ftp://ftp.inria.fr/INRIA/coq/V8.0beta/coq-8.0cdrom.tar.gz
Icon: petit-coq.gif
Requires: coq = 8.0cdrom

%description
The Coq Integrated Development Interface is a graphical interface for the 
Coq proof assistant 

%prep
%setup -n coq-8.0cdrom

%build
./configure -prefix /usr -emacs emacs -emacslib /usr/share/emacs/site-lisp -opt -reals all   # Need ocamlc.opt and ocamlopt.opt
make coqide  # Use native coq to compile theories

%clean
make clean

%install
make -e COQINSTALLPREFIX=$RPM_BUILD_ROOT/ BASETEXDIR=$RPM_BUILD_ROOT install-coqide
# To install only locally the binaries compiled with absolute paths

%post
# This is a because the Coq Team usually build Coq with Ocaml in /usr/local
# but ocaml is actually in /usr if coming from a rpm package
# This works only if ocaml has been installed by rpm
if [ ! -e /usr/local/lib/ocaml ]; then
  ln -s /usr/lib/ocaml /usr/local/lib/ocaml || true
fi

%postun
# This is because the Coq Team usually build Coq with Ocaml in /usr/local
# but ocaml is actually in /usr if coming from a rpm package
if [ -L /usr/local/lib/ocaml ]; then
  rm /usr/local/lib/ocaml
fi

%files
%defattr(-,root,root)
/usr/bin/coqide.byte
/usr/bin/coqide.opt
/usr/bin/coqide
/usr/lib/coq/ide/utf8.v
/usr/lib/coq/ide/utf8.vo
/usr/lib/coq/ide/coq.png
/usr/lib/coq/ide/.coqide-gtk2rc
/usr/lib/coq/ide/FAQ
