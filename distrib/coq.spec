Name: coq
Version: 7.0beta
Release: 1
Summary: The Coq Proof Assistant
Copyright: freely redistributable
Group: Applications/Math
Vendor: INRIA Rocquencourt
URL: http://coq.inria.fr
Source: ftp://ftp.inria.fr/INRIA/coq/V7.0/coq-7.0beta.tar.gz
Icon: petit-coq.gif

%description
Coq is a proof assistant which: 
  - allows to handle calculus assertions, 
  - check mechanically proofs of these assertions, 
  - helps to find formal proofs, 
  - extracts a certified program from the constructive proof
    of its formal specification, 

# Ocaml is required but it is better to install it not with rpm but by
# hand in /usr/local
# Requires: ocaml >= 3.01


%prep
%setup

%build
./configure -bindir /usr/bin -libdir /usr/lib/coq -mandir /usr/man -emacs emacs -emacslib /usr/share/emacs/site-lisp -opt         # Need ocamlc.opt and ocamlopt.opt
make world       # Use native coq to compile theories

%clean
make clean

%install
make -e COQINSTALLPREFIX=$RPM_BUILD_ROOT/ install
# To install only locally the binaries compiled with absolute paths

%post
# This is because the Coq Team usually build Coq with Ocaml in /usr/local
# but ocaml is actually in /usr if coming from a rpm package
where=`ocamlc -v | tail -1 | sed -e 's/.*: \(.*\)/\1/'`
if [ ! "$where" = "/usr/local/lib/ocaml" ]; then
	ln -s $where /usr/local/lib/ocaml
fi

%postun
# This is because the Coq Team usually build Coq with Ocaml in /usr/local
# but ocaml is actually in /usr if coming from a rpm package
where=`ocamlc -v | tail -1 | sed -e 's/.*: \(.*\)/\1/'`
if [ ! "$where" = "/usr/local/lib/ocaml" ]; then
	rm $where /usr/local/lib/ocaml
fi

%files
/usr/bin/coqc
/usr/bin/coqtop
/usr/bin/coqtop.byte
/usr/bin/coqtop.opt
/usr/bin/coq-tex
/usr/bin/coqdep
/usr/bin/gallina
/usr/bin/coq_makefile
#/usr/bin/coq_searchisos.out
/usr/bin/coqmktop
#/usr/bin/coq2html
#/usr/bin/coq2latex
/usr/lib/coq
#/usr/man/man1/coqc.1
#/usr/man/man1/coqtop.1
#/usr/man/man1/coqmktop.1
/usr/man/man1/coqdep.1
/usr/man/man1/gallina.1
/usr/man/man1/coq-tex.1
#/usr/man/man1/coq2latex.1
#/usr/man/man1/coq2html.1
/usr/share/emacs/site-lisp/coq.el
/usr/share/emacs/site-lisp/coq.elc
