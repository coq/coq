Name: coq
Version: 7.3.1
Release: 1
Summary: The Coq Proof Assistant
Copyright: freely redistributable
Group: Applications/Math
Vendor: INRIA Rocquencourt
URL: http://coq.inria.fr
Source: ftp://ftp.inria.fr/INRIA/coq/V7.3.1/coq-7.3.1.tar.gz
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
# Requires: ocaml >= 3.06


%prep
%setup

%build
m4_include(do_build)

%clean
make clean

%install
make -e COQINSTALLPREFIX=$RPM_BUILD_ROOT/ install
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
m4_include(coq.list)
