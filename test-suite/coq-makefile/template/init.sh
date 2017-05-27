
export PATH=$COQBIN:$PATH

rm -rf theories src Makefile Makefile.conf tmp
git clean -dfx || true

mkdir -p src
mkdir -p theories/sub

cp ../template/theories/sub/testsub.v theories/sub
cp ../template/theories/test.v theories
cp ../template/src/test.ml4 src
cp ../template/src/test_aux.mli src
cp ../template/src/test.mli src
cp ../template/src/test_plugin.mlpack src
cp ../template/src/test_aux.ml src
