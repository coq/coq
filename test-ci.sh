cd _build_ci
cd bignums && git clean -dfx
cd ../math_classes && git clean -dfx
cd ../..
bash dev/ci/ci-bignums.sh
bash dev/ci/ci-math_classes.sh
