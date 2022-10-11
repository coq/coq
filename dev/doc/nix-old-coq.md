# Historic Coq versions using Nix

## Introduction

You can download and run older versions of Coq using Nix.

Using Nix flakes, you can run coqide like:

```sh
nix shell nixpkgs#coqPackages_8_15.coqide -c coqide
```

This will setup and run CoqIDE 8.15.2 given a recent enough nixpkgs.

Before 8.14, CoqIDE was included in the main Coq package so you only need to do:

```sh
nix shell nixpkgs#coq_8_12 -c coqide
```

TODO: nix-shell command should probably be here as well since most people will
be using those


## Nixpkgs Version List

Here are a list of hashes for nixpkgs where a version of Coq was introduced.

Each minor version may have several patches so the specific nixpkgs hash has
been provided. Note that new nixpkgs still support the older versions of Coq if
the coq_X_Y package name is used. Newer nixpkgs may however drop support for
these older versions.


```
Coq Ver               nixpkgs SHA                    CoqIDE package
V8.16.0 a037a50b4696632977dadd61747b02492a109478 coq_8_16 coqPackages_8_16.coqide
V8.15.2 442db9429b9fbdb6352cfb937afc8ecccfe2633f coq_8_15 coqPackages_8_15.coqide
V8.15.1 3d0a9d166851548a7182ca7e4fadd1425e125757 coq_8_15 coqPackages_8_15.coqide
V8.15.0 20e7213d16eef3c3591f0452796b8d42245da865 coq_8_15 coqPackages_8_15.coqide
V8.14.1 48406e3fca5be837df5cfa3a5b891dd3d6557e1b coq_8_14 coqPackages_8_14.coqide
V8.14.0 e242eef8a45f7e149f7af64ae07e0c45ab51c044 coq_8_14 coqPackages_8_14.coqide
V8.13.2 ab16ad87649b6ea845be46fa7df7e9466ed4e05d coq_8_13
V8.13.1 cd43a539477b1b7a5af4edb70b500184beaf240b coq_8_13
V8.13.0 813d14b9b7769a4550fbf9a42fa8af779ab6c475 coq_8_13
V8.12.2 c5556b7454f733cf7c2528a8c131c56b2dbd34bc coq_8_12
V8.12.1 2806eb27431abf2ffcff7404783198c4b767e6de coq_8_12
V8.12.0 b8dfca143c5b9e632530720ab472bd54d9d21137 coq_8_12
V8.11.2 48f0d8b3c8678185420231e8cda1139794325dee coq_8_11
V8.11.1 d6a8d0ca5b03dbdb84070b47021b2b852429348e coq_8_11
V8.11.0 13dd5844fdf4be744c359f8559f8727011cb7bf1 coq_8_11
V8.10.2 3806eff9ca233b9b3580a8421b52c2db8e60c6bf coq_8_10
V8.10.1 a8892b0d76b02210b0c37e180b9db6535f001ab0 coq_8_10
V8.10.0 b4db381443ed25a2664a12ca110f9a2a44c1b4bc coq_8_10
V8.9.1  57c3da07eb8524dd8ba9a000c2003f762af50bfa coq_8_9
V8.9.0  b76961124d938dae59e4c9db90832b87ccb1b42b coq_8_9
V8.8.2  23900febe79a3a6aaab1276cde8689e0fa3f3d5c coq_8_8
V8.8.1  314eb884ecd22803db4149936a2c95b48ad2f60b coq_8_8
V8.8.0  76a43d765cc9d5ed31d275abfe28b52f842f6b15 coq_8_8
V8.7.2  90252481bfe233c3fe5a54f9d6d73e93f08e1e27 coq_8_7
V8.7.1  40627000f773d7a51b496f07be29b8498c1324a7 coq_8_7
V8.7.0  89720d851aafe7be2aafc129fd729941a4db18af coq_8_7
V8.6.1  c0dca2fb00a4e94f995b2752c78f4e67a6c6e7c8 coq_8_6
V8.6    a30e8db9f04315730f83f324c4079f69bbac44a5 coq_8_6
V8.5    a30e8db9f04315730f83f324c4079f69bbac44a5 coq_8_5
V8.4pl5 2b9e43b513bb2c85eb59826b32ab3eba565d5a0c coq_8_4
V8.4pl4 5bbcebf2dbe29b7e17d718db6b774991e3070748 coq_8_4
V8.4pl3 fa118fc6777d5ddaf8e91911b007a642c7e10b73 coq_8_4
V8.4pl2 c9f59592851036eef99ac2ed2096aa46935531ec coq_8_4
V8.4    706cbc9318ef56d76a48883d9a0b6539e30985c7 coq_8_4
V8.3pl3 699de0f3f9ec9e03ca2792c1667308dbf86d9f3e coq_8_3
V8.3pl1 bec1a9c44f4b07ebd80a7257271b8c3bf57ace0a coq_8_3
V8.3    0430167083c1cdca354b295f87290d7b10a930e7 coq_8_3
V8.2pl2 c0f343b7527e5c706dfc687b4bd0f17143afd0ef ??
V8.2pl1 a0207b3dc7ff3583df37f2bb8bab939390f964c7 No CoqIDE!
V8.1pl2 12ca68d11447fc5e9d3163caf822b6e98b3a65af No CoqIDE!
```
