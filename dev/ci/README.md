Continuous Integration for the Rocq Prover
==========================================

Changes to Rocq are systematically tested for regression and compatibility
breakage on our Continuous Integration (CI) platforms *before* integration,
so as to ensure better robustness and catch problems as early as possible.
These tests include the compilation of several external libraries / plugins.

This README is split into two specific documents:

- [README-users.md](./README-users.md) which contains information for
  authors of external libraries and plugins who might be interested in
  having their development tested in our CI system.

- [README-developers.md](./README-developers.md) for Rocq developers /
  contributors, who must ensure that they don't break these external
  developments accidentally.

*Remark:* the CI policy outlined in these documents is susceptible to
evolve and specific accommodations are of course possible.
