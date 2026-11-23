# Partial results for the P vs NP project

## L-meta-652 · Three cyclic matchings

For each shift of three positions, the output records whether any active left input coincides with a shifted active right input. The minimum for the three outputs together is between 13 and 15 fan-in-two AND, OR and NOT gates. Any solution using at most 14 gates computes at most three distinct left-right products directly. The cases with 13 and 14 gates remain open.

[CyclicMatchings.lean](CyclicMatchings.lean) proves the 15-gate upper bound. It also gives a 12-gate construction on the 16 inputs with at most one active bit per side, and an input on which that construction fails. The theorem `oneSideLower` proves a lower bound of 15 when the final circuit receives only raw products and arbitrary functions of one fixed side.

The unrestricted lower bound uses [an external SAT encoding](matching_synthesis.py). The [certificate manifest](matching_certificates/manifest.json) lists each case, the role it plays in the argument, and the checksums. The circuit normalization and symmetry arguments are outside Lean. With Python 3.11 or later and [lrat-trim rel-0.2.0](https://github.com/arminbiere/lrat-trim), run from the repository root:

```sh
python3 research/verify_matching.py
```

## L-lib-123 · Checkpoint verification

[CheckpointVerification.lean](CheckpointVerification.lean) proves a three-block alternating characterization of deterministic reachability and a bound for computations of bounded configuration width. The unrestricted time speedup and the machine implementation of the verifier remain open.

To check both Lean files with the project's Mathlib cache installed:

```sh
cd lean
lake build PEqualNP.MetaComplexity.Helpers.Support PEqualNP.Defs.TimeAlt
lake env lean ../research/CyclicMatchings.lean
lake env lean ../research/CheckpointVerification.lean
```
