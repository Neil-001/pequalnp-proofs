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

## L-meta-651 · Petersen edge function

[PetersenElimination.lean](PetersenElimination.lean) proves an unrestricted lower bound of 15 gates and gives a circuit with 20. Deleting one vertex leaves a function requiring at least 13 gates. Deleting two leaves a function requiring at least 11, whether the vertices are adjacent or nonadjacent. These estimates use the project's five- and six-cycle lower bounds and its reader lemma. Boolean identities for the residual graphs and all vertex renumberings are checked in Lean.

Setting vertex 0 to true leaves a function of size exactly 11. Setting it to false admits a 16-gate circuit. Theorem `fanoutConclusionAtEighteen` checks that the reader lemma's conclusion already holds at a hypothetical budget of 18, using savings of two gates on the false branch and four on the true branch. A proof that 19 gates are impossible must use additional information about the circuit.

[A separate counting argument](PetersenDepthOne.md) proves that 20 gates are necessary for monotone circuits with at most one AND on each input-to-output path, including circuits with shared wires. This argument is written out in prose.

To check the Lean files with the project's Mathlib cache installed:

```sh
cd lean
lake build PEqualNP.MetaComplexity.Helpers.Support PEqualNP.Defs.TimeAlt PEqualNP.MetaComplexity.L106
lake env lean ../research/CyclicMatchings.lean
lake env lean ../research/CheckpointVerification.lean
lake env lean -j1 ../research/PetersenElimination.lean
```
