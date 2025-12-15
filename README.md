# Balanced Vectors

A Lean 4 formalization proving that symmetric log-concave functions on weak compositions are maximized on balanced vectors and minimized on concentrated vectors.

## Status

**Work in progress.** Feedback welcome.

## The Theorem

For any function `D : WeakComposition n d → ℚ` that is:
- Strictly positive
- Symmetric under permutations of indices
- Log-concave (satisfies `D(e)² ≥ D(e⁺) · D(e⁻)` for adjacent modifications)

There exist:
- A **balanced** vector `b` (entries differ by at most 1) maximizing `D`
- A **concentrated** vector `c` (all mass at one position) minimizing `D`

## Project Structure

```
BalancedVectors.lean           -- Public API (imports ProofOfMainTheorem)
BalancedVectors/
  Definitions.lean             -- Core definitions (WeakComposition, IsBalanced, etc.)
  MainTheorem.lean             -- Statement: StatementOfTheorem
  ProofOfMainTheorem.lean      -- Proof: mainTheorem
  Proofs/
    helper_lemmas.lean         -- Supporting lemmas
```

The public API exposes exactly two declarations:
- `StatementOfTheorem : Prop`
- `mainTheorem : StatementOfTheorem`

## Origin

This is a refactoring of Johannes Schmitt's [balanced-vectors-blueprint](https://github.com/schmittj/balanced-vectors-blueprint), which formalized a proof discovered by GPT-5 for an open problem about psi-class integrals on moduli spaces of curves.

## Building

```bash
lake exe cache get  # download Mathlib cache
lake build
```

## License

Apache 2.0
