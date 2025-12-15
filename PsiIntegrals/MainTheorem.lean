/-
Copyright (c) 2025 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
module

public import PsiIntegrals.Definitions

/-!
# Statement of the Main Theorem

This file contains the statement of the main theorem about symmetric log-concave functions
on weak compositions.

## Main definitions

- `StatementOfTheorem`: The proposition that for any symmetric log-concave function on
  weak compositions, balanced vectors maximize the function and concentrated vectors minimize it.
-/

/-- **Main Theorem Statement.**
    For any symmetric log-concave function D on weak compositions E(n,d):
    - There exists a balanced vector b such that D(b) ≥ D(e) for all e
    - There exists a concentrated vector c such that D(c) ≤ D(e) for all e -/
@[expose] public def StatementOfTheorem : Prop :=
  ∀ (n : ℕ) (d : ℤ) (_hn : 0 < n) (_hd : 0 ≤ d) (F : SymmetricLogConcaveFunction n d),
    (∃ b : WeakComposition n d, IsBalanced b.toFun ∧ ∀ e, F.D e ≤ F.D b) ∧
    (∃ c : WeakComposition n d, IsConcentrated d c.toFun ∧ ∀ e, F.D c ≤ F.D e)
