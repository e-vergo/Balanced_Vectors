/-
Copyright (c) 2025 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
module

public import BalancedVectors.MainTheorem
import all BalancedVectors.Proofs.helper_lemmas

open Finset BigOperators Function

namespace BalancedVectors

/-- **Main Theorem (Paper formulation - Combined).**
    For any symmetric log-concave function D on weak compositions E(n,d):
    - There exists a balanced vector b such that D(b) ≥ D(e) for all e
    - There exists a concentrated vector c such that D(c) ≤ D(e) for all e -/
public theorem mainTheorem : StatementOfTheorem := by
  intro n d hn hd F
  exact ⟨SymmetricLogConcaveFunction.exists_balanced_maximizer hn hd F,
          SymmetricLogConcaveFunction.exists_concentrated_minimizer hn hd F⟩

end BalancedVectors
