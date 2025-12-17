/-
Copyright (c) 2025 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic

/-!

## WARNING

This repo contains AI generated proofs which may contain errors. To trust the claimed main result, and for it to be meaningful to have Lean check the actual proofs you must read, understand, and validate the content of this file.

-/


/-!
# Weak Compositions and Symmetric Log-Concave Functions

This file defines weak compositions of an integer `d` into `n` parts, along with
symmetric log-concave functions on the space of weak compositions.

## Main definitions

- `WeakComposition n d`: A vector `e : Fin n → ℤ` with `∑ eᵢ = d` and all entries
  non-negative.
- `SymmetricLogConcaveFunction n d`: A function `D : WeakComposition n d → ℚ` that is
  Sₙ-symmetric, log-concave, and strictly positive.
- `IsBalanced`: A vector where all entries differ by at most 1.
- `IsConcentrated`: A vector with all mass at a single position.

## Implementation notes

We use `ℤ` for entries rather than `ℕ` to simplify arithmetic in proofs, particularly
when dealing with the `modify` operation that transfers units between positions.
-/

open Finset BigOperators Function

/-- A weak composition of `d` into `n` parts is a vector `e : Fin n → ℤ` with
    `∑ eᵢ = d` and all entries non-negative. -/
public structure WeakComposition (n : ℕ) (d : ℤ) where
  /-- The underlying function from indices to integer values. -/
  toFun : Fin n → ℤ
  /-- The entries sum to `d`. -/
  sum_eq : ∑ i, toFun i = d
  /-- All entries are non-negative. -/
  nonneg : ∀ i, 0 ≤ toFun i := by grind


namespace WeakComposition

grind_pattern nonneg => self.toFun i
grind_pattern sum_eq => Finset.sum univ self.toFun

public instance : CoeFun (WeakComposition n d) (fun _ => Fin n → ℤ) :=
  ⟨WeakComposition.toFun⟩

@[ext]
public lemma ext {e e' : WeakComposition n d} (h : ∀ i, e i = e' i) : e = e' := by
  cases e; cases e'; simp only [mk.injEq]; funext i; exact h i

/-- The concentrated vector: all zeros except `d` at position `k`. -/
@[expose] public def concentrated (hd : 0 ≤ d) (k : Fin n) : WeakComposition n d where
  toFun := fun i => if i = k then d else 0
  sum_eq := by simp only [sum_ite_eq', mem_univ, ite_true]

/-- Key lemma: extract two positions from a sum with nested if-then-else. -/
public lemma sum_ite_ite_eq_add_add_sum_erase_erase
    (f : Fin n → ℤ) (i j : Fin n) (hij : i ≠ j) (a b : ℤ) :
    (∑ k, (if k = i then a else if k = j then b else f k))
      = a + b + ∑ k ∈ (univ.erase i).erase j, f k := by
  classical
  have hjmem : j ∈ (univ.erase i : Finset (Fin n)) := by grind
  -- First, split the sum: extract the i-th term
  have step1 : ∑ k, (if k = i then a else if k = j then b else f k) =
      a + ∑ k ∈ univ.erase i, (if k = j then b else f k) := by
    rw [← add_sum_erase _ _ (mem_univ i)]
    grind [sum_congr]
  -- Then, extract the j-th term from the remaining sum
  have step2 : ∑ k ∈ univ.erase i, (if k = j then b else f k) =
      b + ∑ k ∈ (univ.erase i).erase j, f k := by
    rw [← add_sum_erase _ _ hjmem]
    grind [sum_congr]
  grind

/-- Auxiliary: the sum of a function that modifies two positions.
    This captures: if we change e at i to (e i - 1) and at j to (e j + 1),
    the total sum is preserved. -/
public lemma sum_modify_eq {e : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j)
    (hsum : ∑ k, e k = d) :
    ∑ k, (if k = i then e i - 1 else if k = j then e j + 1 else e k) = d := by
  have hmod : (∑ k, (if k = i then e i - 1 else if k = j then e j + 1 else e k))
      = (e i - 1) + (e j + 1) + ∑ k ∈ (univ.erase i).erase j, e k := by
    simpa using sum_ite_ite_eq_add_add_sum_erase_erase e i j hij (e i - 1) (e j + 1)
  have hi_sum : e i + ∑ k ∈ univ.erase i, e k = d := by
    rw [add_sum_erase _ _ (mem_univ i), hsum]
  have hj_sum : e j + ∑ k ∈ (univ.erase i).erase j, e k = ∑ k ∈ univ.erase i, e k := by
    have hjmem : j ∈ (univ.erase i : Finset (Fin n)) := by grind
    rw [add_sum_erase _ _ hjmem]
  grind

/-- Modify a composition by transferring one unit from position i to position j. -/
@[expose] public def modify (e : WeakComposition n d) (i j : Fin n)
    (hi : 1 ≤ e i) (hij : i ≠ j) : WeakComposition n d where
  toFun := fun k => if k = i then e i - 1 else if k = j then e j + 1 else e k
  sum_eq := sum_modify_eq hij e.sum_eq

@[simp]
public lemma modify_at_i (e : WeakComposition n d) (i j : Fin n) (hi : 1 ≤ e i) (hij : i ≠ j) :
    (e.modify i j hi hij) i = e i - 1 := by simp only [modify, ite_true]

@[simp]
public lemma modify_at_j (e : WeakComposition n d) (i j : Fin n) (hi : 1 ≤ e i) (hij : i ≠ j) :
    (e.modify i j hi hij) j = e j + 1 := by simp only [modify, hij.symm, ite_false, ite_true]

@[simp]
public lemma modify_at_other (e : WeakComposition n d) (i j k : Fin n)
    (hi : 1 ≤ e i) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    (e.modify i j hi hij) k = e k := by
  simp only [modify, hki, hkj, ite_false]

end WeakComposition

variable {n : ℕ} {d : ℤ}

@[expose] public section
/-- A function on weak compositions that is symmetric under the Sₙ action. -/
def IsSymmetric (D : WeakComposition n d → ℚ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (e : WeakComposition n d),
    D ⟨e ∘ σ.symm, by
        have : ∑ x, e.toFun (σ.symm x) = ∑ x, e.toFun x := Equiv.sum_comp σ.symm e.toFun
        grind,
       fun i => by grind⟩ = D e

/-- The log-concavity condition for D. -/
def SatisfiesLogConcavity (D : WeakComposition n d → ℚ) : Prop :=
  ∀ (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j)
    (hi : 1 ≤ e i) (hj : 1 ≤ e j),
    D e ^ 2 ≥ D (e.modify i j hi hij) * D (e.modify j i hj hij.symm)

/-- D is strictly positive. -/
def IsStrictlyPositive (D : WeakComposition n d → ℚ) : Prop :=
  ∀ e, 0 < D e

/-- A function `D` on weak compositions satisfying the three conditions:
    Sₙ-symmetry, log-concavity, and strict positivity.-/
structure SymmetricLogConcaveFunction (n : ℕ) (d : ℤ) where
  /-- The function D : E(n,d) → ℚ -/
  D : WeakComposition n d → ℚ
  /-- D(e ∘ σ⁻¹) = D(e) for all permutations σ -/
  symmetric : IsSymmetric D
  /-- D(e)² ≥ D(e - δᵢ + δⱼ) · D(e + δᵢ - δⱼ) when eᵢ, eⱼ ≥ 1 -/
  logConcave : SatisfiesLogConcavity D
  /-- D(e) > 0 for all e -/
  strictlyPositive : IsStrictlyPositive D

/-! ### Auxiliary Definitions for Proofs -/

/-- A sequence `s : ℤ → ℚ` is log-concave on `[0, q]`. -/
def LogConcaveOn (s : ℤ → ℚ) (q : ℤ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ q - 1 → s t ^ 2 ≥ s (t - 1) * s (t + 1)

/-- A sequence is palindromic on `[0, q]`. -/
def IsPalindromicOn (s : ℤ → ℚ) (q : ℤ) : Prop :=
  ∀ t, 0 ≤ t → t ≤ q → s t = s (q - t)

/-- A sequence is positive on `[0, q]`. -/
def IsPositiveOn (s : ℤ → ℚ) (q : ℤ) : Prop :=
  ∀ t, 0 ≤ t → t ≤ q → 0 < s t

/-- The maximum entry of a vector. -/
noncomputable def maxEntry (e : Fin n → ℤ) (hn : 0 < n) : ℤ :=
  ((Finset.univ : Finset (Fin n)).image e).max' (⟨e ⟨0, hn⟩, by grind⟩)

/-- The "imbalance" of a vector: sum of squares. -/
def imbalance (e : Fin n → ℤ) : ℤ := ∑ i, (e i) ^ 2

/-- A vector is balanced if all entries differ by at most 1. -/
def IsBalanced (e : Fin n → ℤ) : Prop :=
  ∀ i j, e i ≤ e j + 1 ∧ e j ≤ e i + 1

/-- A vector is concentrated if it equals `d • δₖ` for some `k`. -/
def IsConcentrated (d : ℤ) (e : Fin n → ℤ) : Prop :=
  ∃ k, ∀ i, e i = if i = k then d else 0

/-! ### Slice Analysis Definitions -/

/-- Auxiliary: sum is preserved when we put t at position i and (q-t) at position j. -/
lemma sum_slice_eq {e : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (hsum : ∑ k, e k = d)
    (t : ℤ) :
    ∑ k, (if k = i then t else if k = j then e i + e j - t else e k) = d := by
  have hslice : (∑ k, (if k = i then t else if k = j then e i + e j - t else e k))
      = t + (e i + e j - t) + ∑ k ∈ (Finset.univ.erase i).erase j, e k := by
    simpa using WeakComposition.sum_ite_ite_eq_add_add_sum_erase_erase e i j hij t (e i + e j - t)
  have hi_sum : e i + ∑ k ∈ Finset.univ.erase i, e k = d := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i), hsum]
  have hj_sum : e j + ∑ k ∈ (Finset.univ.erase i).erase j, e k = ∑ k ∈ Finset.univ.erase i, e k := by
    have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin n)) :=
      Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    rw [Finset.add_sum_erase _ _ hjmem]
  grind

/-- Given a weak composition e and distinct positions i, j, construct the composition
    with value t at position i and (e_i + e_j - t) at position j. -/
def sliceComposition (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j)
    (t : ℤ) (ht : 0 ≤ t) (htq : t ≤ e i + e j) : WeakComposition n d where
  toFun := fun k => if k = i then t else if k = j then e i + e j - t else e k
  sum_eq := sum_slice_eq hij e.sum_eq t

/-- The slice sequence for D. -/
noncomputable def sliceSeq (D : WeakComposition n d → ℚ) (e : WeakComposition n d)
    (i j : Fin n) (hij : i ≠ j) : ℤ → ℚ := fun t =>
  if h : 0 ≤ t ∧ t ≤ e i + e j then
    D (sliceComposition e i j hij t h.1 h.2)
  else 0

end
