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
  nonneg : ∀ i, 0 ≤ toFun i

namespace WeakComposition

public instance : CoeFun (WeakComposition n d) (fun _ => Fin n → ℤ) :=
  ⟨WeakComposition.toFun⟩

@[ext]
public lemma ext {e e' : WeakComposition n d} (h : ∀ i, e i = e' i) : e = e' := by
  cases e; cases e'; simp only [mk.injEq]; funext i; exact h i

/-- The concentrated vector: all zeros except `d` at position `k`. -/
@[expose] public def concentrated (hd : 0 ≤ d) (k : Fin n) : WeakComposition n d where
  toFun := fun i => if i = k then d else 0
  sum_eq := by simp only [sum_ite_eq', mem_univ, ite_true]
  nonneg := fun i => by split_ifs <;> omega

/-- Evaluation of concentrated at its concentration point. -/
@[simp]
public lemma concentrated_self (hd : 0 ≤ d) (k : Fin n) : (concentrated hd k) k = d := by
  simp only [concentrated, ite_true]

/-- Evaluation of concentrated away from its concentration point. -/
@[simp]
public lemma concentrated_ne (hd : 0 ≤ d) (k j : Fin n) (h : j ≠ k) :
    (concentrated hd k) j = 0 := by
  simp only [concentrated, h, ite_false]

/-- Key lemma: extract two positions from a sum with nested if-then-else. -/
public lemma sum_ite_ite_eq_add_add_sum_erase_erase
    (f : Fin n → ℤ) (i j : Fin n) (hij : i ≠ j) (a b : ℤ) :
    (∑ k, (if k = i then a else if k = j then b else f k))
      = a + b + ∑ k ∈ (univ.erase i).erase j, f k := by
  classical
  have hjmem : j ∈ (univ.erase i : Finset (Fin n)) :=
    mem_erase.mpr ⟨hij.symm, mem_univ j⟩
  -- First, split the sum: extract the i-th term
  have step1 : ∑ k, (if k = i then a else if k = j then b else f k) =
      a + ∑ k ∈ univ.erase i, (if k = j then b else f k) := by
    rw [← add_sum_erase _ _ (mem_univ i)]
    simp only [ite_true]
    congr 1
    apply sum_congr rfl
    intro k hk
    simp only [mem_erase, ne_eq] at hk
    simp only [hk.1, ite_false]
  -- Then, extract the j-th term from the remaining sum
  have step2 : ∑ k ∈ univ.erase i, (if k = j then b else f k) =
      b + ∑ k ∈ (univ.erase i).erase j, f k := by
    rw [← add_sum_erase _ _ hjmem]
    simp only [ite_true]
    congr 1
    apply sum_congr rfl
    intro k hk
    simp only [mem_erase, ne_eq] at hk
    simp only [hk.1, ite_false]
  calc ∑ k, (if k = i then a else if k = j then b else f k)
      = a + ∑ k ∈ univ.erase i, (if k = j then b else f k) := step1
    _ = a + (b + ∑ k ∈ (univ.erase i).erase j, f k) := by rw [step2]
    _ = a + b + ∑ k ∈ (univ.erase i).erase j, f k := by ring

/-- Auxiliary: the sum of a function that modifies two positions.
    This captures: if we change e at i to (e i - 1) and at j to (e j + 1),
    the total sum is preserved. -/
public lemma sum_modify_eq {e : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j)
    (hsum : ∑ k, e k = d) :
    ∑ k, (if k = i then e i - 1 else if k = j then e j + 1 else e k) = d := by
  classical
  have hmod : (∑ k, (if k = i then e i - 1 else if k = j then e j + 1 else e k))
      = (e i - 1) + (e j + 1) + ∑ k ∈ (univ.erase i).erase j, e k := by
    simpa using sum_ite_ite_eq_add_add_sum_erase_erase e i j hij (e i - 1) (e j + 1)

  have hi_sum : e i + ∑ k ∈ univ.erase i, e k = d := by
    rw [add_sum_erase _ _ (mem_univ i), hsum]

  have hj_sum : e j + ∑ k ∈ (univ.erase i).erase j, e k = ∑ k ∈ univ.erase i, e k := by
    have hjmem : j ∈ (univ.erase i : Finset (Fin n)) :=
      mem_erase.mpr ⟨hij.symm, mem_univ j⟩
    rw [add_sum_erase _ _ hjmem]

  have hdecomp : e i + e j + ∑ k ∈ (univ.erase i).erase j, e k = d := by
    linarith [hi_sum, hj_sum]

  calc (∑ k, (if k = i then e i - 1 else if k = j then e j + 1 else e k))
      = (e i - 1) + (e j + 1) + ∑ k ∈ (univ.erase i).erase j, e k := hmod
    _ = e i + e j + ∑ k ∈ (univ.erase i).erase j, e k := by ring
    _ = d := hdecomp

/-- Modify a composition by transferring one unit from position i to position j. -/
@[expose] public def modify (e : WeakComposition n d) (i j : Fin n)
    (hi : 1 ≤ e i) (hij : i ≠ j) : WeakComposition n d where
  toFun := fun k => if k = i then e i - 1 else if k = j then e j + 1 else e k
  sum_eq := sum_modify_eq hij e.sum_eq
  nonneg := fun k => by
    split_ifs with hki hkj
    · omega
    · have := e.nonneg j; omega
    · exact e.nonneg k

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

/-- A function on weak compositions that is symmetric under the Sₙ action. -/
@[expose] public def IsSymmetric (D : WeakComposition n d → ℚ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (e : WeakComposition n d),
    D ⟨e ∘ σ.symm,
       by simp only [comp_apply]
          have : ∑ x, e.toFun (σ.symm x) = ∑ x, e.toFun x := Equiv.sum_comp σ.symm e.toFun
          rw [this]; exact e.sum_eq,
       fun i => by simp only [comp_apply]; exact e.nonneg _⟩ = D e

/-- The log-concavity condition for D. -/
@[expose] public def SatisfiesLogConcavity (D : WeakComposition n d → ℚ) : Prop :=
  ∀ (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j)
    (hi : 1 ≤ e i) (hj : 1 ≤ e j),
    D e ^ 2 ≥ D (e.modify i j hi hij) * D (e.modify j i hj hij.symm)

/-- D is strictly positive. -/
@[expose] public def IsStrictlyPositive (D : WeakComposition n d → ℚ) : Prop :=
  ∀ e, 0 < D e

/-- A function `D` on weak compositions satisfying the three conditions:
    Sₙ-symmetry, log-concavity, and strict positivity.-/
public structure SymmetricLogConcaveFunction (n : ℕ) (d : ℤ) where
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
@[expose] public def LogConcaveOn (s : ℤ → ℚ) (q : ℤ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ q - 1 → s t ^ 2 ≥ s (t - 1) * s (t + 1)

/-- Apply log-concavity at a point. -/
public lemma LogConcaveOn.apply {s : ℤ → ℚ} {q : ℤ} (h : LogConcaveOn s q)
    (t : ℤ) (ht1 : 1 ≤ t) (htq : t ≤ q - 1) : s t ^ 2 ≥ s (t - 1) * s (t + 1) :=
  h t ht1 htq

/-- A sequence is palindromic on `[0, q]`. -/
@[expose] public def IsPalindromicOn (s : ℤ → ℚ) (q : ℤ) : Prop :=
  ∀ t, 0 ≤ t → t ≤ q → s t = s (q - t)

/-- Apply palindromicity at a point. -/
public lemma IsPalindromicOn.apply {s : ℤ → ℚ} {q : ℤ} (h : IsPalindromicOn s q)
    (t : ℤ) (ht0 : 0 ≤ t) (htq : t ≤ q) : s t = s (q - t) :=
  h t ht0 htq

/-- Construct an IsPalindromicOn proof. -/
public lemma IsPalindromicOn.mk {s : ℤ → ℚ} {q : ℤ}
    (h : ∀ t, 0 ≤ t → t ≤ q → s t = s (q - t)) :
    IsPalindromicOn s q :=
  h

/-- A sequence is positive on `[0, q]`. -/
@[expose] public def IsPositiveOn (s : ℤ → ℚ) (q : ℤ) : Prop :=
  ∀ t, 0 ≤ t → t ≤ q → 0 < s t

/-- Apply positivity at a point. -/
public lemma IsPositiveOn.apply {s : ℤ → ℚ} {q : ℤ} (h : IsPositiveOn s q)
    (t : ℤ) (ht0 : 0 ≤ t) (htq : t ≤ q) : 0 < s t :=
  h t ht0 htq

/-- The "imbalance" of a vector: sum of squares. -/
@[expose] public def imbalance (e : Fin n → ℤ) : ℤ := ∑ i, (e i) ^ 2

/-- Imbalance equals the sum of squares of entries. -/
public lemma imbalance_eq (e : Fin n → ℤ) : imbalance e = ∑ i, (e i) ^ 2 := by
  unfold imbalance; rfl

/-- The maximum entry of a vector. -/
@[expose] public noncomputable def maxEntry (e : Fin n → ℤ) (hn : 0 < n) : ℤ :=
  ((Finset.univ : Finset (Fin n)).image e).max'
    (by
      refine ⟨e ⟨0, hn⟩, ?_⟩
      exact Finset.mem_image.2 ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩)

/-- There exists an index achieving the maximum entry value. -/
public lemma exists_eq_maxEntry (e : Fin n → ℤ) (hn : 0 < n) :
    ∃ i : Fin n, e i = maxEntry e hn := by
  unfold maxEntry
  set s : Finset ℤ := (Finset.univ : Finset (Fin n)).image e
  have hs : s.Nonempty := ⟨e ⟨0, hn⟩, Finset.mem_image.2 ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  have hmem : s.max' hs ∈ s := Finset.max'_mem s hs
  obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hmem
  exact ⟨i, hi⟩

/-- Every entry is at most the maximum entry. -/
public lemma le_maxEntry (e : Fin n → ℤ) (hn : 0 < n) (i : Fin n) :
    e i ≤ maxEntry e hn := by
  unfold maxEntry
  set s : Finset ℤ := (Finset.univ : Finset (Fin n)).image e
  have hs : s.Nonempty := ⟨e ⟨0, hn⟩, Finset.mem_image.2 ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  have hi : e i ∈ s := Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
  exact Finset.le_max' s (e i) hi

/-- Count of non-zero entries. -/
public def nonzeroCount (e : Fin n → ℤ) : ℕ :=
  (Finset.univ.filter (fun i => e i ≠ 0)).card

/-- A vector is balanced if all entries differ by at most 1. -/
@[expose] public def IsBalanced (e : Fin n → ℤ) : Prop :=
  ∀ i j, e i ≤ e j + 1 ∧ e j ≤ e i + 1

/-- Negation of balanced: there exist indices with entries differing by at least 2. -/
public lemma not_isBalanced_iff {e : Fin n → ℤ} :
    ¬ IsBalanced e ↔ ∃ i j, i ≠ j ∧ e j + 2 ≤ e i := by
  unfold IsBalanced
  simp only [not_forall, not_and_or, not_le]
  constructor
  · intro ⟨i, j, hij⟩
    rcases hij with h1 | h2
    · exact ⟨i, j, fun heq => by simp only [heq] at h1; omega, by omega⟩
    · exact ⟨j, i, fun heq => by simp only [heq] at h2; omega, by omega⟩
  · intro ⟨i, j, _, hdiff⟩
    exact ⟨i, j, Or.inl (by omega)⟩

/-- A vector is concentrated if it equals `d • δₖ` for some `k`. -/
@[expose] public def IsConcentrated (d : ℤ) (e : Fin n → ℤ) : Prop :=
  ∃ k, ∀ i, e i = if i = k then d else 0
