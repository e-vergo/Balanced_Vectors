/-
Copyright (c) 2025 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
module

public import BalancedVectors.Definitions
import all BalancedVectors.Definitions

/-!
# Helper Lemmas for the Main Theorem

This file contains the core lemmas needed to prove the main theorem about symmetric
log-concave functions on weak compositions.

## Main results

- `unimodal_of_logconcave_palindromic`: Log-concave palindromic sequences are unimodal.
- `balanced_maximizes`: Any weak composition can be improved to a balanced one.
- `concentrated_minimizes`: Any weak composition can be reduced to a concentrated one.
- `exists_balanced_maximizer`: There exists a balanced vector maximizing `D`.
- `exists_concentrated_minimizer`: There exists a concentrated vector minimizing `D`.

## Implementation notes

The proofs use well-founded recursion on the "imbalance" measure (sum of squares) for the
maximization direction, and on `d - maxEntry` for the minimization direction.
-/

open Finset BigOperators Function WeakComposition

/-- Evaluation of concentrated at its concentration point. -/
@[simp]
public lemma concentrated_self (hd : 0 ≤ d) (k : Fin n) : (concentrated hd k) k = d := by
  simp only [concentrated, ite_true]

/-- Evaluation of concentrated away from its concentration point. -/
@[simp]
public lemma concentrated_ne (hd : 0 ≤ d) (k j : Fin n) (h : j ≠ k) :
    (concentrated hd k) j = 0 := by
  simp only [concentrated, h, ite_false]

/-- Apply log-concavity at a point. -/
lemma LogConcaveOn.apply {s : ℤ → ℚ} {q : ℤ} (h : LogConcaveOn s q)
    (t : ℤ) (ht1 : 1 ≤ t) (htq : t ≤ q - 1) : s t ^ 2 ≥ s (t - 1) * s (t + 1) :=
  h t ht1 htq

/-- Apply positivity at a point. -/
lemma IsPositiveOn.apply {s : ℤ → ℚ} {q : ℤ} (h : IsPositiveOn s q)
    (t : ℤ) (ht0 : 0 ≤ t) (htq : t ≤ q) : 0 < s t :=
  h t ht0 htq


/-- Apply palindromicity at a point. -/
lemma IsPalindromicOn.apply {s : ℤ → ℚ} {q : ℤ} (h : IsPalindromicOn s q)
    (t : ℤ) (ht0 : 0 ≤ t) (htq : t ≤ q) : s t = s (q - t) :=
  h t ht0 htq

/-- Construct an IsPalindromicOn proof. -/
lemma IsPalindromicOn.mk {s : ℤ → ℚ} {q : ℤ}
    (h : ∀ t, 0 ≤ t → t ≤ q → s t = s (q - t)) :
    IsPalindromicOn s q := h

/-- Imbalance equals the sum of squares of entries. -/
lemma imbalance_eq (e : Fin n → ℤ) : imbalance e = ∑ i, (e i) ^ 2 := by
  unfold imbalance; rfl

/-- There exists an index achieving the maximum entry value. -/
lemma exists_eq_maxEntry (e : Fin n → ℤ) (hn : 0 < n) :
    ∃ i : Fin n, e i = maxEntry e hn := by
  unfold maxEntry
  set s : Finset ℤ := (Finset.univ : Finset (Fin n)).image e
  have hs : s.Nonempty := ⟨e ⟨0, hn⟩, Finset.mem_image.2 ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  have hmem : s.max' hs ∈ s := Finset.max'_mem s hs
  obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hmem
  exact ⟨i, hi⟩

/-- Every entry is at most the maximum entry. -/
lemma le_maxEntry (e : Fin n → ℤ) (hn : 0 < n) (i : Fin n) :
    e i ≤ maxEntry e hn := by
  unfold maxEntry
  set s : Finset ℤ := (Finset.univ : Finset (Fin n)).image e
  have hs : s.Nonempty := ⟨e ⟨0, hn⟩, Finset.mem_image.2 ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  have hi : e i ∈ s := Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
  exact Finset.le_max' s (e i) hi


/-- Each entry of a weak composition is bounded by d. -/
lemma WeakComposition.entry_le_d (e : WeakComposition n d) (i : Fin n) : e i ≤ d := by
  have h := Finset.single_le_sum (fun j _ => e.nonneg j) (Finset.mem_univ i)
  linarith [e.sum_eq]

/-- The domain WeakComposition n d is finite when d ≥ 0. -/
instance WeakComposition.finite (hd : 0 ≤ d) : Finite (WeakComposition n d) := by
  classical
  let bound := d.toNat + 1
  let f : WeakComposition n d → (Fin n → Fin bound) := fun e i =>
    ⟨(e i).toNat, by
      have hle := WeakComposition.entry_le_d e i
      have hnonneg := e.nonneg i
      omega⟩
  apply Finite.of_injective f
  intro e₁ e₂ heq
  ext i
  have h : (f e₁) i = (f e₂) i := congrFun heq i
  simp only [f, Fin.mk.injEq] at h
  have h1 := e₁.nonneg i
  have h2 := e₂.nonneg i
  omega

/-- WeakComposition n d is nonempty when n > 0 and d ≥ 0. -/
lemma WeakComposition.nonempty (hn : 0 < n) (hd : 0 ≤ d) : Nonempty (WeakComposition n d) := by
  classical
  refine ⟨⟨fun i => if i = ⟨0, hn⟩ then d else 0, ?_, ?_⟩⟩
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · intro i
    show 0 ≤ if i = ⟨0, hn⟩ then d else 0
    split_ifs <;> omega

/-! ### Key Lemma: Log-concave palindromic sequences are unimodal -/

/-- If `x > 0` and `x² ≥ 1`, then `x ≥ 1`. -/
lemma one_le_of_one_le_sq_pos {x : ℚ} (hx : 0 < x) (hsq : 1 ≤ x ^ 2) : 1 ≤ x := by
  by_contra h
  push_neg at h
  have hsq' : x ^ 2 < 1 := by nlinarith
  linarith

/-- Auxiliary lemma: if a ratio sequence decreases at each step, it is antitone. -/
lemma ratio_antitone_aux (r : ℤ → ℚ) (q : ℤ)
    (hr_step : ∀ t, 0 ≤ t → t + 2 ≤ q → r (t + 1) ≤ r t) :
    ∀ a b, 0 ≤ a → b + 1 ≤ q → a ≤ b → r b ≤ r a := by
  intro a b ha0 hbq hab
  obtain ⟨d, hd⟩ : ∃ d : ℕ, b = a + d := ⟨(b - a).toNat, by omega⟩
  subst hd
  clear hab
  induction d with
  | zero => simp
  | succ n ih =>
    have hn1q : a + ↑n + 1 ≤ q := by omega
    have ih' := ih hn1q
    have hn0 : 0 ≤ a + n := by omega
    have hn2q : (a + ↑n) + 2 ≤ q := by omega
    have hstep := hr_step (a + n) hn0 hn2q
    calc r (a + (↑n + 1))
        = r (a + ↑n + 1) := by ring_nf
      _ ≤ r (a + ↑n) := hstep
      _ ≤ r a := ih'

/-- The main unimodality lemma. -/
theorem unimodal_of_logconcave_palindromic {s : ℤ → ℚ} {q : ℤ} (hq : 0 ≤ q)
    (hpos : IsPositiveOn s q) (hlc : LogConcaveOn s q) (hpal : IsPalindromicOn s q) :
    (∀ t, 0 ≤ t → 2 * t < q → s t ≤ s (t + 1)) ∧
    (∀ t, 2 * t > q → t ≤ q → s t ≤ s (t - 1)) := by
  classical
  let r : ℤ → ℚ := fun t => s (t + 1) / s t
  have hs_pos : ∀ t, 0 ≤ t → t ≤ q → 0 < s t := fun t ht0 htq => hpos.apply t ht0 htq
  have hr_pos : ∀ t, 0 ≤ t → t + 1 ≤ q → 0 < r t := by
    intro t ht0 ht1q
    have hst : 0 < s t := hs_pos t ht0 (by omega)
    have hst1 : 0 < s (t + 1) := hs_pos (t + 1) (by omega) ht1q
    exact div_pos hst1 hst
  have hr_antitone_step : ∀ t, 0 ≤ t → t + 2 ≤ q → r (t + 1) ≤ r t := by
    intro t ht0 ht2q
    have ht1_lo : 1 ≤ t + 1 := by omega
    have ht1_hi : t + 1 ≤ q - 1 := by omega
    have hlc_at := hlc.apply (t + 1) ht1_lo ht1_hi
    have hst : 0 < s t := hs_pos t ht0 (by omega)
    have hst1 : 0 < s (t + 1) := hs_pos (t + 1) (by omega) (by omega)
    simp only [r]
    rw [div_le_div_iff₀ hst1 hst]
    have h3 : s (t + 1 - 1) = s t := by ring_nf
    have h4 : s (t + 1 + 1) = s (t + 2) := by ring_nf
    have h5 : t + 1 + 1 = t + 2 := by ring
    calc s (t + 1 + 1) * s t
        = s (t + 2) * s t := by rw [h5]
      _ = s t * s (t + 2) := by ring
      _ ≤ s (t + 1) ^ 2 := by simp only [h3, h4] at hlc_at; exact hlc_at
      _ = s (t + 1) * s (t + 1) := by ring
  have hr_antitone : ∀ a b, 0 ≤ a → b + 1 ≤ q → a ≤ b → r b ≤ r a :=
    ratio_antitone_aux r q hr_antitone_step
  have hr_pal : ∀ t, 0 ≤ t → t + 1 ≤ q → r (q - 1 - t) = (r t)⁻¹ := by
    intro t ht0 ht1q
    have hst : 0 < s t := hs_pos t ht0 (by omega)
    have hst1 : 0 < s (t + 1) := hs_pos (t + 1) (by omega) ht1q
    have hpal_t : s t = s (q - t) := hpal.apply t ht0 (by omega)
    have hpal_t1 : s (t + 1) = s (q - (t + 1)) := hpal.apply (t + 1) (by omega) ht1q
    have h1 : q - 1 - t + 1 = q - t := by ring
    have h2 : q - (t + 1) = q - 1 - t := by ring
    simp only [r]
    rw [h1, inv_div]
    rw [hpal_t.symm, ← h2, hpal_t1]
  have hincr : ∀ t, 0 ≤ t → 2 * t < q → s t ≤ s (t + 1) := by
    intro t ht0 htmid
    have ht1q : t + 1 ≤ q := by omega
    have hrt_pos : 0 < r t := hr_pos t ht0 ht1q
    have ht_le : t ≤ q - 1 - t := by omega
    have hb1q : (q - 1 - t) + 1 ≤ q := by omega
    have hrat_cmp : r (q - 1 - t) ≤ r t := hr_antitone t (q - 1 - t) ht0 hb1q ht_le
    rw [hr_pal t ht0 ht1q] at hrat_cmp
    have hsq : 1 ≤ (r t) ^ 2 := by
      have hne : r t ≠ 0 := ne_of_gt hrt_pos
      have h : (r t)⁻¹ * r t ≤ r t * r t := by nlinarith
      simp only [inv_mul_cancel₀ hne] at h
      calc 1 ≤ r t * r t := h
        _ = (r t) ^ 2 := by ring
    have hrt_ge1 : 1 ≤ r t := one_le_of_one_le_sq_pos hrt_pos hsq
    have hst_pos : 0 < s t := hs_pos t ht0 (by omega)
    have hne : s t ≠ 0 := ne_of_gt hst_pos
    calc s t
        = s t * 1 := by ring
      _ ≤ s t * r t := by nlinarith
      _ = s t * (s (t + 1) / s t) := rfl
      _ = s (t + 1) := by field_simp
  have hdecr : ∀ t, 2 * t > q → t ≤ q → s t ≤ s (t - 1) := by
    intro t htbig htq
    have htm1_lo : 0 ≤ t - 1 := by omega
    have htm1_hi : t - 1 ≤ q := by omega
    rw [hpal.apply t (by omega) htq, hpal.apply (t - 1) htm1_lo htm1_hi]
    set u := q - t with hu_def
    have hu_lo : 0 ≤ u := by omega
    have hu_mid : 2 * u < q := by omega
    have heq : q - (t - 1) = u + 1 := by omega
    rw [heq]
    exact hincr u hu_lo hu_mid
  exact ⟨hincr, hdecr⟩

/-! ### Imbalance measure for termination -/

/-- Key algebraic fact: (a-1)² + (b+1)² < a² + b² when a ≥ b + 2. -/
lemma sq_transfer_decreases {a b : ℤ} (h : a ≥ b + 2) :
    (a - 1)^2 + (b + 1)^2 < a^2 + b^2 := by
  have expand : (a - 1)^2 + (b + 1)^2 = a^2 + b^2 + 2*(b - a + 1) := by ring
  have neg : b - a + 1 ≤ -1 := by omega
  omega

/-- If e_i ≥ e_j + 2, then modifying from i to j decreases imbalance. -/
lemma imbalance_decreases (e : WeakComposition n d) (i j : Fin n)
    (hij : i ≠ j) (hi : 1 ≤ e i) (hdiff : e j + 2 ≤ e i) :
    imbalance (e.modify i j hi hij).toFun < imbalance e.toFun := by
  classical
  rw [imbalance_eq, imbalance_eq]
  set rest : ℤ := ∑ k ∈ (univ.erase i).erase j, (e k)^2 with hrest
  have hpow_mod : ∀ k, (e.modify i j hi hij).toFun k ^ 2 =
      (if k = i then (e i - 1)^2 else if k = j then (e j + 1)^2 else (e k)^2) := by
    intro k
    by_cases hki : k = i
    · subst hki; simp only [modify_at_i, ite_true]
    · by_cases hkj : k = j
      · subst hkj; simp only [modify_at_j, hki, ite_false, ite_true]
      · rw [modify_at_other e i j k hi hij hki hkj]; simp only [hki, hkj, ite_false]
  have hsum_mod : (∑ k, (e.modify i j hi hij).toFun k ^ 2)
      = (e i - 1)^2 + (e j + 1)^2 + rest := by
    calc (∑ k, (e.modify i j hi hij).toFun k ^ 2)
        = ∑ k, (if k = i then (e i - 1)^2 else if k = j then (e j + 1)^2 else (e k)^2) := by
            refine sum_congr rfl ?_; intro k _; exact hpow_mod k
      _ = (e i - 1)^2 + (e j + 1)^2 + ∑ k ∈ (univ.erase i).erase j, (e k)^2 := by
            simpa using sum_ite_ite_eq_add_add_sum_erase_erase
              (fun k => (e k)^2) i j hij ((e i - 1)^2) ((e j + 1)^2)
      _ = (e i - 1)^2 + (e j + 1)^2 + rest := rfl
  have hsum_orig : (∑ k, (e k)^2) = (e i)^2 + (e j)^2 + rest := by
    have h := sum_ite_ite_eq_add_add_sum_erase_erase (fun k => (e k)^2) i j hij ((e i)^2) ((e j)^2)
    convert h using 1
    apply sum_congr rfl
    intro k _
    by_cases hki : k = i
    · subst hki; simp
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · simp [hki, hkj]
  have hsq : (e i - 1)^2 + (e j + 1)^2 < (e i)^2 + (e j)^2 :=
    sq_transfer_decreases hdiff
  calc ∑ k, (e.modify i j hi hij).toFun k ^ 2
      = (e i - 1)^2 + (e j + 1)^2 + rest := hsum_mod
    _ < (e i)^2 + (e j)^2 + rest := by linarith
    _ = ∑ k, (e k)^2 := hsum_orig.symm

/-- Negation of balanced: there exist indices with entries differing by at least 2. -/
lemma not_isBalanced_iff {e : Fin n → ℤ} :
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

/-- If a vector is not balanced, there exist i, j with e_i ≥ e_j + 2. -/
lemma exists_imbalanced_pair (e : Fin n → ℤ) (h : ¬ IsBalanced e) :
    ∃ i j, i ≠ j ∧ e j + 2 ≤ e i :=
  not_isBalanced_iff.mp h

/-! ### Slice Analysis -/

/-- The slice sequence is palindromic when D is symmetric. -/
lemma sliceSeq_palindromic (D : WeakComposition n d → ℚ)
    (hsym : IsSymmetric D) (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) :
    IsPalindromicOn (sliceSeq D e i j hij) (e i + e j) := by
  apply IsPalindromicOn.mk
  intro t ht htq
  set q := e i + e j with hq
  have ht' : 0 ≤ q - t := by omega
  have htq' : q - t ≤ q := by omega
  unfold sliceSeq
  rw [dif_pos ⟨ht, htq⟩, dif_pos ⟨ht', htq'⟩]
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσ
  have hsym_app := hsym σ (sliceComposition e i j hij (q - t) ht' htq')
  suffices h : (⟨(sliceComposition e i j hij (q - t) ht' htq') ∘ σ.symm,
      by simp only [comp_apply]
         have hsum : ∑ x, (sliceComposition e i j hij (q - t) ht' htq').toFun (σ.symm x) =
             ∑ x, (sliceComposition e i j hij (q - t) ht' htq').toFun x :=
           Equiv.sum_comp σ.symm _
         rw [hsum]; exact (sliceComposition e i j hij (q - t) ht' htq').sum_eq,
      fun k => by simp only [comp_apply]; exact (sliceComposition e i j hij (q - t) ht' htq').nonneg _⟩ :
      WeakComposition n d) = sliceComposition e i j hij t ht htq by
    rw [← h, hsym_app]
  refine WeakComposition.ext (fun k => ?_)
  simp only [sliceComposition, comp_apply]
  by_cases hki : k = i
  · have hswap_k : σ.symm k = j := by rw [hki, hσ, Equiv.symm_swap, Equiv.swap_apply_left]
    rw [hswap_k]
    simp only [hki, hij.symm, ite_false, ite_true]
    ring
  · by_cases hkj : k = j
    · have hswap_k : σ.symm k = i := by rw [hkj, hσ, Equiv.symm_swap, Equiv.swap_apply_right]
      rw [hswap_k]
      simp only [hkj, ite_true, if_neg hij.symm]; ring
    · have hswap_other : σ.symm k = k := by
        rw [hσ, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hki hkj]
      rw [hswap_other]
      simp only [hki, hkj, ite_false]

/-- The slice sequence is log-concave when D satisfies log-concavity. -/
lemma sliceSeq_logconcave (D : WeakComposition n d → ℚ)
    (hlc : SatisfiesLogConcavity D) (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) :
    LogConcaveOn (sliceSeq D e i j hij) (e i + e j) := by
  intro t ht htq
  set q := e i + e j with hq
  have htm1_lo : 0 ≤ t - 1 := by omega
  have htm1_hi : t - 1 ≤ q := by omega
  have htp1_lo : 0 ≤ t + 1 := by omega
  have htp1_hi : t + 1 ≤ q := by omega
  have ht_lo : 0 ≤ t := by omega
  have ht_hi : t ≤ q := by omega
  set e0 := sliceComposition e i j hij t ht_lo ht_hi with he0
  have he0_i : e0 i = t := by simp only [he0, sliceComposition, ite_true]
  have he0_j : e0 j = q - t := by
    simp only [he0, sliceComposition, hij.symm, ite_false, ite_true]
    rw [hq]
  have hi_ge1 : 1 ≤ e0 i := by rw [he0_i]; omega
  have hj_ge1 : 1 ≤ e0 j := by rw [he0_j]; omega
  have hlc_app := hlc e0 i j hij hi_ge1 hj_ge1
  have hmod_ij : e0.modify i j hi_ge1 hij = sliceComposition e i j hij (t - 1) htm1_lo htm1_hi := by
    refine WeakComposition.ext (fun m => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hmi : m = i
    · simp only [hmi, ite_true, he0_i]
    · by_cases hmj : m = j
      · simp only [hmj, ite_true, if_neg hij.symm, he0_j]; ring
      · simp only [hmi, hmj, ite_false, he0, sliceComposition]
  have hmod_ji : e0.modify j i hj_ge1 hij.symm = sliceComposition e i j hij (t + 1) htp1_lo htp1_hi := by
    refine WeakComposition.ext (fun m => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hmi : m = i
    · simp only [hmi, ite_true, if_neg hij, he0_i]
    · by_cases hmj : m = j
      · simp only [hmj, ite_true, if_neg hij.symm, he0_j]; ring
      · simp only [hmi, hmj, ite_false, he0, sliceComposition]
  rw [hmod_ij, hmod_ji] at hlc_app
  unfold sliceSeq
  rw [dif_pos ⟨ht_lo, ht_hi⟩, dif_pos ⟨htm1_lo, htm1_hi⟩, dif_pos ⟨htp1_lo, htp1_hi⟩]
  exact hlc_app

/-- The slice sequence is positive when D is positive. -/
lemma sliceSeq_positive (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) :
    IsPositiveOn (sliceSeq D e i j hij) (e i + e j) := by
  intro t ht htq
  simp only [sliceSeq, ht, htq, and_self, ↓reduceDIte]
  exact hpos _

/-! ### Main Theorems -/

/-- The balancing step weakly increases D when entries differ by ≥ 2. -/
lemma balancing_increases_D (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D)
    (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) (hi : 1 ≤ e i) (hdiff : e j + 2 ≤ e i) :
    D e ≤ D (e.modify i j hi hij) := by
  set q := e i + e j with hq_def
  have hpal := sliceSeq_palindromic D hsym e i j hij
  have hlc' := sliceSeq_logconcave D hlc e i j hij
  have hpos' := sliceSeq_positive D hpos e i j hij
  have hq_nonneg : 0 ≤ q := by
    have := e.nonneg i
    have := e.nonneg j
    omega
  have hunimodal := unimodal_of_logconcave_palindromic hq_nonneg hpos' hlc' hpal
  have hei_lo : 0 ≤ e i := e.nonneg i
  have hei_hi : e i ≤ q := by simp only [hq_def]; linarith [e.nonneg j]
  have hem1_lo : 0 ≤ e i - 1 := by omega
  have hem1_hi : e i - 1 ≤ q := by simp only [hq_def]; omega
  have he_eq_slice : e = sliceComposition e i j hij (e i) hei_lo hei_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [sliceComposition]
    by_cases hki : k = i
    · simp only [hki, ite_true]
    · by_cases hkj : k = j
      · simp only [hkj, ite_true, if_neg hij.symm]; ring
      · simp only [hki, hkj, ite_false]
  have hmod_eq_slice : e.modify i j hi hij = sliceComposition e i j hij (e i - 1) hem1_lo hem1_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hki : k = i
    · simp only [hki, ite_true]
    · by_cases hkj : k = j
      · simp only [hkj, ite_true, if_neg hij.symm]; ring
      · simp only [hki, hkj, ite_false]
  have h2ei_gt_q : 2 * (e i) > q := by simp only [hq_def]; omega
  have hdecr := hunimodal.2 (e i) h2ei_gt_q hei_hi
  have hslice_ei : sliceSeq D e i j hij (e i) = D (sliceComposition e i j hij (e i) hei_lo hei_hi) := by
    unfold sliceSeq
    rw [dif_pos ⟨hei_lo, hei_hi⟩]
  have hslice_em1 : sliceSeq D e i j hij (e i - 1) =
      D (sliceComposition e i j hij (e i - 1) hem1_lo hem1_hi) := by
    unfold sliceSeq
    rw [dif_pos ⟨hem1_lo, hem1_hi⟩]
  rw [hslice_ei, hslice_em1, ← he_eq_slice, ← hmod_eq_slice] at hdecr
  exact hdecr

/-- Imbalance is non-negative for weak compositions. -/
lemma imbalance_nonneg (e : WeakComposition n d) : 0 ≤ imbalance e.toFun := by
  unfold imbalance
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

/-- Any vector can be transformed to a balanced vector while increasing D. -/
theorem balanced_maximizes (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D) :
    ∀ e : WeakComposition n d, ∃ e' : WeakComposition n d, IsBalanced e'.toFun ∧ D e ≤ D e' := by
  intro e
  have h_nonneg : 0 ≤ imbalance e.toFun := imbalance_nonneg e
  generalize hm : (imbalance e.toFun).toNat = m
  induction m using Nat.strong_induction_on generalizing e with
  | _ m ih =>
    by_cases hbal : IsBalanced e.toFun
    · exact ⟨e, hbal, le_refl _⟩
    · obtain ⟨i, j, hij, hdiff⟩ := exists_imbalanced_pair e.toFun hbal
      have hi : 1 ≤ e i := by linarith [e.nonneg j]
      set e1 := e.modify i j hi hij with he1
      have hD_incr : D e ≤ D e1 := balancing_increases_D D hpos hsym hlc e i j hij hi hdiff
      have himb_decr : imbalance e1.toFun < imbalance e.toFun :=
        imbalance_decreases e i j hij hi hdiff
      have h1_nonneg : 0 ≤ imbalance e1.toFun := imbalance_nonneg e1
      have h_pos : 0 < imbalance e.toFun := by
        have hej_nonneg : 0 ≤ e j := e.nonneg j
        have hei : 2 ≤ e i := by omega
        have hsq : 4 ≤ (e i)^2 := by nlinarith
        calc imbalance e.toFun
            = ∑ k, (e k)^2 := rfl
          _ ≥ (e i)^2 := Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
          _ ≥ 4 := hsq
          _ > 0 := by omega
      have hm1 : (imbalance e1.toFun).toNat < m := by
        rw [← hm]
        rw [Int.toNat_lt_toNat h_pos]
        exact himb_decr
      obtain ⟨e', hbal', hD'⟩ := ih (imbalance e1.toFun).toNat hm1 e1 h1_nonneg rfl
      exact ⟨e', hbal', le_trans hD_incr hD'⟩

/-- When e_i > e_j, moving mass from j to i (concentrating) decreases D. -/
lemma concentrating_decreases_D (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D)
    (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) (hj : 1 ≤ e j) (hdiff : e j < e i) :
    D (e.modify j i hj hij.symm) ≤ D e := by
  set q := e j + e i with hq_def
  have hpal := sliceSeq_palindromic D hsym e j i hij.symm
  have hlc' := sliceSeq_logconcave D hlc e j i hij.symm
  have hpos' := sliceSeq_positive D hpos e j i hij.symm
  have hq_nonneg : 0 ≤ q := by linarith [e.nonneg i, e.nonneg j]
  have hunimodal := unimodal_of_logconcave_palindromic hq_nonneg hpos' hlc' hpal
  have hej_lo : 0 ≤ e j := e.nonneg j
  have hej_hi : e j ≤ q := by simp only [hq_def]; linarith [e.nonneg i]
  have hejm1_lo : 0 ≤ e j - 1 := by omega
  have hejm1_hi : e j - 1 ≤ q := by simp only [hq_def]; omega
  have he_eq_slice : e = sliceComposition e j i hij.symm (e j) hej_lo hej_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [sliceComposition]
    by_cases hkj : k = j
    · simp only [hkj, ite_true]
    · by_cases hki : k = i
      · simp only [hki, ite_true, if_neg hij]; ring
      · simp only [hkj, hki, ite_false]
  have hmod_eq_slice : e.modify j i hj hij.symm =
      sliceComposition e j i hij.symm (e j - 1) hejm1_lo hejm1_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hkj : k = j
    · simp only [hkj, ite_true]
    · by_cases hki : k = i
      · simp only [hki, ite_true, if_neg hij]; ring
      · simp only [hkj, hki, ite_false]
  have h2ej_lt_q : 2 * (e j - 1) < q := by simp only [hq_def]; omega
  have hincr := hunimodal.1 (e j - 1) hejm1_lo h2ej_lt_q
  have hslice_ej : sliceSeq D e j i hij.symm (e j) =
      D (sliceComposition e j i hij.symm (e j) hej_lo hej_hi) := by
    unfold sliceSeq; rw [dif_pos ⟨hej_lo, hej_hi⟩]
  have hslice_ejm1 : sliceSeq D e j i hij.symm (e j - 1) =
      D (sliceComposition e j i hij.symm (e j - 1) hejm1_lo hejm1_hi) := by
    unfold sliceSeq; rw [dif_pos ⟨hejm1_lo, hejm1_hi⟩]
  simp only [Int.sub_add_cancel] at hincr
  rw [hslice_ejm1, hslice_ej, ← hmod_eq_slice, ← he_eq_slice] at hincr
  exact hincr

/-! ### MaxEntry for termination of concentrated_minimizes -/

namespace WeakComposition

/-- The maximum entry of a weak composition is at most `d`. -/
lemma maxEntry_le_d (e : WeakComposition n d) (hn : 0 < n) :
    maxEntry e.toFun hn ≤ d := by
  obtain ⟨i, hi⟩ := exists_eq_maxEntry e.toFun hn
  have hle : e i ≤ ∑ k, e k :=
    Finset.single_le_sum (fun k _ => e.nonneg k) (Finset.mem_univ i)
  rw [e.sum_eq] at hle
  linarith

/-- If some entry equals `d`, then the composition is concentrated at that index. -/
lemma concentrated_of_entry_eq_d (e : WeakComposition n d) (i : Fin n) (hi : e i = d) :
    IsConcentrated d e.toFun := by
  refine ⟨i, ?_⟩
  intro j
  by_cases hji : j = i
  · simp only [hji, ite_true, hi]
  · simp only [hji, ite_false]
    have hsplit : (∑ k, e k) = e i + ∑ k ∈ (Finset.univ.erase i), e k := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : (∑ k ∈ (Finset.univ.erase i), e k) = 0 := by
      have := e.sum_eq
      linarith
    have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin n)) := by simp [hji]
    have hle : e j ≤ ∑ k ∈ (Finset.univ.erase i), e k :=
      Finset.single_le_sum (fun k _ => e.nonneg k) hjmem
    have hge : 0 ≤ e j := e.nonneg j
    omega

/-- If the maximum entry equals `d`, the composition is concentrated. -/
lemma concentrated_of_maxEntry_eq_d (e : WeakComposition n d) (hn : 0 < n)
    (hmax : maxEntry e.toFun hn = d) : IsConcentrated d e.toFun := by
  obtain ⟨i, hi⟩ := exists_eq_maxEntry e.toFun hn
  have hid : e i = d := by linarith
  exact concentrated_of_entry_eq_d e i hid

/-- Moving mass to a maximizer increases maxEntry by 1. -/
lemma maxEntry_modify_to_maximizer
    (e : WeakComposition n d) (hn : 0 < n)
    (i j : Fin n) (hij : i ≠ j)
    (hj : 1 ≤ e j)
    (hiMax : e i = maxEntry e.toFun hn) :
    maxEntry (e.modify j i hj hij.symm).toFun hn = maxEntry e.toFun hn + 1 := by
  set e1 := e.modify j i hj hij.symm with he1
  have h_i_val : e1 i = e i + 1 := modify_at_j e j i hj hij.symm
  have h_j_val : e1 j = e j - 1 := modify_at_i e j i hj hij.symm
  have hlow : maxEntry e.toFun hn + 1 ≤ maxEntry e1.toFun hn := by
    have hle : e1 i ≤ maxEntry e1.toFun hn := le_maxEntry e1.toFun hn i
    linarith
  obtain ⟨k, hk⟩ := exists_eq_maxEntry e1.toFun hn
  have hk_bound : e1 k ≤ maxEntry e.toFun hn + 1 := by
    by_cases hki : k = i
    · rw [hki, h_i_val, hiMax]
    · by_cases hkj : k = j
      · have hj_le : e j ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn j
        rw [hkj, h_j_val]
        omega
      · have h_other : e1 k = e k := modify_at_other e j i k hj hij.symm hkj hki
        have hk_le : e k ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn k
        linarith
  have hup : maxEntry e1.toFun hn ≤ maxEntry e.toFun hn + 1 := by linarith
  omega

/-- When maxEntry increases, the termination measure `d - maxEntry` decreases. -/
lemma measure_decreases_of_maxEntry_increases
    (e e1 : WeakComposition n d) (hn : 0 < n)
    (hmax : maxEntry e1.toFun hn = maxEntry e.toFun hn + 1)
    (hmax_lt : maxEntry e.toFun hn < d) :
    (d - maxEntry e1.toFun hn).toNat < (d - maxEntry e.toFun hn).toNat := by
  have hpos : 0 < d - maxEntry e.toFun hn := by omega
  have hlt : d - maxEntry e1.toFun hn < d - maxEntry e.toFun hn := by omega
  have hpos' : 0 ≤ d - maxEntry e1.toFun hn := by omega
  omega

end WeakComposition

/-- If e is not concentrated and d > 0, there exist distinct i, j with e.i > 0 and e.j > 0. -/
lemma exists_two_positive (hd : 0 < d) (e : WeakComposition n d)
    (h : ¬ IsConcentrated d e.toFun) : ∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j := by
  by_contra hcontra
  push_neg at hcontra
  have hone : ∃ k₀, ∀ i, i ≠ k₀ → e i = 0 := by
    by_cases hall : ∀ i, e i = 0
    · have hsum_eq : d = ∑ i, e i := e.sum_eq.symm
      simp only [hall, Finset.sum_const_zero] at hsum_eq
      omega
    · push_neg at hall
      obtain ⟨k₀, hk₀⟩ := hall
      use k₀
      intro i hik
      by_contra hi
      have hpos_k₀ : 0 < e k₀ := by have := e.nonneg k₀; omega
      have hpos_i : 0 < e i := by have := e.nonneg i; omega
      have hcontr_app := hcontra i k₀ hik hpos_i
      omega
  obtain ⟨k₀, hk₀⟩ := hone
  apply h
  use k₀
  intro i
  by_cases hik : i = k₀
  · simp only [hik, ite_true]
    have hsum : d = ∑ m, e m := e.sum_eq.symm
    have hsplit : ∑ m, e m = e k₀ + ∑ m ∈ Finset.univ.erase k₀, e m := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
    rw [hsplit] at hsum
    have hrest : ∑ m ∈ Finset.univ.erase k₀, e m = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      exact hk₀ m (Finset.ne_of_mem_erase hm)
    omega
  · simp only [hik, ite_false]
    exact hk₀ i hik

/-- Helper: D decreases when moving toward the max, even in the equal case. -/
lemma concentrating_to_max_decreases_D (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D)
    (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j)
    (hj : 1 ≤ e j) (hdiff : e j ≤ e i) :
    D (e.modify j i hj hij.symm) ≤ D e := by
  set q := e j + e i with hq_def
  have hpal := sliceSeq_palindromic D hsym e j i hij.symm
  have hlc' := sliceSeq_logconcave D hlc e j i hij.symm
  have hpos' := sliceSeq_positive D hpos e j i hij.symm
  have hq_nonneg : 0 ≤ q := by linarith [e.nonneg i, e.nonneg j]
  have hunimodal := unimodal_of_logconcave_palindromic hq_nonneg hpos' hlc' hpal
  have hej_lo : 0 ≤ e j := e.nonneg j
  have hej_hi : e j ≤ q := by simp only [hq_def]; linarith [e.nonneg i]
  have hejm1_lo : 0 ≤ e j - 1 := by omega
  have hejm1_hi : e j - 1 ≤ q := by simp only [hq_def]; omega
  have he_eq_slice : e = sliceComposition e j i hij.symm (e j) hej_lo hej_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [sliceComposition]
    by_cases hkj : k = j
    · simp only [hkj, ite_true]
    · by_cases hki : k = i
      · simp only [hki, ite_true, if_neg hij]; ring
      · simp only [hkj, hki, ite_false]
  have hmod_eq_slice : e.modify j i hj hij.symm =
      sliceComposition e j i hij.symm (e j - 1) hejm1_lo hejm1_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hkj : k = j
    · simp only [hkj, ite_true]
    · by_cases hki : k = i
      · simp only [hki, ite_true, if_neg hij]; ring
      · simp only [hkj, hki, ite_false]
  have h2ej_lt_q : 2 * (e j - 1) < q := by simp only [hq_def]; omega
  have hincr := hunimodal.1 (e j - 1) hejm1_lo h2ej_lt_q
  have hslice_ej : sliceSeq D e j i hij.symm (e j) =
      D (sliceComposition e j i hij.symm (e j) hej_lo hej_hi) := by
    unfold sliceSeq; rw [dif_pos ⟨hej_lo, hej_hi⟩]
  have hslice_ejm1 : sliceSeq D e j i hij.symm (e j - 1) =
      D (sliceComposition e j i hij.symm (e j - 1) hejm1_lo hejm1_hi) := by
    unfold sliceSeq; rw [dif_pos ⟨hejm1_lo, hejm1_hi⟩]
  simp only [Int.sub_add_cancel] at hincr
  rw [hslice_ejm1, hslice_ej, ← hmod_eq_slice, ← he_eq_slice] at hincr
  exact hincr

/-- Any vector can be transformed to a concentrated vector while decreasing D. -/
theorem concentrated_minimizes (hn : 0 < n) (hd : 0 ≤ d) (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D) :
    ∀ e : WeakComposition n d, ∃ e' : WeakComposition n d,
      IsConcentrated d e'.toFun ∧ D e' ≤ D e := by
  intro e
  by_cases hd0 : d = 0
  · use e
    constructor
    · use ⟨0, hn⟩
      intro i
      have hsum : 0 = ∑ j, e j := by rw [← hd0]; exact e.sum_eq.symm
      have hall_zero : ∀ j, e j = 0 := by
        intro j
        have hnonneg := e.nonneg j
        have hle : e j ≤ ∑ k, e k := Finset.single_le_sum (fun k _ => e.nonneg k) (Finset.mem_univ j)
        omega
      rw [hall_zero i, hd0]
      simp only [ite_self]
    · exact le_refl _
  have hd_pos : 0 < d := by omega
  generalize hm : (d - maxEntry e.toFun hn).toNat = m
  induction m using Nat.strong_induction_on generalizing e with
  | _ m ih =>
    by_cases hmax_eq : maxEntry e.toFun hn = d
    · exact ⟨e, WeakComposition.concentrated_of_maxEntry_eq_d e hn hmax_eq, le_refl _⟩
    have hmax_lt : maxEntry e.toFun hn < d := by
      have hle := WeakComposition.maxEntry_le_d e hn
      omega
    obtain ⟨i, hi_max⟩ := exists_eq_maxEntry e.toFun hn
    have hconc : ¬ IsConcentrated d e.toFun := by
      intro hc
      obtain ⟨k, hk⟩ := hc
      have hi_eq_d : e i = d := by
        have hei := hk i
        by_cases hik : i = k
        · rw [hik]
          have hek := hk k
          simp only [ite_true] at hek
          exact hek
        · simp only [hik, ite_false] at hei
          have hek := hk k
          simp only [ite_true] at hek
          have hk_le : e k ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn k
          linarith
      linarith
    obtain ⟨i', j', hij', hi'_pos, hj'_pos⟩ := exists_two_positive hd_pos e hconc
    have hj_exists : ∃ j, j ≠ i ∧ 0 < e j := by
      by_cases hi'i : i' = i
      · exact ⟨j', fun h => hij' (hi'i.trans h.symm), hj'_pos⟩
      · exact ⟨i', hi'i, hi'_pos⟩
    obtain ⟨j, hji, hj_pos⟩ := hj_exists
    have hij : i ≠ j := hji.symm
    have hj_ge1 : 1 ≤ e j := by omega
    have hj_le_i : e j ≤ e i := by
      have hi_le : e i ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn i
      have hj_le : e j ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn j
      linarith
    set e1 := e.modify j i hj_ge1 hji with he1
    have hD_decr : D e1 ≤ D e := concentrating_to_max_decreases_D D hpos hsym hlc e i j hij hj_ge1 hj_le_i
    have hmax_incr : maxEntry e1.toFun hn = maxEntry e.toFun hn + 1 :=
      WeakComposition.maxEntry_modify_to_maximizer e hn i j hij hj_ge1 hi_max
    have hm1 : (d - maxEntry e1.toFun hn).toNat < m := by
      rw [← hm]
      exact WeakComposition.measure_decreases_of_maxEntry_increases e e1 hn hmax_incr hmax_lt
    obtain ⟨e', hconc', hD'⟩ := ih (d - maxEntry e1.toFun hn).toNat hm1 e1 rfl
    exact ⟨e', hconc', le_trans hD' hD_decr⟩

namespace SymmetricLogConcaveFunction

/-- Every symmetric log-concave function on weak compositions is maximized on balanced vectors. -/
theorem maximized_on_balanced (F : SymmetricLogConcaveFunction n d) (e : WeakComposition n d) :
    ∃ e' : WeakComposition n d, IsBalanced e'.toFun ∧ F.D e ≤ F.D e' :=
  balanced_maximizes F.D F.strictlyPositive F.symmetric F.logConcave e

/-- Every symmetric log-concave function on weak compositions is minimized on concentrated vectors. -/
theorem minimized_on_concentrated (hn : 0 < n) (hd : 0 ≤ d)
    (F : SymmetricLogConcaveFunction n d) (e : WeakComposition n d) :
    ∃ e' : WeakComposition n d, IsConcentrated d e'.toFun ∧ F.D e' ≤ F.D e :=
  concentrated_minimizes hn hd F.D F.strictlyPositive F.symmetric F.logConcave e

/-- **Main Theorem (Paper formulation - Maximum).**
    There exists a balanced vector that maximizes D over all of E(n,d). -/
public theorem exists_balanced_maximizer (hn : 0 < n) (hd : 0 ≤ d)
    (F : SymmetricLogConcaveFunction n d) :
    ∃ b : WeakComposition n d, IsBalanced b.toFun ∧ ∀ e, F.D e ≤ F.D b := by
  classical
  haveI : Finite (WeakComposition n d) := WeakComposition.finite hd
  haveI : Nonempty (WeakComposition n d) := WeakComposition.nonempty hn hd
  obtain ⟨eMax, heMax⟩ := Finite.exists_max F.D
  obtain ⟨b, hb_bal, hD_le⟩ := F.maximized_on_balanced eMax
  have hD_ge : F.D b ≤ F.D eMax := heMax b
  have hD_eq : F.D b = F.D eMax := le_antisymm hD_ge hD_le
  use b, hb_bal
  intro e
  calc F.D e ≤ F.D eMax := heMax e
       _ = F.D b := hD_eq.symm

/-- **Main Theorem (Paper formulation - Minimum).**
    There exists a concentrated vector that minimizes D over all of E(n,d). -/
public theorem exists_concentrated_minimizer (hn : 0 < n) (hd : 0 ≤ d)
    (F : SymmetricLogConcaveFunction n d) :
    ∃ c : WeakComposition n d, IsConcentrated d c.toFun ∧ ∀ e, F.D c ≤ F.D e := by
  classical
  haveI : Finite (WeakComposition n d) := WeakComposition.finite hd
  haveI : Nonempty (WeakComposition n d) := WeakComposition.nonempty hn hd
  obtain ⟨eMin, heMin⟩ := Finite.exists_min F.D
  obtain ⟨c, hc_conc, hD_le⟩ := F.minimized_on_concentrated hn hd eMin
  have hD_ge : F.D eMin ≤ F.D c := heMin c
  have hD_eq : F.D c = F.D eMin := le_antisymm hD_le hD_ge
  use c, hc_conc
  intro e
  calc F.D c = F.D eMin := hD_eq
       _ ≤ F.D e := heMin e

end SymmetricLogConcaveFunction
