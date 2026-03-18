/-
Copyright (c) 2026 Mathlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilio Ferrucci
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Functions of finite p-variation

We define the p-variation of a function and prove basic properties.

The theorem `pVariationPowOn.add_le_union` and its dependency `monotone_mem_of_nonempty` were
originally part of `Mathlib.Topology.EMetricSpace.BoundedVariation`. Some later material in this
file also
duplicates, at a conceptual level, duality/reflection arguments from `BoundedVariation`: in
particular, `pVariationPowOn_Icc_reflect` parallels `eVariationOn.comp_ofDual`. It may be worth
refactoring this in the future to reduce duplication, possibly by reorganizing or even merging the
two files.

### Main definitions

* `pVariationPowOn f s p` is the p-th power of the p-variation of the function `f` on the set `s`,
  in `ℝ≥0∞`. It equals the supremum over all finite increasing sequences `u` in `s` of
  `∑ edist (f (u (i+1))) (f (u i)) ^ p`.
* `pVariationOn f s p = (pVariationPowOn f s p) ^ (1 / p)` is the rooted quantity usually called
  the p-variation in the literature.
* `FinitePVariationOn f s p` registers that the p-variation of `f` on `s` is finite.

### Main statements

* `pVariationPowOn.mono`: monotonicity in the set.
* `pVariationPowOn.add_le_union`: p-variation is super-additive on sets to the left and right of
  each other.
* `pVariationPowOn.norm_le`: for `1 ≤ p ≤ q`, the normalized q-variation is controlled by the
  normalized p-variation:
  `(pVariationPowOn f s q) ^ (1 / q) ≤ (pVariationPowOn f s p) ^ (1 / p)`.
* `pVariationPowOn.tendsto_pVariationPowOn_of_tendsto`: for a continuous function of finite
  p-variation, the p-variation on intervals `[sₙ, tₙ]` tends to `0` whenever `sₙ, tₙ → x`
  with `a ≤ sₙ ≤ tₙ ≤ b`.

### Implementation notes

The exponent `p : ℝ` is required to satisfy `1 ≤ p` throughout; the concept is not useful for
`p < 1`. The value `p = 1` recovers `eVariationOn`, both for `pVariationPowOn` and for the rooted
`pVariationOn`.

### Tags

p-variation, bounded variation, Hölder, Young integral
-/

@[expose] public section

open scoped NNReal ENNReal
open Set

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/-- The p-th power of the p-variation of a function `f` on a set `s` inside a linear order is the
supremum of `∑ edist (f (u (i+1))) (f (u i)) ^ p` over all finite increasing sequences `u`
in `s`. -/
noncomputable def pVariationPowOn (f : α → E) (s : Set α) (p : ℝ) : ℝ≥0∞ :=
  ⨆ π : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range π.1, edist (f (π.2.1 (i + 1))) (f (π.2.1 i)) ^ p

/-- The p-variation of a function `f` on a set `s` is the p-th root of `pVariationPowOn f s p`. -/
noncomputable def pVariationOn (f : α → E) (s : Set α) (p : ℝ) : ℝ≥0∞ :=
  pVariationPowOn f s p ^ (1 / p)

/-- A function has finite p-variation on a set `s` if `pVariationPowOn f s p` is finite. -/
def FinitePVariationOn (f : α → E) (s : Set α) (p : ℝ) :=
  pVariationPowOn f s p ≠ ∞

private lemma monotone_mem_of_nonempty {s : Set α} (hs : s.Nonempty) :
    Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun _ => x, fun i j _ => le_rfl, fun _ => hx⟩⟩

namespace pVariationPowOn

/-- The p-th power of the p-variation is monotone in the set: a larger set has at least as much
`p`-variation. -/
theorem mono (f : α → E) {s t : Set α} {p : ℝ}
    (hst : t ⊆ s) : pVariationPowOn f t p ≤ pVariationPowOn f s p := by
  apply iSup_le
  rintro ⟨n, u, hu, ut⟩
  exact le_iSup_of_le ⟨n, u, hu, fun i => hst (ut i)⟩ le_rfl

/-- The p-th power of the p-variation on the empty set is zero. -/
@[simp]
protected lemma empty (f : α → E) (p : ℝ) : pVariationPowOn f ∅ p = 0 := by
  simp [pVariationPowOn]

/-- The p-th power of the p-variation on the union of two sets `s` and `t`, with `s` to the left
of `t`, is at least the sum of the p-th powers along `s` and `t`. -/
theorem add_le_union (f : α → E) {s t : Set α} {p : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
    pVariationPowOn f s p + pVariationPowOn f t p ≤ pVariationPowOn f (s ∪ t) p := by
  by_cases hs : s = ∅
  · simp [hs]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } :=
    monotone_mem_of_nonempty (nonempty_iff_ne_empty.2 hs)
  by_cases ht : t = ∅
  · simp [ht]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ t } :=
    monotone_mem_of_nonempty (nonempty_iff_ne_empty.2 ht)
  refine ENNReal.iSup_add_iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩ ⟨m, ⟨v, hv, vt⟩⟩
  let w i := if i ≤ n then u i else v (i - (n + 1))
  calc
    ((∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ p) +
        ∑ i ∈ Finset.range m, edist (f (v (i + 1))) (f (v i)) ^ p) =
      (∑ i ∈ Finset.range n, edist (f (w (i + 1))) (f (w i)) ^ p) +
        ∑ i ∈ Finset.range m,
          edist (f (w (n + 1 + i + 1))) (f (w (n + 1 + i))) ^ p := by
      dsimp only [w]
      congr 1
      · grind [Finset.sum_congr]
      · grind
    _ = (∑ i ∈ Finset.range n, edist (f (w (i + 1))) (f (w i)) ^ p) +
        ∑ i ∈ Finset.Ico (n + 1) (n + 1 + m),
          edist (f (w (i + 1))) (f (w i)) ^ p := by
      congr 1
      rw [Finset.range_eq_Ico]
      convert Finset.sum_Ico_add
        (fun i : ℕ => edist (f (w (i + 1))) (f (w i)) ^ p) 0 m (n + 1)
        using 3 <;> abel
    _ ≤ ∑ i ∈ Finset.range (n + 1 + m),
          edist (f (w (i + 1))) (f (w i)) ^ p := by
      rw [← Finset.sum_union]
      · gcongr; grind
      · exact Finset.disjoint_left.2 (by grind)
    _ ≤ pVariationPowOn f (s ∪ t) p :=
      le_iSup_of_le ⟨n + 1 + m, w, by grind [Monotone], by grind⟩ le_rfl

/-- For `1 ≤ p ≤ q`, the normalized `q`-variation is controlled by the normalized
`p`-variation:
`(pVariationPowOn f s q) ^ (1 / q) ≤ (pVariationPowOn f s p) ^ (1 / p)`. -/
theorem norm_le (f : α → E) (s : Set α) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    (pVariationPowOn f s q) ^ (1 / q) ≤ (pVariationPowOn f s p) ^ (1 / p) := by
  have h :
      pVariationPowOn f s q ≤ (pVariationPowOn f s p) ^ (q / p) := by
    apply iSup_le
    rintro ⟨n, u, hu, us⟩
    have hsum :
        ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) ^ p) ^ (q / p) ≤
          (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ p) ^ (q / p) := by
      let a : ℕ → ℝ≥0∞ := fun i => edist (f (u (i + 1))) (f (u i)) ^ p
      have hqp : 1 ≤ q / p := by
        rwa [le_div_iff₀ (by linarith : (0 : ℝ) < p), one_mul]
      change ∑ i ∈ Finset.range n, (a i) ^ (q / p) ≤ (∑ i ∈ Finset.range n, a i) ^ (q / p)
      induction n with
      | zero =>
          simp
      | succ n ihn =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          calc
            (∑ x ∈ Finset.range n, a x ^ (q / p)) + a n ^ (q / p) ≤
                (∑ x ∈ Finset.range n, a x) ^ (q / p) + a n ^ (q / p) := by
                  gcongr
            _ ≤ ((∑ x ∈ Finset.range n, a x) + a n) ^ (q / p) := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    ENNReal.add_rpow_le_rpow_add (∑ x ∈ Finset.range n, a x) (a n) hqp
            _ = (∑ x ∈ Finset.range n, a x + a n) ^ (q / p) := by
                  rfl
    calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ q
        = ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) ^ p) ^ (q / p) := by
          congr 1; ext i
          rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ (by linarith : p ≠ 0)]
      _ ≤ (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ p) ^ (q / p) :=
          hsum
      _ ≤ (pVariationPowOn f s p) ^ (q / p) :=
          ENNReal.rpow_le_rpow (le_iSup_of_le ⟨n, ⟨u, hu, us⟩⟩ le_rfl)
            (div_nonneg (by linarith) (by linarith))
  calc
    (pVariationPowOn f s q) ^ (1 / q) ≤ ((pVariationPowOn f s p) ^ (q / p)) ^ (1 / q) := by
      exact ENNReal.rpow_le_rpow h (one_div_nonneg.2 (by linarith))
    _ = (pVariationPowOn f s p) ^ ((q / p) * (1 / q)) := by
      rw [← ENNReal.rpow_mul]
    _ = (pVariationPowOn f s p) ^ (1 / p) := by
      congr 1
      field_simp [show q ≠ 0 by linarith]

/-- Comparison estimate for the p-variation power on a closed interval split into two closed
subintervals. -/
lemma Icc_split_le (f : α → E) {p : ℝ} (hp : 1 ≤ p) {s₀ s t₀ : α}
    (hs₀s : s₀ ≤ s) (hst₀ : s ≤ t₀) :
    pVariationPowOn f (Icc s₀ t₀) p ≤
      2 ^ (p - 1) * (pVariationPowOn f (Icc s₀ s) p + pVariationPowOn f (Icc s t₀) p) := by
  set C : ℝ≥0∞ := 2 ^ (p - 1)
  have hC : 1 ≤ C := by
    simpa [C] using ENNReal.rpow_le_rpow (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
      (sub_nonneg.mpr hp)
  have hscale (x : ℝ≥0∞) : x ≤ C * x := by
    calc
      x = (1 : ℝ≥0∞) * x := by simp
      _ ≤ C * x := by gcongr
  apply iSup_le
  rintro ⟨n, u, hu, us⟩
  let a : ℕ → ℝ≥0∞ := fun i => edist (f (u (i + 1))) (f (u i)) ^ p
  by_cases hns : u n ≤ s
  · let v : ℕ → α := fun i => if i ≤ n then u i else u n
    have hv : Monotone v := by
      intro i j hij
      by_cases hj : j ≤ n
      · have hi : i ≤ n := hij.trans hj
        simp [v, hi, hj, hu hij]
      · by_cases hi : i ≤ n
        · simpa [v, hi, hj] using hu hi
        · simp [v, hi, hj]
    have hvmem : ∀ i, v i ∈ Icc s₀ s := by
      intro i
      by_cases hi : i ≤ n
      · simpa [v, hi] using (show u i ∈ Icc s₀ s from ⟨(us i).1, (hu hi).trans hns⟩)
      · simpa [v, hi] using (show u n ∈ Icc s₀ s from ⟨(us n).1, hns⟩)
    calc
      ∑ i ∈ Finset.range n, a i =
          ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) ^ p := by
            refine Finset.sum_congr rfl fun i hi => ?_
            simp [a, v, (Finset.mem_range.mp hi).le, Nat.succ_le_of_lt (Finset.mem_range.mp hi)]
      _ ≤ pVariationPowOn f (Icc s₀ s) p := le_iSup_of_le ⟨n, v, hv, hvmem⟩ le_rfl
      _ ≤ pVariationPowOn f (Icc s₀ s) p + pVariationPowOn f (Icc s t₀) p :=
        le_add_of_nonneg_right (zero_le _)
      _ ≤ C * (pVariationPowOn f (Icc s₀ s) p + pVariationPowOn f (Icc s t₀) p) := hscale _
  by_cases hs0 : s ≤ u 0
  · calc
      ∑ i ∈ Finset.range n, a i ≤ pVariationPowOn f (Icc s t₀) p :=
        le_iSup_of_le ⟨n, u, hu, fun i => ⟨hs0.trans (hu (Nat.zero_le i)), (us i).2⟩⟩ le_rfl
      _ ≤ pVariationPowOn f (Icc s₀ s) p + pVariationPowOn f (Icc s t₀) p :=
        le_add_of_nonneg_left (zero_le _)
      _ ≤ C * (pVariationPowOn f (Icc s₀ s) p + pVariationPowOn f (Icc s t₀) p) := hscale _
  have hs0' : u 0 < s := lt_of_not_ge hs0
  have hns' : s < u n := lt_of_not_ge hns
  have hn : 0 < n := by
    cases n with
    | zero => exact (hs0'.not_ge hns'.le).elim
    | succ n => exact Nat.succ_pos _
  have hex : ∃ k, k ≤ n ∧ s ≤ u k := ⟨n, le_rfl, hns'.le⟩
  let K : ℕ := Nat.find hex
  have hK : K ≤ n ∧ s ≤ u K := Nat.find_spec hex
  have hK0 : 0 < K := by
    by_contra hK0
    exact hs0 (by simpa [K, Nat.eq_zero_of_not_pos hK0] using hK.2)
  let N : ℕ := K - 1
  have hNK : N + 1 = K := by omega
  have hN : N < n := by omega
  have hsN : s ≤ u (N + 1) := by simpa [hNK] using hK.2
  have hNu : u N ≤ s := by
    have h := Nat.find_min hex (m := N) (by omega)
    exact le_of_lt <| lt_of_not_ge fun hs => h ⟨by omega, hs⟩
  let v : ℕ → α := fun i => if i ≤ N then u i else s
  let w : ℕ → α := fun i => if i = 0 then s else u (N + i)
  have hv : Monotone v := by
    intro i j hij
    by_cases hj : j ≤ N
    · have hi : i ≤ N := hij.trans hj
      simp [v, hi, hj, hu hij]
    · by_cases hi : i ≤ N
      · simp [v, hi, hj, (hu hi).trans hNu]
      · simp [v, hi, hj]
  have hvmem : ∀ i, v i ∈ Icc s₀ s := by
    intro i
    by_cases hi : i ≤ N
    · simpa [v, hi] using (show u i ∈ Icc s₀ s from ⟨(us i).1, (hu hi).trans hNu⟩)
    · simpa [v, hi] using (show s ∈ Icc s₀ s from ⟨hs₀s, le_rfl⟩)
  have hw : Monotone w := by
    apply monotone_nat_of_le_succ
    intro i
    cases i with
    | zero => simp [w, hsN]
    | succ i =>
        simpa [w, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hu (by omega)
  have hwmem : ∀ i, w i ∈ Icc s t₀ := by
    intro i
    cases i with
    | zero => simpa [w] using (show s ∈ Icc s t₀ from ⟨le_rfl, hst₀⟩)
    | succ i =>
        refine ⟨hsN.trans (hu (by omega)), (us (N + i.succ)).2⟩
  set Sv := ∑ i ∈ Finset.range (N + 1), edist (f (v (i + 1))) (f (v i)) ^ p with hSv_def
  set Sw := ∑ i ∈ Finset.range (n - N), edist (f (w (i + 1))) (f (w i)) ^ p with hSw_def
  have hSv : Sv ≤ pVariationPowOn f (Icc s₀ s) p := by
    rw [hSv_def]
    exact le_iSup_of_le ⟨N + 1, v, hv, hvmem⟩ le_rfl
  have hSw : Sw ≤ pVariationPowOn f (Icc s t₀) p := by
    rw [hSw_def]
    exact le_iSup_of_le ⟨n - N, w, hw, hwmem⟩ le_rfl
  have hcross : a N ≤ C * (edist (f s) (f (u N)) ^ p + edist (f (u (N + 1))) (f s) ^ p) := by
    calc
      a N ≤ (edist (f (u (N + 1))) (f s) + edist (f s) (f (u N))) ^ p :=
        ENNReal.rpow_le_rpow (edist_triangle _ _ _) (by linarith)
      _ ≤ C * (edist (f (u (N + 1))) (f s) ^ p + edist (f s) (f (u N)) ^ p) := by
        simpa [C] using ENNReal.rpow_add_le_mul_rpow_add_rpow
          (edist (f (u (N + 1))) (f s)) (edist (f s) (f (u N))) hp
      _ = C * (edist (f s) (f (u N)) ^ p + edist (f (u (N + 1))) (f s) ^ p) := by
        rw [add_comm]
  have hsum : ∑ i ∈ Finset.range n, a i =
      ∑ i ∈ Finset.range N, a i + a N + ∑ i ∈ Finset.Ico (N + 1) n, a i := by
    rw [← Finset.sum_range_add_sum_Ico a hN.le, Finset.sum_eq_sum_Ico_succ_bot hN]
    abel
  have hSv' : Sv = ∑ i ∈ Finset.range N, a i + edist (f s) (f (u N)) ^ p := by
    rw [hSv_def, Finset.sum_range_succ]
    congr 1
    · exact Finset.sum_congr rfl fun i hi => by simp [v, a, (Finset.mem_range.mp hi).le,
        Nat.succ_le_of_lt (Finset.mem_range.mp hi)]
    · simp [v]
  have hSw' : Sw = edist (f (u (N + 1))) (f s) ^ p + ∑ i ∈ Finset.Ico (N + 1) n, a i := by
    rw [hSw_def, show n - N = n - (N + 1) + 1 by omega, Finset.sum_range_succ']
    rw [add_comm]
    congr 1
    · rw [Finset.sum_Ico_eq_sum_range a (N + 1) n]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h : i + (2 + N) = i + (1 + (1 + N)) := by omega
      simp [w, a, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, h]
  calc
    ∑ i ∈ Finset.range n, a i
        ≤ C * (∑ i ∈ Finset.range N, a i) +
            C * (edist (f s) (f (u N)) ^ p + edist (f (u (N + 1))) (f s) ^ p) +
            C * (∑ i ∈ Finset.Ico (N + 1) n, a i) := by
      rw [hsum]
      refine add_le_add (add_le_add ?_ hcross) ?_
      · exact hscale _
      · exact hscale _
    _ = C * (Sv + Sw) := by rw [hSv', hSw', ← mul_add, ← mul_add]; abel_nf
    _ ≤ C * (pVariationPowOn f (Icc s₀ s) p + pVariationPowOn f (Icc s t₀) p) := by gcongr

open Filter Topology in
private lemma pVariationPowOn_Icc_reflect
    (f : ℝ → E) {u v : ℝ} (huv : u ≤ v) {p : ℝ} :
    pVariationPowOn (fun z => f (-z)) (Icc (-v) (-u)) p = pVariationPowOn f (Icc u v) p := by
  have haux :
      ∀ (g : ℝ → E) {a b : ℝ}, a ≤ b →
        pVariationPowOn (fun z => g (-z)) (Icc (-b) (-a)) p ≤ pVariationPowOn g (Icc a b) p := by
    intro g a b hab
    apply iSup_le
    rintro ⟨n, z, hzmono, hzmem⟩
    let w : ℕ → ℝ := fun i => if h : i ≤ n then -(z (n - i)) else -(z 0)
    have hwmono : Monotone w := by
      intro i j hij
      by_cases hj : j ≤ n
      · have hi : i ≤ n := hij.trans hj
        simp [w, hi, hj]
        have hsub : n - j ≤ n - i := by omega
        simpa using hzmono hsub
      · by_cases hi : i ≤ n
        · simp [w, hi, hj]
          simpa using hzmono (Nat.zero_le (n - i))
        · simp [w, hi, hj]
    have hwmem : ∀ i, w i ∈ Icc a b := by
      intro i
      by_cases hi : i ≤ n
      · have hzi : z (n - i) ∈ Icc (-b) (-a) := hzmem (n - i)
        simp [w, hi, mem_Icc] at hzi ⊢
        constructor <;> linarith
      · have hz0 : z 0 ∈ Icc (-b) (-a) := hzmem 0
        simp [w, hi, mem_Icc] at hz0 ⊢
        constructor <;> linarith
    have hsum :
        ∑ i ∈ Finset.range n, edist (g (-(z (i + 1)))) (g (-(z i))) ^ p =
          ∑ i ∈ Finset.range n, edist (g (w (i + 1))) (g (w i)) ^ p := by
      let A : ℕ → ℝ≥0∞ := fun i => edist (g (-(z (i + 1)))) (g (-(z i))) ^ p
      calc
        ∑ i ∈ Finset.range n, edist (g (-(z (i + 1)))) (g (-(z i))) ^ p
            = ∑ i ∈ Finset.range n, A i := by
              rfl
        _ = ∑ i ∈ Finset.range n, A (n - 1 - i) := by
              symm
              exact Finset.sum_range_reflect A n
        _ = ∑ i ∈ Finset.range n, edist (g (w (i + 1))) (g (w i)) ^ p := by
              apply Finset.sum_congr rfl
              intro i hi
              have hi_lt : i < n := Finset.mem_range.mp hi
              have hi_le : i ≤ n := hi_lt.le
              have hi1_le : i + 1 ≤ n := by omega
              have hsub1 : n - (i + 1) = n - 1 - i := by omega
              have hsub2 : n - i = (n - 1 - i) + 1 := by omega
              simp [A, w, hi_le, hi1_le, hsub1, hsub2, edist_comm]
    calc
      ∑ i ∈ Finset.range n, edist (g (-(z (i + 1)))) (g (-(z i))) ^ p
          = ∑ i ∈ Finset.range n, edist (g (w (i + 1))) (g (w i)) ^ p := hsum
      _ ≤ pVariationPowOn g (Icc a b) p :=
        le_iSup_of_le ⟨n, w, hwmono, hwmem⟩ le_rfl
  refine le_antisymm (haux f huv) ?_
  simpa [neg_neg] using haux (fun z => f (-z)) (a := -v) (b := -u) (by linarith)

open Filter Topology in
private lemma tendsto_pVariationPowOn_Icc_right_zero_of_tendsto
    {f : ℝ → E} {p : ℝ} (hp : 1 ≤ p)
    {x b : ℝ} (hxb : x ≤ b) (hf : ContinuousOn f (Icc x b))
    (hpv : FinitePVariationOn f (Icc x b) p)
    {y : ℕ → ℝ} (hy : ∀ n, y n ∈ Icc x b) (hyx : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun n => pVariationPowOn f (Icc x (y n)) p) atTop (𝓝 0) := by
  set V := pVariationPowOn f (Icc x b) p
  have hV : V ≠ ⊤ := hpv
  have hle : ∀ n, pVariationPowOn f (Icc x (y n)) p ≤ V :=
    fun n => mono f (Icc_subset_Icc_right (hy n).2)
  rw [ENNReal.tendsto_atTop_zero]
  by_contra h_not
  push_neg at h_not
  obtain ⟨ε, hε_pos, h_freq⟩ := h_not
  have hε_fin : ε ≠ ⊤ := by
    obtain ⟨n, -, hn⟩ := h_freq 0
    exact ne_top_of_le_ne_top hV (hn.le.trans (hle n))
  have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := ENNReal.div_pos hε_pos.ne' (by norm_num)
  -- Continuity bound: edist(f z, f x)^p < ε/4 for z in [x, b] near x
  have hf_cont : ContinuousWithinAt f (Icc x b) x :=
    hf x (left_mem_Icc.mpr hxb)
  -- Extract N₀: for n ≥ N₀, ∀ z ∈ [x, yₙ], edist(f z, f x)^p < ε/4
  have h_cont_bound : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∀ z ∈ Icc x (y n), edist (f z) (f x) ^ p < ε / 4 := by
    have hp0 : (0 : ℝ) < p := by linarith
    have hε4_fin : ε / 4 ≠ ⊤ := ENNReal.div_ne_top hε_fin (by norm_num)
    set ε' := (ε / 4) ^ ((1 : ℝ) / p)
    have hε'_pos : (0 : ℝ≥0∞) < ε' := ENNReal.rpow_pos hε4_pos hε4_fin
    -- From continuity of f at x within [x, b]:
    -- ∀ᶠ z in 𝓝[Icc x b] x, edist (f z) (f x) < ε'
    have h_evt : ∀ᶠ z in 𝓝[Icc x b] x, edist (f z) (f x) < ε' :=
      EMetric.tendsto_nhds.mp hf_cont ε' hε'_pos
    rw [eventually_nhdsWithin_iff] at h_evt
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp h_evt
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hyx δ hδ_pos
    refine ⟨N₀, fun n hn z hz => ?_⟩
    have hzδ : dist z x < δ := calc
      dist z x ≤ dist (y n) x := by
        rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hz.1),
          abs_of_nonneg (sub_nonneg.mpr (hy n).1)]
        linarith [hz.2]
      _ < δ := hN₀ n hn
    have hzs : z ∈ Icc x b := Icc_subset_Icc_right (hy n).2 hz
    have hedist_lt : edist (f z) (f x) < ε' := hδ hzδ hzs
    calc edist (f z) (f x) ^ p < ε' ^ p := ENNReal.rpow_lt_rpow hedist_lt hp0
      _ = (ε / 4) ^ ((1 / p) * p) := by rw [← ENNReal.rpow_mul]
      _ = ε / 4 := by rw [one_div, inv_mul_cancel₀ hp0.ne']; simp
  obtain ⟨N₀, h_cont_bound⟩ := h_cont_bound
  -- Peeling: if pVar[x, yₙ] > ε and the continuity bound holds,
  -- then ∃ w > x with pVar[w, yₙ] ≥ ε/4
  have peeling : ∀ n, N₀ ≤ n → ε < pVariationPowOn f (Icc x (y n)) p →
      ∃ w, x < w ∧ w ≤ y n ∧ ε / 4 ≤ pVariationPowOn f (Icc w (y n)) p := by
    intro n hn hpn
    by_contra h_no_w
    push_neg at h_no_w
    obtain ⟨⟨m, u, hu, us⟩, hsum⟩ := lt_iSup_iff.mp hpn
    set S := ∑ i ∈ Finset.range m,
      edist (f (u (i + 1))) (f (u i)) ^ p with hS_def
    have hp0 : (0 : ℝ) < p := by linarith
    -- ∃ j ≤ m with u j > x (else sum = 0)
    have h_exists : ∃ j, j ≤ m ∧ x < u j := by
      by_contra h_all
      push_neg at h_all
      have : S = 0 := Finset.sum_eq_zero fun i hi => by
        rw [le_antisymm (h_all i (Finset.mem_range.mp hi).le) (us i).1,
          le_antisymm (h_all (i + 1) (Nat.succ_le_of_lt
            (Finset.mem_range.mp hi))) (us (i + 1)).1]
        simp [edist_self, ENNReal.zero_rpow_of_pos hp0]
      exact absurd (this ▸ hsum) (not_lt.mpr (zero_le ε))
    set j₀ := Nat.find h_exists
    have hj₀m : j₀ ≤ m := (Nat.find_spec h_exists).1
    have hj₀x : x < u j₀ := (Nat.find_spec h_exists).2
    have hj₀_eq : ∀ k, k < j₀ → u k = x := fun k hk => by
      have := Nat.find_min h_exists hk
      push_neg at this
      exact le_antisymm (this (hk.le.trans hj₀m)) (us k).1
    -- Bound ∑ range j₀ ≤ edist(f(u j₀), f(x))^p
    have hfirst_le : ∑ i ∈ Finset.range j₀,
        edist (f (u (i + 1))) (f (u i)) ^ p ≤
        edist (f (u j₀)) (f x) ^ p := by
      rcases Nat.eq_zero_or_pos j₀ with hj₀0 | hj₀pos
      · simp [hj₀0]
      · have hpred_lt : j₀ - 1 < j₀ := Nat.pred_lt hj₀pos.ne'
        have hj₀split : j₀ = (j₀ - 1) + 1 := by omega
        have hpred_add : j₀ - 1 + 1 = j₀ := by omega
        rw [hj₀split, Finset.sum_range_succ]
        rw [Finset.sum_eq_zero (fun i hi => by
          have him := Finset.mem_range.mp hi
          rw [hj₀_eq i (him.trans hpred_lt),
            hj₀_eq (i + 1) ((Nat.succ_le_of_lt him).trans_lt hpred_lt)]
          simp [edist_self, ENNReal.zero_rpow_of_pos hp0]),
          zero_add, hpred_add, hj₀_eq _ hpred_lt]
    -- Bound ∑ Ico j₀ m ≤ pVar[u j₀, y n]
    have hrest_le : ∑ i ∈ Finset.Ico j₀ m,
        edist (f (u (i + 1))) (f (u i)) ^ p ≤
        pVariationPowOn f (Icc (u j₀) (y n)) p := by
      set v : ℕ → ℝ := fun k => u (k + j₀)
      have hv_sum : ∑ i ∈ Finset.Ico j₀ m,
          edist (f (u (i + 1))) (f (u i)) ^ p =
          ∑ k ∈ Finset.range (m - j₀),
            edist (f (v (k + 1))) (f (v k)) ^ p := by
        rw [Finset.sum_Ico_eq_sum_range]
        exact Finset.sum_congr rfl fun k _ => by
          change edist (f (u (j₀ + k + 1))) (f (u (j₀ + k))) ^ p =
            edist (f (u (k + 1 + j₀))) (f (u (k + j₀))) ^ p
          have h1 : j₀ + k + 1 = k + 1 + j₀ := by omega
          have h2 : j₀ + k = k + j₀ := by omega
          rw [h1, h2]
      rw [hv_sum]
      exact le_iSup_of_le ⟨m - j₀, v,
        fun a b hab => hu (Nat.add_le_add_right hab j₀),
        fun k => ⟨hu (Nat.le_add_left j₀ k), (us (k + j₀)).2⟩⟩ le_rfl
    -- pVar[u j₀, y n] < ε/4
    have hpvar_lt : pVariationPowOn f (Icc (u j₀) (y n)) p < ε / 4 :=
      h_no_w (u j₀) hj₀x (us j₀).2
    -- S ≤ ε/4 + ε/4 ≤ ε, contradicting hsum : ε < S
    have hS_le : S ≤ ε := calc
      S = (∑ i ∈ Finset.range j₀,
            edist (f (u (i + 1))) (f (u i)) ^ p) +
          ∑ i ∈ Finset.Ico j₀ m,
            edist (f (u (i + 1))) (f (u i)) ^ p :=
        (Finset.sum_range_add_sum_Ico _ hj₀m).symm
      _ ≤ edist (f (u j₀)) (f x) ^ p +
          pVariationPowOn f (Icc (u j₀) (y n)) p :=
        add_le_add hfirst_le hrest_le
      _ ≤ ε / 4 + ε / 4 :=
        add_le_add (h_cont_bound n hn (u j₀)
          ⟨hj₀x.le, (us j₀).2⟩).le hpvar_lt.le
      _ ≤ ε / 2 + ε / 2 :=
        add_le_add (ENNReal.div_le_div_left (by norm_num : (2 : ℝ≥0∞) ≤ 4) ε)
          (ENNReal.div_le_div_left (by norm_num : (2 : ℝ≥0∞) ≤ 4) ε)
      _ = ε := ENNReal.add_halves ε
    exact absurd hsum (not_lt.mpr hS_le)
  -- Inductive construction: for all N, ∃ w r with (N+1)*(ε/4) ≤ pVar[w, r] ≤ V
  have key : ∀ N : ℕ, ∃ w r, x < w ∧ w ≤ r ∧ r ≤ b ∧
      ↑(N + 1) * (ε / 4) ≤ pVariationPowOn f (Icc w r) p := by
    intro N
    induction N with
    | zero =>
      obtain ⟨n, hn, hpn⟩ := h_freq N₀
      obtain ⟨w, hwx, hwyn, hpw⟩ := peeling n hn hpn
      exact ⟨w, y n, hwx, hwyn, (hy n).2, by simpa⟩
    | succ N ih =>
      obtain ⟨w₁, r₁, hw₁x, hw₁r₁, hr₁b, hpv₁⟩ := ih
      have hyw₁ : ∀ᶠ n in atTop, y n < w₁ :=
        (tendsto_order.mp hyx).2 w₁ hw₁x
      obtain ⟨M, hM⟩ := hyw₁.exists_forall_of_atTop
      obtain ⟨n, hn, hpn⟩ := h_freq (max N₀ M)
      have hnN₀ : N₀ ≤ n := le_of_max_le_left hn
      have hynw₁ : y n < w₁ := hM n (le_of_max_le_right hn)
      obtain ⟨w', hw'x, hw'yn, hpw'⟩ := peeling n hnN₀ hpn
      refine ⟨w', r₁, hw'x, hw'yn.trans (hynw₁.le.trans hw₁r₁),
        hr₁b, ?_⟩
      calc ↑(N + 1 + 1) * (ε / 4)
            = ε / 4 + ↑(N + 1) * (ε / 4) := by push_cast; ring
          _ ≤ pVariationPowOn f (Icc w' (y n)) p +
              pVariationPowOn f (Icc w₁ r₁) p := add_le_add hpw' hpv₁
          _ ≤ pVariationPowOn f (Icc w' (y n) ∪ Icc w₁ r₁) p :=
              add_le_union f (fun a ha c hc => ha.2.trans (hynw₁.le.trans hc.1))
          _ ≤ pVariationPowOn f (Icc w' r₁) p :=
              mono f (union_subset
                (Icc_subset_Icc le_rfl (hynw₁.le.trans hw₁r₁))
                (Icc_subset_Icc (hw'yn.trans hynw₁.le) le_rfl))
  -- Contradiction: ε/4 > 0 and V < ⊤, so ∃ M with V < M * (ε/4)
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_mul_gt hε4_pos.ne' hV
  rcases M with _ | M'
  · simp at hM
  · obtain ⟨w, r, hwx, _, hrb, hwr⟩ := key M'
    exact absurd (hwr.trans (mono f (Icc_subset_Icc hwx.le hrb))) (not_le.mpr hM)


open Filter Topology in
/-- If `f : ℝ → E` is continuous and has finite `p`-variation on `[a, b]`, then the
`pVariationPowOn` on `[sₙ, tₙ]` tends to `0` for any sequences `sₙ, tₙ → x` with
`a ≤ sₙ ≤ tₙ ≤ b`. -/
theorem tendsto_pVariationPowOn_of_tendsto
    {f : ℝ → E} {p : ℝ} (hp : 1 ≤ p)
    {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hpv : FinitePVariationOn f (Icc a b) p)
    {x : ℝ} (hx : x ∈ Icc a b)
    {s t : ℕ → ℝ} (hst : ∀ n, s n ∈ Icc a (t n))
    (htb : ∀ n, t n ∈ Icc (s n) b)
    (hs : Tendsto s atTop (𝓝 x)) (ht : Tendsto t atTop (𝓝 x)) :
    Tendsto (fun n => pVariationPowOn f (Icc (s n) (t n)) p) atTop (𝓝 0) := by
  have h_right :
      Tendsto (fun n => pVariationPowOn f (Icc x (t n ⊔ x)) p) atTop (𝓝 0) := by
    apply tendsto_pVariationPowOn_Icc_right_zero_of_tendsto hp hx.2
    · exact hf.mono (Icc_subset_Icc_left hx.1)
    · exact ne_top_of_le_ne_top hpv (mono f (Icc_subset_Icc_left hx.1))
    · intro n
      exact ⟨le_sup_right, sup_le (htb n).2 hx.2⟩
    · simpa using ht.sup_nhds (tendsto_const_nhds (x := x))
  have h_left_reflected :
      Tendsto (fun n => pVariationPowOn (fun z => f (-z)) (Icc (-x) (-((s n) ⊓ x))) p) atTop
        (𝓝 0) := by
    have hnegax : -x ≤ -a := by
      linarith [hx.1]
    apply tendsto_pVariationPowOn_Icc_right_zero_of_tendsto (f := fun z => f (-z)) hp
      hnegax
    · exact hf.comp continuous_neg.continuousOn (by
        intro z hz
        simp only [mem_Icc] at hz ⊢
        constructor
        · linarith
        · linarith [hx.2])
    · have hpv' : FinitePVariationOn f (Icc a x) p :=
        ne_top_of_le_ne_top hpv (mono f (Icc_subset_Icc_right hx.2))
      simpa [FinitePVariationOn, pVariationPowOn_Icc_reflect f hx.1] using hpv'
    · intro n
      have hsx : s n ⊓ x ∈ Icc a x := by
        exact ⟨le_inf (hst n).1 hx.1, inf_le_right⟩
      simp only [mem_Icc] at hsx ⊢
      constructor
      · linarith
      · linarith
    · simpa using (hs.inf_nhds (tendsto_const_nhds (x := x))).neg
  have h_left :
      Tendsto (fun n => pVariationPowOn f (Icc (s n ⊓ x) x) p) atTop (𝓝 0) := by
    simpa [pVariationPowOn_Icc_reflect f inf_le_right] using h_left_reflected
  have bound :
      (fun n => pVariationPowOn f (Icc (s n) (t n)) p) ≤
        fun n => (2 : ℝ≥0∞) ^ (p - 1) *
          (pVariationPowOn f (Icc (s n ⊓ x) x) p +
            pVariationPowOn f (Icc x (t n ⊔ x)) p) := by
    intro n
    calc
      pVariationPowOn f (Icc (s n) (t n)) p ≤ pVariationPowOn f (Icc (s n ⊓ x) (t n ⊔ x)) p :=
        mono f (Icc_subset_Icc inf_le_left le_sup_left)
      _ ≤ (2 : ℝ≥0∞) ^ (p - 1) *
            (pVariationPowOn f (Icc (s n ⊓ x) x) p +
              pVariationPowOn f (Icc x (t n ⊔ x)) p) :=
        Icc_split_le f hp inf_le_right le_sup_right
  have h_upper :
      Tendsto (fun n => (2 : ℝ≥0∞) ^ (p - 1) *
        (pVariationPowOn f (Icc (s n ⊓ x) x) p +
          pVariationPowOn f (Icc x (t n ⊔ x)) p)) atTop (𝓝 0) := by
    have htop : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
    simpa [mul_zero] using ENNReal.Tendsto.const_mul (h_left.add h_right) (Or.inr htop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper
    (fun n => zero_le _) bound


end pVariationPowOn
