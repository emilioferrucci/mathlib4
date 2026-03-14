/-
Copyright (c) 2026 Mathlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilio Ferrucci
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Functions of finite p-variation

We define the p-variation of a function and prove basic properties,
as well as a basic helper on monotone sequences in nonempty sets, used also in the study of total
variation.

The theorem `pVariationOn.add_le_union` and its dependency `nonempty_monotone_mem` were originally
part of `Mathlib.Topology.EMetricSpace.BoundedVariation`.

## Main definitions

* `pVariationOn f s p` is the p-variation of the function `f` on the set `s`, in `ℝ≥0∞`.
  It equals the supremum over all finite increasing sequences `u` in `s` of
  `∑ edist (f (u (i+1))) (f (u i)) ^ p`.
* `FinitePVariationOn f s p` registers that the p-variation of `f` on `s` is finite.

## Main statements

* `nonempty_monotone_mem`: a nonempty set admits a monotone sequence valued in it.
* `pVariationOn.mono`: monotonicity in the set.
* `pVariationOn.add_le_union`: p-variation is super-additive on sets to the left and right of
  each other.
* `pVariationOn.norm_le`: for `1 ≤ p ≤ q`, the normalized q-variation is controlled by the
  normalized p-variation:
  `(pVariationOn f s q) ^ (1 / q) ≤ (pVariationOn f s p) ^ (1 / p)`.

## Implementation notes

The exponent `p : ℝ` is required to satisfy `1 ≤ p` throughout; the concept is not useful for
`p < 1`. The value `p = 1` recovers `eVariationOn`.

## Tags

p-variation, bounded variation, Hölder, Young integral
-/

@[expose] public section

open scoped NNReal ENNReal
open Set

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/-- The p-variation of a function `f` on a set `s` inside a linear order is the supremum of
`∑ edist (f (u (i+1))) (f (u i)) ^ p` over all finite increasing sequences `u` in `s`. -/
noncomputable def pVariationOn (f : α → E) (s : Set α) (p : ℝ) : ℝ≥0∞ :=
  ⨆ π : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range π.1, edist (f (π.2.1 (i + 1))) (f (π.2.1 i)) ^ p

/-- A function has finite p-variation on a set `s` if its p-variation there is finite. -/
def FinitePVariationOn (f : α → E) (s : Set α) (p : ℝ) :=
  pVariationOn f s p ≠ ∞

theorem nonempty_monotone_mem {s : Set α} (hs : s.Nonempty) :
    Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun _ => x, fun i j _ => le_rfl, fun _ => hx⟩⟩

namespace pVariationOn

/-- The p-variation is monotone in the set: a larger set has at least as much p-variation. -/
theorem mono (f : α → E) {s t : Set α} {p : ℝ}
    (hst : t ⊆ s) : pVariationOn f t p ≤ pVariationOn f s p := by
  apply iSup_le
  rintro ⟨n, u, hu, ut⟩
  exact le_iSup_of_le ⟨n, u, hu, fun i => hst (ut i)⟩ le_rfl

/-- The p-variation on the empty set is zero. -/
@[simp]
protected theorem empty (f : α → E) (p : ℝ) : pVariationOn f ∅ p = 0 := by
  simp [pVariationOn]

/-- The p-variation on the union of two sets `s` and `t`, with `s` to the left of `t`,
is at least the sum of the p-variations along `s` and `t`. -/
theorem add_le_union (f : α → E) {s t : Set α} {p : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
    pVariationOn f s p + pVariationOn f t p ≤ pVariationOn f (s ∪ t) p := by
  by_cases hs : s = ∅
  · simp [hs]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 hs)
  by_cases ht : t = ∅
  · simp [ht]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ t } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 ht)
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
    _ ≤ pVariationOn f (s ∪ t) p :=
      le_iSup_of_le ⟨n + 1 + m, w, by grind [Monotone], by grind⟩ le_rfl

/-- For `1 ≤ p ≤ q`, the normalized `q`-variation is controlled by the normalized
`p`-variation:
`(pVariationOn f s q) ^ (1 / q) ≤ (pVariationOn f s p) ^ (1 / p)`. -/
theorem norm_le (f : α → E) (s : Set α) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    (pVariationOn f s q) ^ (1 / q) ≤ (pVariationOn f s p) ^ (1 / p) := by
  have h :
      pVariationOn f s q ≤ (pVariationOn f s p) ^ (q / p) := by
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
      _ ≤ (pVariationOn f s p) ^ (q / p) :=
          ENNReal.rpow_le_rpow (le_iSup_of_le ⟨n, ⟨u, hu, us⟩⟩ le_rfl)
            (div_nonneg (by linarith) (by linarith))
  calc
    (pVariationOn f s q) ^ (1 / q) ≤ ((pVariationOn f s p) ^ (q / p)) ^ (1 / q) := by
      exact ENNReal.rpow_le_rpow h (one_div_nonneg.2 (by linarith))
    _ = (pVariationOn f s p) ^ ((q / p) * (1 / q)) := by
      rw [← ENNReal.rpow_mul]
    _ = (pVariationOn f s p) ^ (1 / p) := by
      congr 1
      field_simp [show q ≠ 0 by linarith]

end pVariationOn
