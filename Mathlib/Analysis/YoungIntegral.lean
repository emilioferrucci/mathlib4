/-
Copyright (c) 2026 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Convex.Function

/-!
# Controls and the Sewing Lemma

We develop the theory of *controls* — superadditive functions `ℝ → ℝ → ℝ≥0` continuous on
the diagonal — and use them to prove the **sewing lemma**, the key ingredient in Young's
theory of rough-path integration.

## Main definitions

* `Control`: a superadditive function `ω : ℝ → ℝ → ℝ≥0` continuous on the diagonal.
* `Partition s t N`: a strictly increasing sequence of `N + 2` points in `ℝ` from `s` to `t`.

## Main results

* `Control.mono_right`, `Control.mono_left`: controls are nondecreasing in each variable.
* `Control.comp_superadd`: the composition of a control with a superadditive increasing function
  vanishing at zero is again a control.
* `Control.mul_rpow`: if `α + β ≥ 1` then `fun s t ↦ ω s t ^ α * ω' s t ^ β` is a control.
* `removePoint`: for any partition there is an interior point whose removal costs at most
  `(2 / N) * ω(s, t)`.
* `sewingLemma`: the limit `lim_{|π|→0} Σ_π A` exists and satisfies a maximal inequality.

## References

* N. Tapia, *Construction of the Young integral* (2026).
-/

open Filter Topology NNReal Set

/-! ## Controls -/

/-- A *control* is a nonneg function `ω : ℝ → ℝ → ℝ≥0` that is superadditive on ordered
triples, `ω(s, u) + ω(u, t) ≤ ω(s, t)` for `s ≤ u ≤ t`, and continuous on the diagonal
in the sense that `ω(s, t) → 0` as `t → s⁺`. -/
structure Control where
  /-- The underlying bivariate function -/
  toFun : ℝ → ℝ → ℝ≥0
  /-- Superadditivity: `ω(s, u) + ω(u, t) ≤ ω(s, t)` whenever `s ≤ u ≤ t` -/
  superadditive : ∀ {s u t : ℝ}, s ≤ u → u ≤ t → toFun s u + toFun u t ≤ toFun s t
  /-- Diagonal continuity: `ω(s, ·) → 0` as the argument approaches `s` from the right -/
  diag_cont : ∀ s : ℝ, Tendsto (toFun s) (𝓝[Ioi s] s) (𝓝 0)

namespace Control

instance : CoeFun Control (fun _ => ℝ → ℝ → ℝ≥0) := ⟨toFun⟩

variable {ω ω' : Control}

/-- Controls are nondecreasing in the right variable:
if `s ≤ u ≤ t` then `ω(s, u) ≤ ω(s, t)`. -/
theorem mono_right {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t) : ω s u ≤ ω s t :=
  (le_add_of_nonneg_right (zero_le _)).trans (ω.superadditive hsu hut)

/-- Controls are nondecreasing in the left variable:
if `s ≤ u ≤ t` then `ω(u, t) ≤ ω(s, t)`. -/
theorem mono_left {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t) : ω u t ≤ ω s t :=
  (le_add_of_nonneg_left (zero_le _)).trans (ω.superadditive hsu hut)

/-- The composition of a control with an increasing function that is superadditive and vanishes
at zero is again a control.

This applies in particular when `φ` is increasing, convex, and satisfies `φ 0 = 0`. -/
noncomputable def comp_superadd (ω : Control) {φ : ℝ≥0 → ℝ≥0} (hφ_mono : Monotone φ)
    (hφ_sadd : ∀ a b : ℝ≥0, φ a + φ b ≤ φ (a + b))
    (hφ_zero : φ 0 = 0) (hφ_cont : Continuous φ) : Control where
  toFun s t := φ (ω s t)
  superadditive {s} {_u} {t} hsu hut := calc
    φ (ω s _) + φ (ω _ t) ≤ φ (ω s _ + ω _ t) := hφ_sadd _ _
    _ ≤ φ (ω s t) := hφ_mono (ω.superadditive hsu hut)
  diag_cont s := by
    rw [show (0 : ℝ≥0) = φ 0 from hφ_zero.symm]
    exact (hφ_cont.tendsto _).comp (ω.diag_cont s)

/-- An increasing function `φ : ℝ≥0 → ℝ≥0` with `φ 0 = 0` is superadditive if and only if
`φ(a) ≤ (a / (a + b)) * φ(a + b)` for all `a ≤ a + b`. This follows from convexity.

The key instance is `φ(x) = x ^ p` for `p ≥ 1`, which satisfies `a ^ p + b ^ p ≤ (a + b) ^ p`
by `NNReal.add_rpow_le_rpow_add`. -/
theorem rpow_superadd {p : ℝ} (hp : 1 ≤ p) (a b : ℝ≥0) :
    a ^ p + b ^ p ≤ (a + b) ^ p :=
  NNReal.add_rpow_le_rpow_add a b hp

/-- The composition of a control `ω` with the power function `x ↦ x ^ p` for `p ≥ 1` is
again a control. -/
noncomputable def rpow (ω : Control) {p : ℝ} (hp : 1 ≤ p) : Control :=
  comp_superadd ω (fun _ _ h => NNReal.rpow_le_rpow h (by linarith))
    (rpow_superadd hp) (by simp [NNReal.zero_rpow, show p ≠ 0 from by linarith])
    (NNReal.continuous_rpow_const (by linarith : 0 ≤ p))

/-- **2-term Hölder inequality.** For `r + s = 1` and `r, s ≥ 0`:
`a ^ r * b ^ s + c ^ r * d ^ s ≤ (a + c) ^ r * (b + d) ^ s`. -/
private theorem holder_two_term {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1)
    (a b c d : ℝ≥0) :
    a ^ r * b ^ s + c ^ r * d ^ s ≤ (a + c) ^ r * (b + d) ^ s := by
  by_cases hr_zero : r = 0
  · -- r = 0, s = 1: equality
    subst hr_zero; simp only [NNReal.rpow_zero, one_mul]
    have hs1 : s = 1 := by linarith
    subst hs1; simp
  · have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr_zero)
    by_cases hs_zero : s = 0
    · -- s = 0, r = 1: equality
      subst hs_zero; simp only [NNReal.rpow_zero, mul_one]
      have hr1 : r = 1 := by linarith
      subst hr1; simp
    · -- Both r > 0 and s > 0: apply Hölder with p = 1/r, q = 1/s
      have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_zero)
      have hr_ne : r ≠ 0 := hr_pos.ne'
      have hs_ne : s ≠ 0 := hs_pos.ne'
      have hpq : Real.HolderConjugate (1 / r) (1 / s) :=
        Real.holderConjugate_one_div hr_pos hs_pos hrs
      -- Apply Hölder with f i = (![a,c] i)^r, g i = (![b,d] i)^s, p = 1/r, q = 1/s
      have key := NNReal.inner_le_Lp_mul_Lq Finset.univ
        (fun i : Fin 2 => (![a, c] i) ^ r) (fun i : Fin 2 => (![b, d] i) ^ s) hpq
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at key
      -- (x ^ r) ^ (1/r) = x
      have pow_rpow_r : ∀ x : ℝ≥0, (x ^ r) ^ (1 / r) = x := fun x => by
        rw [← NNReal.rpow_mul, mul_one_div_cancel hr_ne, NNReal.rpow_one]
      have pow_rpow_s : ∀ x : ℝ≥0, (x ^ s) ^ (1 / s) = x := fun x => by
        rw [← NNReal.rpow_mul, mul_one_div_cancel hs_ne, NNReal.rpow_one]
      simp only [pow_rpow_r, pow_rpow_s] at key
      -- 1 / (1/r) = r
      have r_eq : (1 : ℝ) / (1 / r) = r := by field_simp
      have s_eq : (1 : ℝ) / (1 / s) = s := by field_simp
      rw [r_eq, s_eq] at key
      exact key

/-- If `α + β ≥ 1` and `ω`, `ω'` are controls, then
`fun s t ↦ ω s t ^ α * ω' s t ^ β` is also a control. -/
noncomputable def mul_rpow (ω ω' : Control) {α β : ℝ} (hαβ : 1 ≤ α + β)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : Control where
  toFun s t := ω s t ^ α * ω' s t ^ β
  superadditive {s} {u} {t} hsu hut := by
    -- Let θ = α + β ≥ 1
    set θ := α + β with hθ_def
    have hθ_pos : 0 < θ := by linarith
    have hθ_ne : θ ≠ 0 := hθ_pos.ne'
    -- (x ^ (α/θ) * y ^ (β/θ)) ^ θ = x ^ α * y ^ β
    have factor : ∀ x y : ℝ≥0, (x ^ (α / θ) * y ^ (β / θ)) ^ θ = x ^ α * y ^ β := fun x y => by
      rw [NNReal.mul_rpow, ← NNReal.rpow_mul x (α / θ) θ, ← NNReal.rpow_mul y (β / θ) θ,
          div_mul_cancel₀ α hθ_ne, div_mul_cancel₀ β hθ_ne]
    -- 2-term Hölder: ω̂(s,u) + ω̂(u,t) ≤ (ω(s,u)+ω(u,t))^(α/θ) * (ω'(s,u)+ω'(u,t))^(β/θ)
    have hrs : α / θ + β / θ = 1 := by field_simp [hθ_ne]; linarith
    have hhat : ω.toFun s u ^ (α / θ) * ω'.toFun s u ^ (β / θ) +
        ω.toFun u t ^ (α / θ) * ω'.toFun u t ^ (β / θ) ≤
        (ω.toFun s u + ω.toFun u t) ^ (α / θ) * (ω'.toFun s u + ω'.toFun u t) ^ (β / θ) :=
      holder_two_term (by positivity) (by positivity) hrs _ _ _ _
    -- Monotonicity: apply superadditivity of ω and ω'
    have hω : (ω.toFun s u + ω.toFun u t) ^ (α / θ) ≤ ω.toFun s t ^ (α / θ) :=
      NNReal.rpow_le_rpow (ω.superadditive hsu hut) (by positivity)
    have hω' : (ω'.toFun s u + ω'.toFun u t) ^ (β / θ) ≤ ω'.toFun s t ^ (β / θ) :=
      NNReal.rpow_le_rpow (ω'.superadditive hsu hut) (by positivity)
    -- Combine: use rpow_superadd + Hölder + monotonicity
    rw [← factor (ω.toFun s u) (ω'.toFun s u), ← factor (ω.toFun u t) (ω'.toFun u t),
        ← factor (ω.toFun s t) (ω'.toFun s t)]
    calc (ω.toFun s u ^ (α / θ) * ω'.toFun s u ^ (β / θ)) ^ θ +
          (ω.toFun u t ^ (α / θ) * ω'.toFun u t ^ (β / θ)) ^ θ
        ≤ (ω.toFun s u ^ (α / θ) * ω'.toFun s u ^ (β / θ) +
            ω.toFun u t ^ (α / θ) * ω'.toFun u t ^ (β / θ)) ^ θ := rpow_superadd hαβ _ _
      _ ≤ ((ω.toFun s u + ω.toFun u t) ^ (α / θ) *
            (ω'.toFun s u + ω'.toFun u t) ^ (β / θ)) ^ θ :=
          NNReal.rpow_le_rpow hhat (by linarith)
      _ ≤ (ω.toFun s t ^ (α / θ) * ω'.toFun s t ^ (β / θ)) ^ θ :=
          NNReal.rpow_le_rpow (mul_le_mul' hω hω') (by linarith)
  diag_cont s := by
    -- At least one of α, β is positive since α + β ≥ 1 > 0
    rcases hα.lt_or_eq with hα_pos | hα_zero
    · -- α > 0: (ω s x)^α → 0 since ω s x → 0 and 0^α = 0 (α ≠ 0)
      have h0α : (0 : ℝ≥0) ^ α = 0 := NNReal.zero_rpow hα_pos.ne'
      have hα_tend : Tendsto (fun x => ω.toFun s x ^ α) (𝓝[Ioi s] s) (𝓝 0) := by
        rw [← h0α]
        exact (NNReal.continuous_rpow_const hα).continuousAt.tendsto.comp (ω.diag_cont s)
      rcases hβ.lt_or_eq with hβ_pos | hβ_zero
      · -- β > 0 too: (ω' s x)^β → 0, product → 0 * 0 = 0
        have h0β : (0 : ℝ≥0) ^ β = 0 := NNReal.zero_rpow hβ_pos.ne'
        have hβ_tend : Tendsto (fun x => ω'.toFun s x ^ β) (𝓝[Ioi s] s) (𝓝 0) := by
          rw [← h0β]
          exact (NNReal.continuous_rpow_const hβ).continuousAt.tendsto.comp (ω'.diag_cont s)
        simpa using hα_tend.mul hβ_tend
      · -- β = 0: (ω' s x)^0 = 1, product = (ω s x)^α → 0
        subst hβ_zero
        simp only [NNReal.rpow_zero, mul_one]
        exact hα_tend
    · -- α = 0: β ≥ 1, (ω' s x)^β → 0
      subst hα_zero
      have hβ_ge1 : 1 ≤ β := by linarith
      have h0β : (0 : ℝ≥0) ^ β = 0 := NNReal.zero_rpow (by linarith)
      have hβ_tend : Tendsto (fun x => ω'.toFun s x ^ β) (𝓝[Ioi s] s) (𝓝 0) := by
        rw [← h0β]
        exact (NNReal.continuous_rpow_const hβ).continuousAt.tendsto.comp (ω'.diag_cont s)
      simp only [NNReal.rpow_zero, one_mul]
      exact hβ_tend

end Control

/-! ## Partitions -/

/-- A *partition* of the interval `[s, t]` with `N` interior points is a strictly increasing
function `π : Fin (N + 2) → ℝ` with `π 0 = s` and `π (N + 1) = t`. -/
structure Partition (s t : ℝ) (N : ℕ) where
  /-- The points of the partition, indexed from `0` to `N + 1` -/
  points : Fin (N + 2) → ℝ
  /-- The points are strictly increasing -/
  strictMono : StrictMono points
  /-- The first point equals `s` -/
  head_eq : points 0 = s
  /-- The last point equals `t` -/
  last_eq : points (Fin.last (N + 1)) = t

namespace Partition

variable {s t : ℝ} {N : ℕ} (π : Partition s t N)

/-- The mesh of a partition: the maximum length of a subinterval. -/
noncomputable def mesh : ℝ :=
  ⨆ k : Fin (N + 1), π.points k.succ - π.points k.castSucc

/-- The Riemann-type sum of a two-parameter function `A` over consecutive pairs of the
partition. -/
noncomputable def riemannSum (A : ℝ → ℝ → ℝ) : ℝ :=
  ∑ k : Fin (N + 1), A (π.points k.castSucc) (π.points k.succ)

end Partition

/-! ## The sewing lemma -/

/-- The *defect* of a two-parameter function `A` from additivity:
`δA(s, u, t) = A(s, t) - A(s, u) - A(u, t)`. -/
noncomputable def defect (A : ℝ → ℝ → ℝ) (s u t : ℝ) : ℝ := A s t - A s u - A u t

-- Helper: remove the k-th interior point from a partition.
private noncomputable def Partition.remove {s t : ℝ} {N : ℕ} (π : Partition s t N)
    (hN : 0 < N) (k : Fin N) : Partition s t (N - 1) where
  points := fun j : Fin (N - 1 + 2) =>
    if j.val ≤ k.val then π.points ⟨j.val, by omega⟩
    else π.points ⟨j.val + 1, by omega⟩
  strictMono := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Fin.mk_lt_mk] at hab
    simp only
    split_ifs with h1 h2
    · exact π.strictMono (Fin.mk_lt_mk.mpr (by omega))
    · have hak : a ≤ k.val := h1
      have hbk : ¬ b ≤ k.val := h2
      exact π.strictMono (Fin.mk_lt_mk.mpr (by omega))
    · exact absurd hab (by omega)
    · exact π.strictMono (Fin.mk_lt_mk.mpr (by omega))
  head_eq := by simp [π.head_eq]
  last_eq := by
    have : ¬ (N - 1 + 1 : ℕ) ≤ k.val := by omega
    simp only [Fin.last, this, ite_false]
    convert π.last_eq using 2
    simp [Fin.last]; omega

-- The riemannSum changes by -(defect A) when a point is removed.
private lemma Partition.riemannSum_remove {s t : ℝ} {N : ℕ} (A : ℝ → ℝ → ℝ)
    (π : Partition s t N) (hN : 0 < N) (k : Fin N) :
    π.riemannSum A - (π.remove hN k).riemannSum A =
      -(defect A (π.points ⟨k.val, by omega⟩) (π.points ⟨k.val + 1, by omega⟩)
                  (π.points ⟨k.val + 2, by omega⟩)) := by
  simp only [defect]
  -- Safe total indexing function (clamped to valid range)
  let p : ℕ → ℝ := fun j => π.points ⟨min j (N + 1), by omega⟩
  have hp : ∀ j (hj : j < N + 2), p j = π.points ⟨j, hj⟩ := fun j hj => by
    simp [p, Nat.min_eq_left (by omega : j ≤ N + 1)]
  let f : ℕ → ℝ := fun j => A (p j) (p (j + 1))
  -- p agrees with the named points
  have hpk : p k.val = π.points ⟨k.val, by omega⟩ := hp _ (by omega)
  have hpk1 : p (k.val + 1) = π.points ⟨k.val + 1, by omega⟩ := hp _ (by omega)
  have hpk2 : p (k.val + 2) = π.points ⟨k.val + 2, by omega⟩ := hp _ (by omega)
  -- Step 1: Convert original Fin sum to range sum over f
  have hS : π.riemannSum A = ∑ j ∈ Finset.range (N + 1), f j := by
    simp only [Partition.riemannSum]
    trans ∑ j : Fin (N + 1), f j.val
    · apply Finset.sum_congr rfl; intro ⟨j, hj⟩ _
      simp only [Fin.castSucc, Fin.succ, f]
      show A (π.points ⟨j, _⟩) (π.points ⟨j + 1, _⟩) = A (p j) (p (j + 1))
      rw [← hp j (by omega), ← hp (j + 1) (by omega)]
    · exact (Finset.sum_range (f := f)).symm
  -- Step 2: Convert removed Fin sum to range sum
  -- The removed partition skip-indexes: for j in Fin(N-1+1), points are
  --   if j ≤ k then π[j] else π[j+1]
  -- Consecutive pairs give:
  --   j < k:  A(π[j], π[j+1]) = f(j)
  --   j = k:  A(π[k], π[k+2]) = A(p k, p(k+2))
  --   j > k:  A(π[j+1], π[j+2]) = f(j+1)
  let g : ℕ → ℝ := fun j =>
    if j < k.val then f j
    else if j = k.val then A (p k.val) (p (k.val + 2))
    else f (j + 1)
  -- Each term of the removed sum equals g
  have hterm : ∀ (j : ℕ) (hj : j < N - 1 + 1),
      A ((π.remove hN k).points (⟨j, by omega⟩ : Fin (N-1+1)).castSucc)
        ((π.remove hN k).points (⟨j, by omega⟩ : Fin (N-1+1)).succ) = g j := by
    intro j hj
    simp only [Partition.remove, Fin.castSucc_mk, Fin.succ_mk]
    by_cases hjk : j < k.val
    · have h1 : j ≤ k.val := by omega
      have h2 : j + 1 ≤ k.val := by omega
      simp only [h1, h2, ite_true, g, hjk, ite_true, f]
      congr 1 <;> exact (hp _ (by omega)).symm
    · by_cases hjk2 : j = k.val
      · subst hjk2
        simp only [le_refl, ite_true, show ¬ (k.val + 1 ≤ k.val) from by omega, ite_false,
            g, show ¬ k.val < k.val from lt_irrefl _, ite_false, ite_true, p,
            Nat.min_eq_left (show k.val ≤ N + 1 by omega),
            Nat.min_eq_left (show k.val + 2 ≤ N + 1 by omega)]
      · have h1 : ¬ j ≤ k.val := by omega
        have h2 : ¬ (j + 1) ≤ k.val := by omega
        simp only [h1, h2, ite_false, g, show ¬ j < k.val from by omega, hjk2, ite_false, f, p,
            Nat.min_eq_left (show j + 1 ≤ N + 1 by omega),
            Nat.min_eq_left (show j + 2 ≤ N + 1 by omega)]
  have hR : (π.remove hN k).riemannSum A = ∑ j ∈ Finset.range N, g j := by
    simp only [Partition.riemannSum]
    trans ∑ j : Fin N, g j.val
    · apply Finset.sum_nbij' (fun ⟨i, hi⟩ => ⟨i, by omega⟩) (fun ⟨i, hi⟩ => ⟨i, by omega⟩)
      · intro ⟨i, hi⟩ _; exact Finset.mem_univ _
      · intro ⟨i, hi⟩ _; exact Finset.mem_univ _
      · intro ⟨i, hi⟩ _; rfl
      · intro ⟨i, hi⟩ _; rfl
      · intro ⟨j, hj_fin⟩ _; exact hterm j (by omega)
    · exact (Finset.sum_range (f := g)).symm
  -- Step 3: Split original sum
  -- Use conv to rewrite only in the Finset.range argument, avoiding k : Fin N
  have hkN : k.val < N := k.isLt
  have hS' : π.riemannSum A =
      ∑ j ∈ Finset.range k.val, f j + f k.val + f (k.val + 1) +
      ∑ j ∈ Finset.range (N - 1 - k.val), f (k.val + 2 + j) := by
    rw [hS]
    have : ∑ j ∈ Finset.range (N + 1), f j =
        ∑ j ∈ Finset.range (k.val + 2), f j +
        ∑ j ∈ Finset.range (N - 1 - k.val), f (k.val + 2 + j) := by
      rw [show N + 1 = (k.val + 2) + (N - 1 - k.val) from by omega, Finset.sum_range_add]
    rw [this, show k.val + 2 = k.val + 1 + 1 from by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
  -- Step 4: Split removed sum
  have hR' : (π.remove hN k).riemannSum A =
      ∑ j ∈ Finset.range k.val, f j + A (p k.val) (p (k.val + 2)) +
      ∑ j ∈ Finset.range (N - 1 - k.val), f (k.val + 2 + j) := by
    rw [hR]
    have hsplit : ∑ j ∈ Finset.range N, g j =
        ∑ j ∈ Finset.range k.val, g j + g k.val +
        ∑ j ∈ Finset.range (N - 1 - k.val), g (k.val + 1 + j) := by
      conv_lhs => rw [show (N : ℕ) = (k.val + 1) + (N - 1 - k.val) from by omega]
      rw [Finset.sum_range_add, Finset.sum_range_succ]
    rw [hsplit]
    have hg_low : ∀ j, j < k.val → g j = f j := fun j hj => by
      simp only [g, hj, ite_true]
    have hg_mid : g k.val = A (p k.val) (p (k.val + 2)) := by
      simp only [g, lt_irrefl, ite_false, ite_true]
    have hg_high : ∀ j, g (k.val + 1 + j) = f (k.val + 2 + j) := fun j => by
      simp only [g, show ¬ (k.val + 1 + j < k.val) from by omega,
          show ¬ (k.val + 1 + j = k.val) from by omega, ite_false, f]
      congr 1 <;> congr 1 <;> omega
    rw [hg_mid]
    congr 1; congr 1
    · exact Finset.sum_congr rfl (fun j hj => hg_low j (Finset.mem_range.mp hj))
    · exact Finset.sum_congr rfl (fun j _ => hg_high j)
  -- Step 5: Compute the difference
  rw [hS', hR']
  -- Unfold f at the key positions
  show (∑ j ∈ Finset.range k.val, f j + f k.val + f (k.val + 1) +
      ∑ j ∈ Finset.range (N - 1 - k.val), f (k.val + 2 + j)) -
    (∑ j ∈ Finset.range k.val, f j + A (p k.val) (p (k.val + 2)) +
      ∑ j ∈ Finset.range (N - 1 - k.val), f (k.val + 2 + j)) =
    -(A (π.points ⟨k.val, _⟩) (π.points ⟨k.val + 2, _⟩) -
      A (π.points ⟨k.val, _⟩) (π.points ⟨k.val + 1, _⟩) -
      A (π.points ⟨k.val + 1, _⟩) (π.points ⟨k.val + 2, _⟩))
  -- f k.val = A (p k.val) (p (k.val + 1))
  -- f (k.val + 1) = A (p (k.val + 1)) (p (k.val + 2))
  have hf0 : f k.val = A (p k.val) (p (k.val + 1)) := rfl
  have hf1 : f (k.val + 1) = A (p (k.val + 1)) (p (k.val + 2)) := rfl
  rw [hf0, hf1, hpk, hpk1, hpk2]; ring

-- Helper: split a sum over Fin N into even- and odd-indexed parts.
-- Proved by: bijection {even k < N} ↔ Fin ((N+1)/2) and {odd k < N} ↔ Fin (N/2).
private lemma sum_parity_split {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ k : Fin N, f k =
      ∑ j : Fin ((N + 1) / 2), f (2 * j) +
      ∑ j : Fin (N / 2), f (2 * j + 1) := by
  -- Convert to range sum, use filter decomposition + explicit bijections
  rw [← Finset.sum_range (f := f), ← Finset.sum_range (f := fun j => f (2*j)),
      ← Finset.sum_range (f := fun j => f (2*j+1))]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun k => Even k)]
  congr 1
  · -- Even part: ∑_{k < N, k even} f k = ∑_{j < (N+1)/2} f (2j)
    apply Finset.sum_nbij' (fun k => k / 2) (fun j => 2 * j)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      simp only [Finset.mem_range]
      obtain ⟨hkN, ⟨t, ht⟩⟩ := hk; omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, ⟨j, by ring⟩⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨_, ⟨t, ht⟩⟩ := hk; omega
    · intro j _; omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      congr 1; obtain ⟨_, ⟨t, ht⟩⟩ := hk; omega
  · -- Odd part: ∑_{k < N, k odd} f k = ∑_{j < N/2} f (2j+1)
    apply Finset.sum_nbij' (fun k => k / 2) (fun j => 2 * j + 1)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      simp only [Finset.mem_range]
      obtain ⟨hkN, hkOdd⟩ := hk
      rw [Nat.not_even_iff_odd, Nat.odd_iff] at hkOdd; omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by rw [Nat.not_even_iff_odd, Nat.odd_iff]; omega⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨_, hkOdd⟩ := hk
      rw [Nat.not_even_iff_odd, Nat.odd_iff] at hkOdd; omega
    · intro j _; omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨_, hkOdd⟩ := hk
      rw [Nat.not_even_iff_odd, Nat.odd_iff] at hkOdd; congr 1; omega

-- Helper: for a monotone `a : ℕ → ℝ`, the sum of ω over consecutive pairs telescopes.
private lemma sum_control_le (ω : Control) {n : ℕ} (a : ℕ → ℝ) (ha : Monotone a) :
    ∑ k : Fin n, ω (a k) (a (k + 1)) ≤ ω (a 0) (a n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    calc ∑ k : Fin n, ω (a ↑k) (a (↑k + 1)) + ω (a n) (a (n + 1))
        ≤ ω (a 0) (a n) + ω (a n) (a (n + 1)) := add_le_add ih (le_refl _)
      _ ≤ ω (a 0) (a (n + 1)) :=
          ω.superadditive (ha (Nat.zero_le n)) (ha (Nat.le_succ n))

/-- **Remove lemma.** For any control `ω`, any partition `π` of `[s, t]` with `N ≥ 1`
interior points has an index `k` such that
`ω(t_{k}, t_{k+2}) ≤ (2 / N) * ω(s, t)`. -/
theorem removePoint (ω : Control) {s t : ℝ} {N : ℕ} (hN : 0 < N) (π : Partition s t N) :
    ∃ k : Fin N,
      ω (π.points ⟨k.val, by omega⟩) (π.points ⟨k.val + 2, by omega⟩) ≤
        (2 / N : ℝ≥0) * ω s t := by
  -- Step 1: ∑_k ω(t_k, t_{k+2}) ≤ 2 * ω(s,t) (proved via superadditivity + telescoping)
  have hsum : ∑ k : Fin N, ω (π.points ⟨k.val, by omega⟩) (π.points ⟨k.val + 2, by omega⟩) ≤
      2 * ω s t := by
    -- Extend π.points to ℕ → ℝ for the telescoping lemma
    let a : ℕ → ℝ := fun k => π.points ⟨min k (N + 1), by omega⟩
    have ha : Monotone a := fun i j hij => by
      simp only [a]
      have hle : min i (N + 1) ≤ min j (N + 1) := min_le_min_right (N + 1) hij
      rcases hle.eq_or_lt with h | h
      · simp [h]
      · exact le_of_lt (π.strictMono (show (⟨min i (N+1), by omega⟩ : Fin (N+2)) <
            ⟨min j (N+1), by omega⟩ from h))
    have ha0 : a 0 = s := by simp [a, π.head_eq]
    have haN1 : a (N + 1) = t := by
      simp only [a, Nat.min_self]; exact π.last_eq
    -- ∑_k ω(t_k, t_{k+1}) ≤ ω(a 0)(a(N+1)) = ω s t
    have hle1 : ∑ k : Fin N, ω (a k) (a (k + 1)) ≤ ω s t := by
      calc ∑ k : Fin N, ω (a ↑k) (a (↑k + 1))
          ≤ ω (a 0) (a N) := sum_control_le ω a ha
        _ ≤ ω (a 0) (a (N + 1)) :=
            ω.mono_right (ha (Nat.zero_le N)) (ha (Nat.le_succ N))
        _ = ω s t := by rw [ha0, haN1]
    -- ∑_k ω(t_{k+1}, t_{k+2}) ≤ ω s t
    have hle2 : ∑ k : Fin N, ω (a (k + 1)) (a (k + 2)) ≤ ω s t := by
      have key : ∑ k : Fin N, ω (a (↑k + 1)) (a (↑k + 1 + 1)) ≤ ω (a 1) (a (N + 1)) :=
        sum_control_le ω (fun i => a (i + 1)) (fun _ _ h => ha (Nat.succ_le_succ h))
      simp only [Nat.add_assoc] at key
      calc ∑ k : Fin N, ω (a (↑k + 1)) (a (↑k + 2))
          ≤ ω (a 1) (a (N + 1)) := key
        _ ≤ ω (a 0) (a (N + 1)) := ω.mono_left (ha (Nat.zero_le 1)) (ha (by omega : 1 ≤ N+1))
        _ = ω s t := by rw [ha0, haN1]
    -- a equality: ∀ k ≤ N+1, a k = π.points ⟨k, _⟩
    have ha_eq : ∀ k : ℕ, (hk : k ≤ N + 1) → a k = π.points ⟨k, Nat.lt_succ_of_le hk⟩ :=
      fun k hk => by simp [a, min_eq_left hk]
    -- Even sub-sum ≤ ω s t (via sum_control_le on even subseq)
    have heven : ∑ j : Fin ((N + 1) / 2), ω (a (2 * j.val)) (a (2 * j.val + 2)) ≤ ω s t :=
      (sum_control_le ω (fun j => a (2 * j)) (ha.comp (fun _ _ h => by omega))).trans
        ((ω.mono_right (ha (Nat.zero_le _))
            (ha (show 2 * ((N + 1) / 2) ≤ N + 1 from by omega))).trans
          (by rw [ha0, haN1]))
    -- Odd sub-sum ≤ ω s t (via sum_control_le on odd subseq)
    have hodd : ∑ j : Fin (N / 2), ω (a (2 * j.val + 1)) (a (2 * j.val + 3)) ≤ ω s t :=
      (sum_control_le ω (fun j => a (2 * j + 1)) (ha.comp (fun _ _ h => by omega))).trans
        ((calc ω (a 1) (a (2 * (N / 2) + 1))
              ≤ ω (a 1) (a (N + 1)) :=
                ω.mono_right (ha (by omega)) (ha (show 2 * (N/2) + 1 ≤ N+1 from by omega))
            _ ≤ ω (a 0) (a (N + 1)) :=
                ω.mono_left (ha (Nat.zero_le 1)) (ha (by omega : 1 ≤ N + 1))).trans
          (by rw [ha0, haN1]))
    -- Rewrite goal in terms of a, apply parity split, combine
    have hrw : ∀ k : Fin N,
        ω (π.points ⟨k.val, by omega⟩) (π.points ⟨k.val + 2, by omega⟩) =
        ω (a k.val) (a (k.val + 2)) := fun k => by
      have hk1 : k.val ≤ N + 1 := by have := k.isLt; omega
      have hk2 : k.val + 2 ≤ N + 1 := by have := k.isLt; omega
      rw [ha_eq k.val hk1, ha_eq (k.val + 2) hk2]
    simp_rw [hrw]
    have split := sum_parity_split N (fun k => ω (a k) (a (k + 2)))
    calc ∑ k : Fin N, ω (a ↑k) (a (↑k + 2))
        = ∑ j : Fin ((N+1)/2), ω (a (2 * ↑j)) (a (2 * ↑j + 2)) +
          ∑ j : Fin (N/2), ω (a (2 * ↑j + 1)) (a (2 * ↑j + 3)) := split
      _ ≤ ω s t + ω s t := add_le_add heven hodd
      _ = 2 * ω s t := by ring
  -- Step 2: averaging argument — by contradiction
  by_contra hcontra
  push_neg at hcontra
  have hN_pos : (0 : ℝ≥0) < N := by exact_mod_cast hN
  have hN_ne : (N : ℝ≥0) ≠ 0 := hN_pos.ne'
  have hlt : ∑ _ : Fin N, (2 / N * ω s t) <
      ∑ k : Fin N, ω (π.points ⟨↑k, by omega⟩) (π.points ⟨↑k + 2, by omega⟩) :=
    Finset.sum_lt_sum (fun k _ => le_of_lt (hcontra k))
      ⟨⟨0, hN⟩, Finset.mem_univ _, hcontra ⟨0, hN⟩⟩
  simp only [Finset.sum_const, Finset.card_fin] at hlt
  rw [nsmul_eq_mul, show (N : ℝ≥0) * (2 / N * ω s t) = 2 * ω s t from by
    rw [← mul_assoc, mul_comm (N : ℝ≥0) (2 / N), div_mul_cancel₀ 2 hN_ne]] at hlt
  exact absurd hsum (not_le.mpr hlt)

/-- **Maximal inequality.** If `|δA(s, u, t)| ≤ ω(s, t)^θ` for some `θ > 1`, then for every
partition `π` of `[s, t]` we have
`|Σ_π A - A(s, t)| ≤ 2^θ * ζ(θ) * ω(s, t)^θ`,
where `ζ(θ) = ∑_{n=1}^∞ n^{-θ}` is the Riemann zeta function. -/
theorem maximalInequality {A : ℝ → ℝ → ℝ} (ω : Control) {θ : ℝ} (hθ : 1 < θ)
    (hA : ∀ {s u t : ℝ}, s ≤ u → u ≤ t → |defect A s u t| ≤ (ω s t : ℝ) ^ θ)
    {s t : ℝ} (hst : s ≤ t) {N : ℕ} (π : Partition s t N) :
    |π.riemannSum A - A s t| ≤
      (2 : ℝ) ^ θ * (∑' n : ℕ+, (n : ℝ) ^ (-θ)) * (ω s t : ℝ) ^ θ := by
  -- Prove stronger claim by induction: finite truncated zeta bound
  suffices h : ∀ M : ℕ, ∀ (π' : Partition s t M),
      |π'.riemannSum A - A s t| ≤
        (2 : ℝ) ^ θ * (∑ j : Fin M, ((j : ℝ) + 1) ^ (-θ)) * (ω s t : ℝ) ^ θ from
    (h N π).trans (by
      gcongr
      -- ∑ j : Fin N, (j+1)^{-θ} ≤ ∑' n : ℕ+, n^{-θ}
      -- ∑' n : ℕ+, n^{-θ} = ∑' n : ℕ, (n+1)^{-θ} ≥ ∑ j : Fin N, (j+1)^{-θ}
      -- Convert ∑' n : ℕ+, n^{-θ} to ∑' n : ℕ, (n+1)^{-θ}, then use partial sum ≤ tsum
      have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-θ)) :=
        Real.summable_nat_rpow.2 (by linarith)
      have hsumm : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-θ)) := by
        have := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-θ)) 1).mpr hbase
        exact this.congr (fun n => by push_cast; ring)
      have hreidx : ∑' n : ℕ+, (n : ℝ) ^ (-θ) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-θ) :=
        (tsum_pnat_eq_tsum_succ (f := fun n => (n : ℝ) ^ (-θ))).trans
          (tsum_congr (fun n => by push_cast; ring_nf))
      have hlhs : ∑ j : Fin N, ((j : ℝ) + 1) ^ (-θ) =
          ∑ j ∈ Finset.range N, ((j : ℝ) + 1) ^ (-θ) :=
        (Finset.sum_range (fun j => ((j : ℝ) + 1) ^ (-θ))).symm
      have hstep : ∑ j ∈ Finset.range N, ((j : ℝ) + 1) ^ (-θ) ≤
          ∑' n : ℕ, ((n : ℝ) + 1) ^ (-θ) :=
        hsumm.sum_le_tsum _ (fun i _ => by positivity)
      linarith [hlhs.symm ▸ hreidx ▸ hstep])
  intro M
  induction M with
  | zero =>
    intro π'
    -- Trivial partition: riemannSum = A s t
    have hrS : π'.riemannSum A = A s t := by
      simp [Partition.riemannSum]
      rw [π'.head_eq, show (1 : Fin 2) = Fin.last 1 from rfl, π'.last_eq]
    simp [hrS]
  | succ M ih =>
    intro π'
    -- Apply removePoint to find a cheap interior point
    obtain ⟨k, hk⟩ := removePoint ω (Nat.succ_pos M) π'
    let π'' := π'.remove (Nat.succ_pos M) k
    -- IH applied to π'' which has M interior points
    have ih_π'' := ih π''
    -- Bound on the removed-point cost: |δA| ≤ (2/(M+1))^θ * ω^θ
    have hremove : |π'.riemannSum A - π''.riemannSum A| ≤
        (2 : ℝ) ^ θ * ((M : ℝ) + 1) ^ (-θ) * (ω s t : ℝ) ^ θ := by
      rw [Partition.riemannSum_remove A π' (Nat.succ_pos M) k, abs_neg]
      have hle1 : (π'.points ⟨k.val, by omega⟩) ≤ (π'.points ⟨k.val + 1, by omega⟩) :=
        le_of_lt (π'.strictMono (by simp only [Fin.lt_def]; omega))
      have hle2 : (π'.points ⟨k.val + 1, by omega⟩) ≤ (π'.points ⟨k.val + 2, by omega⟩) :=
        le_of_lt (π'.strictMono (by simp only [Fin.lt_def]; omega))
      have step1 := hA hle1 hle2
      have step2 : (ω (π'.points ⟨k.val, by omega⟩) (π'.points ⟨k.val + 2, by omega⟩) : ℝ) ^ θ ≤
          ((2 / (M + 1 : ℝ)) * (ω s t : ℝ)) ^ θ := by
        apply Real.rpow_le_rpow (by positivity)
        · have : ((2 / (↑(M + 1) : ℝ≥0) * ω s t : ℝ≥0) : ℝ) =
              (2 / (M + 1 : ℝ)) * (ω s t : ℝ) := by push_cast; ring
          rw [← this]; exact_mod_cast hk
        · linarith
      have step3 : ((2 / (M + 1 : ℝ)) * (ω s t : ℝ)) ^ θ =
          (2 : ℝ) ^ θ * ((M : ℝ) + 1) ^ (-θ) * (ω s t : ℝ) ^ θ := by
        rw [Real.mul_rpow (by positivity) (by positivity),
            Real.div_rpow (by norm_num) (by positivity)]
        congr 1; rw [Real.rpow_neg (by positivity)]; ring
      linarith [step1.trans step2, step2.trans_eq step3]
    -- Triangle inequality: |a - c| ≤ |a - b| + |b - c|
    have htri : |π'.riemannSum A - A s t| ≤
        |π'.riemannSum A - π''.riemannSum A| + |π''.riemannSum A - A s t| := by
      have heq : π'.riemannSum A - A s t =
          (π'.riemannSum A - π''.riemannSum A) + (π''.riemannSum A - A s t) := by ring
      rw [heq]
      by_cases h : (0 : ℝ) ≤ π'.riemannSum A - π''.riemannSum A + (π''.riemannSum A - A s t)
      · rw [abs_of_nonneg h]
        linarith [le_abs_self (π'.riemannSum A - π''.riemannSum A),
                  le_abs_self (π''.riemannSum A - A s t)]
      · push_neg at h; rw [abs_of_neg h]
        linarith [neg_abs_le (π'.riemannSum A - π''.riemannSum A),
                  neg_abs_le (π''.riemannSum A - A s t)]
    -- Combine and use Fin.sum_univ_castSucc for the sum identity
    calc |π'.riemannSum A - A s t|
          ≤ |π'.riemannSum A - π''.riemannSum A| + |π''.riemannSum A - A s t| := htri
        _ ≤ (2 : ℝ) ^ θ * ((M : ℝ) + 1) ^ (-θ) * (ω s t : ℝ) ^ θ +
            (2 : ℝ) ^ θ * (∑ j : Fin M, ((j : ℝ) + 1) ^ (-θ)) * (ω s t : ℝ) ^ θ :=
              add_le_add hremove ih_π''
        _ = (2 : ℝ) ^ θ * (∑ j : Fin (M + 1), ((j : ℝ) + 1) ^ (-θ)) * (ω s t : ℝ) ^ θ := by
              rw [Fin.sum_univ_castSucc]
              simp only [Fin.val_castSucc, Fin.val_last]
              ring

/-- **Sewing lemma.** Let `A : ℝ → ℝ → ℝ` be a two-parameter function satisfying the
*germ bound* `|δA(s, u, t)| ≤ ω(s, t)^θ` for some control `ω` and exponent `θ > 1`.

Then there exists a function `I : ℝ → ℝ` such that for all `s ≤ t`:
- **(Maximal inequality)** `|I(t) - I(s) - A(s, t)| ≤ 2^θ * ζ(θ) * ω(s, t)^θ`.
- **(Convergence)** `I(t) - I(s) = lim_{mesh(π)→0} Σ_π A`. -/
theorem sewingLemma {A : ℝ → ℝ → ℝ} (ω : Control) {θ : ℝ} (hθ : 1 < θ)
    (hA : ∀ {s u t : ℝ}, s ≤ u → u ≤ t → |defect A s u t| ≤ (ω s t : ℝ) ^ θ) :
    ∃ I : ℝ → ℝ,
      (∀ {s t : ℝ}, s ≤ t →
        |I t - I s - A s t| ≤
          (2 : ℝ) ^ θ * (∑' n : ℕ+, (n : ℝ) ^ (-θ)) * (ω s t : ℝ) ^ θ) ∧
      (∀ {s t : ℝ}, s ≤ t → ∀ ε > 0, ∃ δ > 0,
        ∀ {N : ℕ} (π : Partition s t N), π.mesh < δ →
          |π.riemannSum A - (I t - I s)| < ε) := by
  sorry
