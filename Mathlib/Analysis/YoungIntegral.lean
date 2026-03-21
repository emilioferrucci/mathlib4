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
triples, `ω(s, u) + ω(u, t) ≤ ω(s, t)` for `s ≤ u ≤ t`, vanishes on the diagonal, and is
jointly continuous on the simplex `{(s, t) | s ≤ t}`. -/
structure Control where
  /-- The underlying bivariate function -/
  toFun : ℝ → ℝ → ℝ≥0
  /-- Superadditivity: `ω(s, u) + ω(u, t) ≤ ω(s, t)` whenever `s ≤ u ≤ t` -/
  superadditive : ∀ {s u t : ℝ}, s ≤ u → u ≤ t → toFun s u + toFun u t ≤ toFun s t
  /-- Vanishes on the diagonal: `ω(s, s) = 0` -/
  zero_diag : ∀ s : ℝ, toFun s s = 0
  /-- Joint continuity on the simplex `{(s, t) | s ≤ t}` -/
  cont : ContinuousOn (fun p : ℝ × ℝ => toFun p.1 p.2) {p | p.1 ≤ p.2}

namespace Control

instance : CoeFun Control (fun _ => ℝ → ℝ → ℝ≥0) := ⟨toFun⟩

variable {ω ω' : Control}

/-- The diagonal continuity `ω(s, ·) → 0` as `· → s⁺` follows from joint continuity and
`ω(s, s) = 0`. -/
theorem diag_cont (ω : Control) (s : ℝ) : Tendsto (ω.toFun s) (𝓝[Ioi s] s) (𝓝 0) := by
  rw [← ω.zero_diag s]
  have hmem : (s, s) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} := le_refl s
  have hcont : ContinuousWithinAt (fun p : ℝ × ℝ => ω.toFun p.1 p.2) {p | p.1 ≤ p.2} (s, s) :=
    ω.cont (s, s) hmem
  -- Compose hcont with the map t ↦ (s, t), noting that Ioi s maps into {p | p.1 ≤ p.2}
  have hmap : Tendsto (fun t => (s, t)) (𝓝[Ioi s] s) (𝓝[{p : ℝ × ℝ | p.1 ≤ p.2}] (s, s)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Filter.Tendsto.prodMk_nhds tendsto_const_nhds
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    · filter_upwards [self_mem_nhdsWithin] with t ht using le_of_lt ht
  simpa using hcont.tendsto.comp hmap

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
  zero_diag s := by simp [ω.zero_diag s, hφ_zero]
  cont := hφ_cont.comp_continuousOn ω.cont

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
  zero_diag s := by
    simp only [ω.zero_diag s, ω'.zero_diag s]
    rcases hα.lt_or_eq with hα_pos | hα_zero
    · simp [NNReal.zero_rpow hα_pos.ne']
    · rcases hβ.lt_or_eq with hβ_pos | hβ_zero
      · simp [NNReal.zero_rpow hβ_pos.ne', ← hα_zero]
      · linarith [hα_zero.symm ▸ hβ_zero.symm ▸ hαβ]
  cont := by
    apply ContinuousOn.mul
    · exact (NNReal.continuous_rpow_const hα).comp_continuousOn ω.cont
    · exact (NNReal.continuous_rpow_const hβ).comp_continuousOn ω'.cont

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

/-- Restrict a partition `π₀ : Partition s t N₀` to the sub-interval
`[π₀.points i, π₀.points j]` for indices `i ≤ j`. The result has `j - i - 1` interior points. -/
private noncomputable def Partition.restrict {s t : ℝ} {N₀ : ℕ} (π₀ : Partition s t N₀)
    (i j : Fin (N₀ + 2)) (hij : i < j) :
    Partition (π₀.points i) (π₀.points j) (j.val - i.val - 1) where
  points k := π₀.points ⟨i.val + k.val, by
    have hk := k.isLt  -- k < j - i - 1 + 2 = j - i + 1 (since j > i so j - i ≥ 1)
    have hj := j.isLt  -- j < N₀ + 2
    have hij' : i.val < j.val := hij
    omega⟩
  strictMono a b hab := π₀.strictMono (by simp only [Fin.mk_lt_mk]; omega)
  head_eq := by simp
  last_eq := by
    simp only [Fin.last]
    congr 1; ext; simp only [Fin.val_mk]; omega

/-- The Riemann sum of `π₀` decomposes as a sum over sub-intervals determined by `π`.
For each consecutive pair `(tₖ, tₖ₊₁)` of `π`, the sum of `A` over those sub-interval
points of `π₀` equals the restricted Riemann sum. -/
private lemma Partition.riemannSum_eq_sum_restrict {s t : ℝ} {N₀ N : ℕ}
    (π₀ : Partition s t N₀) (π : Partition s t N) (A : ℝ → ℝ → ℝ)
    -- For each point of π, find its index in π₀
    (hidx : ∀ k : Fin (N + 2), ∃ j : Fin (N₀ + 2), π.points k = π₀.points j)
    -- The index function
    (φ : Fin (N + 2) → Fin (N₀ + 2))
    (hφ : ∀ k, π.points k = π₀.points (φ k))
    (hφ_mono : StrictMono φ) :
    π₀.riemannSum A = ∑ k : Fin (N + 1),
      (π₀.restrict (φ k.castSucc) (φ k.succ)
        (hφ_mono (Fin.castSucc_lt_succ (i := k)))).riemannSum A := by
  have hφ0 : φ 0 = 0 := by
    apply π₀.strictMono.injective; rw [← hφ 0, π.head_eq, π₀.head_eq]
  have hφlast : φ (Fin.last (N + 1)) = Fin.last (N₀ + 1) := by
    apply π₀.strictMono.injective; rw [← hφ (Fin.last (N + 1)), π.last_eq, π₀.last_eq]
  have hφ0_val : (φ 0).val = 0 := congr_arg Fin.val hφ0
  have hφlast_val : (φ (Fin.last (N + 1))).val = N₀ + 1 := by
    have := congr_arg Fin.val hφlast; simp [Fin.val_last] at this; exact this
  -- Auxiliary: a monotone ℕ-sequence decomposes range(g(n)) into consecutive Ico blocks.
  have range_decomp : ∀ (n : ℕ) (g : ℕ → ℕ) (_ : Monotone g) (_ : g 0 = 0) (f : ℕ → ℝ),
      ∑ l ∈ Finset.range (g n), f l =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.Ico (g k) (g (k + 1)), f l := by
    intro n g hg hg0 f
    induction n with
    | zero => simp [hg0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      have h0n : 0 ≤ g n := by rw [← hg0]; exact hg (Nat.zero_le _)
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive f h0n (hg (Nat.le_succ n)),
        Nat.Ico_zero_eq_range]
  -- Define the ℕ-level summand
  -- f(l) = A(π₀.points ⟨l, _⟩, π₀.points ⟨l+1, _⟩) for l < N₀+1
  -- We clamp to make it total.
  -- Apply range_decomp with g(k) = (φ ⟨k, _⟩).val extended to ℕ
  -- g(k) = (φ ⟨min k (N+1), _⟩).val, monotone since φ is monotone and min is monotone
  set g : ℕ → ℕ := fun k => (φ ⟨min k (N + 1), by omega⟩).val
  have hg_mono : Monotone g := by
    intro a b hab
    simp only [g]
    by_cases ha : a ≤ N + 1 <;> by_cases hb : b ≤ N + 1
    · simp only [Nat.min_eq_left ha, Nat.min_eq_left hb]
      rcases eq_or_lt_of_le hab with rfl | hab'
      · rfl
      · exact le_of_lt (hφ_mono (Fin.mk_lt_mk.mpr hab'))
    · simp only [Nat.min_eq_left ha, Nat.min_eq_right (by omega : N + 1 ≤ b)]
      rcases eq_or_lt_of_le (show a ≤ N + 1 from ha) with rfl | ha'
      · exact le_refl _
      · exact le_of_lt (hφ_mono (Fin.mk_lt_mk.mpr ha'))
    · omega
    · simp only [Nat.min_eq_right (by omega : N + 1 ≤ a),
        Nat.min_eq_right (by omega : N + 1 ≤ b)]
      exact le_refl _
  have hg0' : g 0 = 0 := by
    show (φ ⟨min 0 (N + 1), _⟩).val = 0
    simp [hφ0_val]
  have hgN : g (N + 1) = N₀ + 1 := by
    simp only [g, min_self]
    exact hφlast_val
  -- Key identity at ℕ level
  have key : ∀ (f : ℕ → ℝ), ∑ l ∈ Finset.range (N₀ + 1), f l =
      ∑ k ∈ Finset.range (N + 1), ∑ l ∈ Finset.Ico (g k) (g (k + 1)), f l := by
    intro f; rw [← hgN, range_decomp (N + 1) g hg_mono hg0' f]
  -- g agrees with φ on {0,...,N+1}
  have hg_eq : ∀ k : ℕ, (hk : k ≤ N + 1) → g k = (φ ⟨k, Nat.lt_of_le_of_lt hk (by omega)⟩).val := by
    intro k hk; simp [g, Nat.min_eq_left hk]
  -- Now both sides are sums that decompose the same range. We convert each side to
  -- ∑ l ∈ Finset.range (N₀+1), A(π₀[⟨l,_⟩], π₀[⟨l+1,_⟩]) using the key decomposition.
  -- LHS: π₀.riemannSum A = ∑ k : Fin (N₀+1), A(...)
  -- We prove LHS = ∑ l in range(N₀+1), and RHS = same, via key.
  -- Define the common ℕ → ℝ summand (clamped to be total)
  set F : ℕ → ℝ := fun l =>
    A (π₀.points ⟨min l (N₀ + 1), by omega⟩) (π₀.points ⟨min (l + 1) (N₀ + 1), by omega⟩)
  -- LHS = ∑ l in range(N₀+1), F l
  suffices hLHS : π₀.riemannSum A = ∑ l ∈ Finset.range (N₀ + 1), F l by
    rw [hLHS, key F]
    -- Now: ∑ k ∈ range(N+1), ∑ l ∈ Ico(g k, g(k+1)), F l
    --    = ∑ k : Fin(N+1), (restrict ...).riemannSum A
    -- Convert key LHS from range to Fin
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro ⟨k, hk⟩ _
    show ∑ l ∈ Finset.Ico (g k) (g (k + 1)), F l =
        (π₀.restrict (φ (⟨k, hk⟩ : Fin (N + 1)).castSucc) (φ (⟨k, hk⟩ : Fin (N + 1)).succ) _).riemannSum A
    rw [hg_eq k (by omega), hg_eq (k + 1) (by omega)]
    -- Now goal: ∑ l ∈ Ico(φ⟨k,_⟩.val, φ⟨k+1,_⟩.val), F l = restrict.riemannSum A
    -- where the Fin args to φ match castSucc and succ
    have hcs : (φ ⟨k, by omega⟩) = φ (⟨k, hk⟩ : Fin (N + 1)).castSucc := by congr 1
    have hsu : (φ ⟨k + 1, by omega⟩) = φ (⟨k, hk⟩ : Fin (N + 1)).succ := by congr 1
    rw [hcs, hsu]
    -- Now: ∑ l ∈ Ico(φ(k.cs).val, φ(k.s).val), F l = (restrict ...).riemannSum A
    symm; rw [Partition.riemannSum]; simp only [Partition.restrict]
    -- Goal: ∑ m : Fin(bs), A(π₀[φ(k.cs)+m.cs], π₀[φ(k.cs)+m.s]) =
    --       ∑ l ∈ Ico(φ(k.cs).val, φ(k.s).val), F l
    -- First convert the Ico sum: ∑ l ∈ Ico(a, b), F l = ∑ m ∈ Ico(0, b-a), F(a+m)
    set a := (φ (⟨k, hk⟩ : Fin (N + 1)).castSucc).val
    set b := (φ (⟨k, hk⟩ : Fin (N + 1)).succ).val
    have hab : a < b := hφ_mono (Fin.castSucc_lt_succ (i := ⟨k, hk⟩))
    have hbs : b - a - 1 + 1 = b - a := by omega
    -- Convert Ico to shifted range via sum_Ico_add
    have hab_le : a ≤ b := le_of_lt hab
    rw [show Finset.Ico a b = Finset.Ico (0 + a) (b - a + a) from by
      congr 1 <;> omega]
    rw [← Finset.sum_Ico_add F 0 (b - a) a, Nat.Ico_zero_eq_range]
    -- Now: ∑ m : Fin(b-a-1+1), body(m) = ∑ m ∈ range(b-a), F(a+m)
    -- The summand for index m is A(π₀[a + m.castSucc], π₀[a + m.succ])
    -- = A(π₀[a + m], π₀[a + m + 1]) = F(a + m) (since a+m, a+m+1 ≤ N₀+1).
    -- Use a single tactic to prove both sides equal.
    trans ∑ m : Fin (b - a - 1 + 1), F (a + m.val)
    · apply Finset.sum_congr rfl; intro ⟨m, hm⟩ _
      have hm' : m < b - a := by omega
      show A (π₀.points ⟨_, _⟩) (π₀.points ⟨_, _⟩) = F (a + m)
      simp only [F, a, Fin.val_castSucc, Fin.val_succ,
        Nat.min_eq_left (by have := (φ (⟨k, hk⟩ : Fin (N + 1)).succ).isLt; omega),
        Nat.min_eq_left (by have := (φ (⟨k, hk⟩ : Fin (N + 1)).succ).isLt; omega)]
      congr 1 <;> congr 1 <;> ext <;> simp <;> omega
    · rw [Fin.sum_univ_eq_sum_range (fun m => F (a + m)), hbs]
  -- Proof of hLHS: π₀.riemannSum A = ∑ l in range(N₀+1), F l
  simp only [Partition.riemannSum]
  -- First show the Fin sum equals the Fin sum of F ∘ val
  have : (∑ k : Fin (N₀ + 1), A (π₀.points k.castSucc) (π₀.points k.succ)) =
      ∑ k : Fin (N₀ + 1), F k.val := by
    apply Finset.sum_congr rfl; intro ⟨l, hl⟩ _
    simp only [F, Nat.min_eq_left (by omega : l ≤ N₀ + 1),
      Nat.min_eq_left (by omega : l + 1 ≤ N₀ + 1)]
    congr 1 <;> congr 1 <;> ext <;> simp [Fin.castSucc, Fin.succ]
  rw [this, Fin.sum_univ_eq_sum_range F]

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

/-! ### Uniform diagonal continuity and the mesh filter -/

/-- For a control `ω`, the function `(u, v) ↦ ω(u, v)` converges to 0 uniformly as `v - u → 0`
on any compact interval `[a, b]`. This follows from joint continuity of `ω` on the simplex
and the fact that `ω(u, u) = 0`. -/
private lemma Control.unif_diag_cont (ω : Control) {a b : ℝ} (hab : a ≤ b) :
    ∀ ε > 0, ∃ δ > 0, ∀ {u v : ℝ}, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
      (ω u v : ℝ) < ε := by
  intro ε hε
  -- K = {(u,v) | a ≤ u ≤ v ≤ b} is compact (closed subset of [a,b]²)
  set K : Set (ℝ × ℝ) := {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}
  have hK_compact : IsCompact K := by
    have : K = (Set.Icc a b) ×ˢ (Set.Icc a b) ∩ {p | p.1 ≤ p.2} := by
      ext ⟨u, v⟩; simp only [K, Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨⟨h1, by linarith⟩, ⟨by linarith, h3⟩⟩, h2⟩
      · rintro ⟨⟨⟨h1, _⟩, ⟨_, h3⟩⟩, h2⟩; exact ⟨h1, h2, h3⟩
    rw [this]
    exact ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_fst continuous_snd))
  -- f = (u,v) ↦ ω(u,v) (as ℝ) is continuous on K ⊆ {p | p.1 ≤ p.2}
  have hf_cont : ContinuousOn (fun p : ℝ × ℝ => (ω.toFun p.1 p.2 : ℝ)) K :=
    NNReal.continuous_coe.comp_continuousOn
      (ω.cont.mono (fun p ⟨_, huv, _⟩ => huv))
  -- Uniform continuity on K (Heine-Cantor)
  have huc := hK_compact.uniformContinuousOn_of_continuous hf_cont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := huc (ε / 2) (half_pos hε)
  refine ⟨min δ₀ 1 / 2, by positivity, fun {u v} hau huv hvb hvmu => ?_⟩
  have huv_K : (u, v) ∈ K := ⟨hau, huv, hvb⟩
  have huu_K : (u, u) ∈ K := ⟨hau, le_refl u, by linarith⟩
  have hdist : dist (u, v) (u, u) < δ₀ := by
    rw [Prod.dist_eq]
    simp only [Real.dist_eq]
    calc max |u - u| |v - u|
        = max 0 (v - u) := by
          rw [sub_self, abs_zero, abs_of_nonneg (by linarith)]
      _ = v - u := max_eq_right (by linarith)
      _ < min δ₀ 1 / 2 := hvmu
      _ ≤ δ₀ := by linarith [min_le_left δ₀ 1]
  have key := hδ₀ (u, v) huv_K (u, u) huu_K hdist
  simp only [Real.dist_eq] at key
  have h0 : (ω.toFun u u : ℝ) = 0 := by exact_mod_cast ω.zero_diag u
  rw [h0, sub_zero, abs_of_nonneg (by positivity)] at key
  linarith [half_lt_self hε]

/-- **Key bound**: for a partition `π₀` that refines `π` (i.e., has `π`'s points as a subset),
the Riemann sums satisfy
`|Σ_{π₀} A - Σ_π A| ≤ 2^θ * ζ(θ) * ω_max(π)^(θ-1) * ω(s, t)`
where `ω_max(π) = ⨆_k ω(t_k, t_{k+1})`.

Proof sketch: decompose `Σ_{π₀} A = Σ_k Σ_{π₀|[tₖ,tₖ₊₁]} A` and apply `maximalInequality`
to each sub-interval `[tₖ, tₖ₊₁]`. The error on `[tₖ,tₖ₊₁]` is `≤ C * ω(tₖ,tₖ₊₁)^θ`.
Summing and using `ω(tₖ,tₖ₊₁)^θ ≤ ω_max^{θ-1} * ω(tₖ,tₖ₊₁)` and superadditivity gives
`Σ_k ω(tₖ,tₖ₊₁) ≤ ω(s,t)`. -/
private lemma riemannSum_refine_bound {A : ℝ → ℝ → ℝ} {ω : Control} {θ : ℝ} (hθ : 1 < θ)
    (hA : ∀ {s u t : ℝ}, s ≤ u → u ≤ t → |defect A s u t| ≤ (ω s t : ℝ) ^ θ)
    {s t : ℝ} (hst : s ≤ t) {N₀ N : ℕ}
    (π₀ : Partition s t N₀) (π : Partition s t N)
    (hrefine : ∀ k : Fin (N + 2), ∃ j : Fin (N₀ + 2), π.points k = π₀.points j) :
    |π₀.riemannSum A - π.riemannSum A| ≤
      (2 : ℝ) ^ θ * (∑' n : ℕ+, (n : ℝ) ^ (-θ)) *
      (⨆ k : Fin (N + 1), (ω (π.points k.castSucc) (π.points k.succ) : ℝ)) ^ (θ - 1) *
      (ω s t : ℝ) := by
  -- Step 0: Extract a strictly monotone refinement map φ
  set φ : Fin (N + 2) → Fin (N₀ + 2) := fun k => Classical.choose (hrefine k)
  have hφ : ∀ k, π.points k = π₀.points (φ k) :=
    fun k => Classical.choose_spec (hrefine k)
  have hφ_mono : StrictMono φ := by
    intro a b hab
    by_contra h
    push_neg at h
    rcases h.eq_or_lt with heq | hlt
    · have heq' : π₀.points (φ b) = π₀.points (φ a) := congr_arg π₀.points heq
      rw [← hφ a, ← hφ b] at heq'
      exact absurd (π.strictMono hab) (not_lt.mpr heq'.le)
    · have h1 := π.strictMono hab
      rw [hφ a, hφ b] at h1
      exact absurd h1 (not_lt.mpr (le_of_lt (π₀.strictMono hlt)))
  -- Step 1: Decompose π₀.riemannSum A using the restriction
  have hdecomp := Partition.riemannSum_eq_sum_restrict π₀ π A hrefine φ hφ hφ_mono
  -- Step 2: Write the difference as a sum of local differences
  have hdiff : π₀.riemannSum A - π.riemannSum A =
      ∑ k : Fin (N + 1), ((π₀.restrict (φ k.castSucc) (φ k.succ)
        (hφ_mono (Fin.castSucc_lt_succ (i := k)))).riemannSum A -
        A (π.points k.castSucc) (π.points k.succ)) := by
    rw [hdecomp, Partition.riemannSum, ← Finset.sum_sub_distrib]
  -- Step 3: Triangle inequality on the sum
  have habs_sum : |π₀.riemannSum A - π.riemannSum A| ≤
      ∑ k : Fin (N + 1), |(π₀.restrict (φ k.castSucc) (φ k.succ)
        (hφ_mono (Fin.castSucc_lt_succ (i := k)))).riemannSum A -
        A (π.points k.castSucc) (π.points k.succ)| := by
    rw [hdiff]; exact Finset.abs_sum_le_sum_abs _ _
  -- Step 4: Apply maximalInequality to each sub-interval
  set C := (2 : ℝ) ^ θ * (∑' n : ℕ+, (n : ℝ) ^ (-θ))
  -- Summability and positivity of the zeta sum
  have hsumm_nat : Summable (fun n : ℕ => (n : ℝ) ^ (-θ)) :=
    Real.summable_nat_rpow.2 (by linarith)
  have hsumm_shift : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-θ)) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-θ)) 1).mpr hsumm_nat
    exact this.congr (fun n => by push_cast; ring)
  have hreidx : ∑' n : ℕ+, (n : ℝ) ^ (-θ) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-θ) :=
    (tsum_pnat_eq_tsum_succ (f := fun n => (n : ℝ) ^ (-θ))).trans
      (tsum_congr (fun n => by push_cast; ring_nf))
  have hzeta_pos : 0 < ∑' n : ℕ+, (n : ℝ) ^ (-θ) := by
    rw [hreidx]
    have h1 : (0 : ℝ) < ((0 : ℝ) + 1) ^ (-θ) := by positivity
    calc (0 : ℝ) < ((0 : ℝ) + 1) ^ (-θ) := by positivity
      _ = ∑ n ∈ ({0} : Finset ℕ), ((n : ℝ) + 1) ^ (-θ) := by simp
      _ ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-θ) :=
          hsumm_shift.sum_le_tsum _ (fun n _ => by positivity)
  have hC_pos : 0 < C := mul_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) θ) hzeta_pos
  -- Step 4 continued: apply maximalInequality to each sub-interval
  -- The restricted partition lives on [π₀.points (φ k.cs), π₀.points (φ k.s)]
  -- and maximalInequality gives the bound with ω on that interval.
  -- We need: the restrict endpoints match π's endpoints (via hφ).
  have hlocal : ∀ k : Fin (N + 1),
      |(π₀.restrict (φ k.castSucc) (φ k.succ)
        (hφ_mono (Fin.castSucc_lt_succ (i := k)))).riemannSum A -
        A (π₀.points (φ k.castSucc)) (π₀.points (φ k.succ))| ≤
      C * (ω (π₀.points (φ k.castSucc)) (π₀.points (φ k.succ)) : ℝ) ^ θ := by
    intro k
    have hk_le : π₀.points (φ k.castSucc) ≤ π₀.points (φ k.succ) :=
      le_of_lt (π₀.strictMono (hφ_mono (Fin.castSucc_lt_succ (i := k))))
    exact maximalInequality ω hθ hA hk_le _
  -- Rewrite in terms of π's points
  have hlocal' : ∀ k : Fin (N + 1),
      |(π₀.restrict (φ k.castSucc) (φ k.succ)
        (hφ_mono (Fin.castSucc_lt_succ (i := k)))).riemannSum A -
        A (π.points k.castSucc) (π.points k.succ)| ≤
      C * (ω (π.points k.castSucc) (π.points k.succ) : ℝ) ^ θ := by
    intro k
    simp only [show ∀ j, π₀.points (φ j) = π.points j from fun j => (hφ j).symm] at hlocal
    exact hlocal k
  -- Step 5: Combine: |...| ≤ C * ∑ k, ω(tₖ, tₖ₊₁)^θ
  have hsum_bound : |π₀.riemannSum A - π.riemannSum A| ≤
      C * ∑ k : Fin (N + 1), (ω (π.points k.castSucc) (π.points k.succ) : ℝ) ^ θ :=
    (habs_sum.trans (Finset.sum_le_sum (fun k _ => hlocal' k))).trans
      (by rw [← Finset.mul_sum])
  -- Step 6: Factor ω(tₖ, tₖ₊₁)^θ ≤ ω_max^(θ-1) * ω(tₖ, tₖ₊₁)
  set ω_max := ⨆ k : Fin (N + 1), (ω (π.points k.castSucc) (π.points k.succ) : ℝ)
  have hbdd : BddAbove (Set.range (fun k : Fin (N + 1) =>
      (ω (π.points k.castSucc) (π.points k.succ) : ℝ))) := by
    refine ⟨(ω s t : ℝ), fun x ⟨k, hk⟩ => hk ▸ ?_⟩
    have hle1 : π.points k.castSucc ≤ π.points k.succ :=
      le_of_lt (π.strictMono (Fin.castSucc_lt_succ (i := k)))
    have hs_le : s ≤ π.points k.castSucc := by
      have := π.strictMono.monotone (Fin.zero_le k.castSucc); rwa [π.head_eq] at this
    have hle_t : π.points k.succ ≤ t := by
      have := π.strictMono.monotone (Fin.le_last k.succ); rwa [π.last_eq] at this
    have hcs_le_t : π.points k.castSucc ≤ t := hle1.trans hle_t
    exact_mod_cast (ω.mono_right hle1 hle_t).trans (ω.mono_left hs_le hcs_le_t)
  have hω_max_nn : 0 ≤ ω_max := Real.iSup_nonneg (fun k => by positivity)
  have hω_le_max : ∀ k : Fin (N + 1),
      (ω (π.points k.castSucc) (π.points k.succ) : ℝ) ≤ ω_max :=
    fun k => le_ciSup hbdd k
  have hfactor : ∀ k : Fin (N + 1),
      (ω (π.points k.castSucc) (π.points k.succ) : ℝ) ^ θ ≤
      ω_max ^ (θ - 1) * (ω (π.points k.castSucc) (π.points k.succ) : ℝ) := by
    intro k
    set ωk := (ω (π.points k.castSucc) (π.points k.succ) : ℝ)
    have hωk_nn : 0 ≤ ωk := by positivity
    by_cases hωk_zero : ωk = 0
    · simp [hωk_zero, Real.zero_rpow (by linarith : θ ≠ 0)]
    · have hωk_pos : 0 < ωk := lt_of_le_of_ne hωk_nn (Ne.symm hωk_zero)
      calc ωk ^ θ = ωk ^ ((θ - 1) + 1) := by ring_nf
          _ = ωk ^ (θ - 1) * ωk ^ (1 : ℝ) := Real.rpow_add hωk_pos (θ - 1) 1
          _ = ωk ^ (θ - 1) * ωk := by rw [Real.rpow_one]
          _ ≤ ω_max ^ (θ - 1) * ωk := by
                apply mul_le_mul_of_nonneg_right _ hωk_nn
                exact Real.rpow_le_rpow hωk_nn (hω_le_max k) (by linarith)
  -- Step 7: Sum ω_k ≤ ω(s, t) by superadditivity
  have hsum_omega : ∑ k : Fin (N + 1),
      (ω (π.points k.castSucc) (π.points k.succ) : ℝ) ≤ (ω s t : ℝ) := by
    -- Use sum_control_le with a clamped extension of π.points to ℕ
    set a : ℕ → ℝ := fun i => π.points ⟨min i (N + 1), by omega⟩
    have ha : Monotone a := by
      intro i j hij; simp only [a]
      rcases (min_le_min_right (N + 1) hij).eq_or_lt with h | h
      · simp [h]
      · exact le_of_lt (π.strictMono h)
    have key := @sum_control_le ω (N + 1) a ha
    have ha0 : a 0 = s := by simp [a, π.head_eq]
    have haN1 : a (N + 1) = t := by simp only [a, Nat.min_self]; exact π.last_eq
    -- Rewrite key: ∑ k : Fin(N+1), ω(a k, a(k+1)) ≤ ω(a 0, a(N+1)) = ω s t
    have hkey : ∑ k : Fin (N + 1), ω (a ↑k) (a (↑k + 1)) ≤ ω s t := by
      calc ∑ k : Fin (N + 1), ω (a ↑k) (a (↑k + 1))
          ≤ ω (a 0) (a (N + 1)) := by
            calc _ ≤ ω (a 0) (a (N + 1 : ℕ)) := by exact_mod_cast key
              _ = ω (a 0) (a (N + 1)) := rfl
        _ = ω s t := by rw [ha0, haN1]
    -- Now show each summand matches
    have hrw : ∀ k : Fin (N + 1), ω (a ↑k) (a (↑k + 1)) =
        ω (π.points k.castSucc) (π.points k.succ) := by
      intro ⟨k, hk⟩; simp only [a, Fin.val_mk,
        min_eq_left (show k ≤ N + 1 by omega),
        min_eq_left (show k + 1 ≤ N + 1 by omega)]
      congr 1 <;> congr 1 <;> ext <;> simp [Fin.castSucc, Fin.succ]
    calc (∑ k : Fin (N + 1), (ω (π.points k.castSucc) (π.points k.succ) : ℝ))
        = ↑(∑ k : Fin (N + 1), ω (π.points k.castSucc) (π.points k.succ)) := by push_cast; rfl
      _ = ↑(∑ k : Fin (N + 1), ω (a ↑k) (a (↑k + 1))) := by
            congr 1; exact (Finset.sum_congr rfl (fun k _ => (hrw k).symm))
      _ ≤ (ω s t : ℝ) := by exact_mod_cast hkey
  -- Step 8: Combine everything
  calc |π₀.riemannSum A - π.riemannSum A|
      ≤ C * ∑ k : Fin (N + 1), (ω (π.points k.castSucc) (π.points k.succ) : ℝ) ^ θ :=
        hsum_bound
    _ ≤ C * ∑ k : Fin (N + 1),
        (ω_max ^ (θ - 1) * (ω (π.points k.castSucc) (π.points k.succ) : ℝ)) := by
        gcongr with k _; exact hfactor k
    _ = C * ω_max ^ (θ - 1) *
        ∑ k : Fin (N + 1), (ω (π.points k.castSucc) (π.points k.succ) : ℝ) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ C * ω_max ^ (θ - 1) * (ω s t : ℝ) := by
        apply mul_le_mul_of_nonneg_left hsum_omega
        exact mul_nonneg hC_pos.le (Real.rpow_nonneg hω_max_nn _)

/-- The `ω_max` of a partition goes to 0 as the mesh goes to 0, by uniform diagonal continuity. -/
private lemma omega_max_tendsto_zero {ω : Control} {s t : ℝ} (hst : s ≤ t) {N : ℕ}
    {f : ℕ → Partition s t N} (hmesh : Filter.Tendsto (fun n => (f n).mesh) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ⨆ k : Fin (N + 1),
      (ω ((f n).points k.castSucc) ((f n).points k.succ) : ℝ))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := ω.unif_diag_cont hst ε hε
  rw [Metric.tendsto_atTop] at hmesh
  obtain ⟨M, hM⟩ := hmesh δ hδ_pos
  refine ⟨M, fun n hn => ?_⟩
  have hmesh_n : (f n).mesh < δ := by
    have h := hM n hn
    simp only [Real.dist_eq, sub_zero] at h
    exact lt_of_abs_lt h
  -- Show iSup ≤ ε by bounding each term
  rw [Real.dist_eq, sub_zero]
  -- Helper: each partition point is in [s, t]
  have hpts_s : ∀ j : Fin (N + 2), s ≤ (f n).points j := fun j => by
    have := (f n).strictMono.monotone (Fin.zero_le j)
    simp only [(f n).head_eq] at this; exact this
  have hpts_t : ∀ j : Fin (N + 2), (f n).points j ≤ t := fun j => by
    have := (f n).strictMono.monotone (Fin.le_last j)
    simp only [(f n).last_eq] at this; exact this
  have hbdd : BddAbove (Set.range (fun k : Fin (N + 1) =>
      (ω ((f n).points k.castSucc) ((f n).points k.succ) : ℝ))) := by
    refine ⟨(ω s t : ℝ), fun x ⟨k, hk⟩ => hk ▸ ?_⟩
    have hkle : (f n).points k.castSucc ≤ (f n).points k.succ :=
      le_of_lt ((f n).strictMono Fin.castSucc_lt_succ)
    have h1 := ω.mono_left (hpts_s k.castSucc) (hpts_t k.castSucc)
    have h2 := ω.mono_right hkle (hpts_t k.succ)
    exact_mod_cast h2.trans h1
  -- The mesh of the partition bounds each sub-interval length
  have hmesh_bdd : BddAbove (Set.range (fun k : Fin (N + 1) =>
      (f n).points k.succ - (f n).points k.castSucc)) := by
    refine ⟨t - s, fun x hx => ?_⟩
    obtain ⟨j, rfl⟩ := hx
    simp only
    linarith [hpts_s j.castSucc, hpts_t j.succ,
      le_of_lt ((f n).strictMono (Fin.castSucc_lt_succ (i := j)))]
  have hle_mesh : ∀ k : Fin (N + 1),
      (f n).points k.succ - (f n).points k.castSucc ≤ (f n).mesh := fun k =>
    le_ciSup hmesh_bdd k
  have hnn : 0 ≤ ⨆ k : Fin (N + 1), (ω ((f n).points k.castSucc) ((f n).points k.succ) : ℝ) :=
    Real.iSup_nonneg (fun k => by positivity)
  rw [abs_of_nonneg hnn]
  have hlt : ∀ k : Fin (N + 1),
      (ω ((f n).points k.castSucc) ((f n).points k.succ) : ℝ) < ε := fun k =>
    hδ (hpts_s k.castSucc)
      (le_of_lt ((f n).strictMono (Fin.castSucc_lt_succ (i := k))))
      (hpts_t k.succ)
      (lt_of_le_of_lt (hle_mesh k) hmesh_n)
  -- iSup of a finite type with all values < ε is < ε
  rw [← sSup_range]
  rw [Set.Finite.csSup_lt_iff (Set.finite_range _) (Set.range_nonempty _)]
  rintro _ ⟨k, rfl⟩
  exact hlt k

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
  -- The proof constructs I as the Cauchy limit of Riemann sums.
  -- Key sorry'd ingredients: exists_partition, common_refine.
  -- The Cauchy property follows from riemannSum_refine_bound + common refinement.
  -- The limit exists by completeness of ℝ.
  -- The maximal inequality follows by passing maximalInequality to the limit.
  -- Additivity of the sewing value follows from concatenation of partitions + uniqueness.
  set C := (2 : ℝ) ^ θ * (∑' n : ℕ+, (n : ℝ) ^ (-θ)) with hC_def
  have hzeta_pos : 0 < ∑' n : ℕ+, (n : ℝ) ^ (-θ) := by
    have hsumm : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-θ)) := by
      have := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-θ)) 1).mpr
        (Real.summable_nat_rpow.2 (by linarith))
      exact this.congr (fun n => by push_cast; ring)
    have hreidx : ∑' n : ℕ+, (n : ℝ) ^ (-θ) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-θ) :=
      (tsum_pnat_eq_tsum_succ (f := fun n => (n : ℝ) ^ (-θ))).trans
        (tsum_congr (fun n => by push_cast; ring_nf))
    rw [hreidx]
    calc (0 : ℝ) < ((0 : ℝ) + 1) ^ (-θ) := by positivity
      _ = ∑ n ∈ ({0} : Finset ℕ), ((n : ℝ) + 1) ^ (-θ) := by simp
      _ ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-θ) :=
          hsumm.sum_le_tsum _ (fun n _ => by positivity)
  have hC_pos : 0 < C :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) θ) hzeta_pos
  -- === Sorry'd combinatorial helpers ===
  have exists_partition : ∀ {s t : ℝ} (_ : s < t) (δ : ℝ) (_ : 0 < δ),
      ∃ (N : ℕ) (π : Partition s t N), π.mesh < δ := by
    intro s t hst δ hδ
    -- Use N+1 equal subintervals where N = ⌈(t-s)/δ⌉ - 1
    set n := Nat.ceil ((t - s) / δ) + 1 with hn_def
    have hts_pos : 0 < t - s := sub_pos.mpr hst
    have hn_pos : 0 < n := by omega
    -- Build uniform partition with n+1 subintervals (n interior points)
    -- Actually use n subintervals (n-1 interior points), so N = n - 1
    set N := n - 1
    have hn_eq : n = N + 1 := Nat.succ_pred_eq_of_pos hn_pos
    -- Points: s + k * (t-s)/n for k = 0, ..., n = N+1
    refine ⟨N, ⟨fun k => s + k.val * ((t - s) / n), ?_, ?_, ?_⟩, ?_⟩
    · -- strictMono
      intro a b hab
      have hab' : (a.val : ℝ) < b.val := by exact_mod_cast hab
      have hstep : 0 < (t - s) / (n : ℝ) := div_pos hts_pos (Nat.cast_pos.mpr hn_pos)
      linarith [mul_lt_mul_of_pos_right hab' hstep]
    · -- head_eq
      simp
    · -- last_eq
      simp only [Fin.val_last]
      have hn_cast : N + 1 = n := by omega
      have : ((N + 1 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hn_cast
      rw [this]; field_simp; ring
    · -- mesh < δ
      -- Each subinterval has length (t-s)/n
      have hstep : 0 < (t - s) / (n : ℝ) := div_pos hts_pos (Nat.cast_pos.mpr hn_pos)
      have hmesh_eq : ∀ k : Fin (N + 1),
          (s + (k.succ).val * ((t - s) / (n : ℝ))) -
          (s + (k.castSucc).val * ((t - s) / (n : ℝ))) = (t - s) / n := by
        intro k
        have : (k.succ).val = (k.castSucc).val + 1 := by
          simp [Fin.val_succ, Fin.val_castSucc]
        push_cast [this]; ring
      have hall_eq : ∀ k : Fin (N + 1),
          (s + (k.succ).val * ((t - s) / (n : ℝ))) -
          (s + (k.castSucc).val * ((t - s) / (n : ℝ))) = (t - s) / n := hmesh_eq
      have hiSup : (⨆ k : Fin (N + 1),
          ((s + (k.succ).val * ((t - s) / (n : ℝ))) -
           (s + (k.castSucc).val * ((t - s) / (n : ℝ))))) = (t - s) / n := by
        have : (fun k : Fin (N + 1) =>
          (s + (k.succ).val * ((t - s) / (n : ℝ))) -
          (s + (k.castSucc).val * ((t - s) / (n : ℝ)))) = fun _ => (t - s) / n :=
          funext hall_eq
        rw [this, ciSup_const]
      rw [Partition.mesh, hiSup]
      have hn_cast : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      rw [div_lt_iff₀ hn_cast]
      have hle : (t - s) / δ < n := by
        have h1 := Nat.le_ceil ((t - s) / δ)
        have h3 : (⌈(t - s) / δ⌉₊ : ℝ) < (n : ℝ) := by
          exact_mod_cast show ⌈(t - s) / δ⌉₊ < n by omega
        linarith
      have := (div_lt_iff₀ hδ).mp hle
      linarith
  have common_refine : ∀ {s t : ℝ} (_ : s ≤ t) {N₁ N₂ : ℕ}
      (π₁ : Partition s t N₁) (π₂ : Partition s t N₂),
      ∃ (N₀ : ℕ) (π₀ : Partition s t N₀),
        (∀ k : Fin (N₁ + 2), ∃ j : Fin (N₀ + 2), π₁.points k = π₀.points j) ∧
        (∀ k : Fin (N₂ + 2), ∃ j : Fin (N₀ + 2), π₂.points k = π₀.points j) := by
    intro s t _hst N₁ N₂ π₁ π₂
    -- Collect all points into a Finset
    set S : Finset ℝ := (Finset.univ.image π₁.points) ∪ (Finset.univ.image π₂.points)
    -- S has at least 2 elements
    have hcard_ge2 : 2 ≤ S.card := by
      have hne : π₁.points 0 ≠ π₁.points (Fin.last (N₁ + 1)) :=
        ne_of_lt (π₁.strictMono (by simp [Fin.lt_def, Fin.val_last]))
      calc 2 = ({π₁.points 0, π₁.points (Fin.last (N₁ + 1))} : Finset ℝ).card := by
              rw [Finset.card_pair hne]
        _ ≤ S.card := Finset.card_le_card (fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
            · exact Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨Fin.last _, Finset.mem_univ _,
                  Finset.mem_singleton.mp hx ▸ rfl⟩))
    set N₀ := S.card - 2
    have hcard_eq : S.card = N₀ + 2 := by omega
    set f := S.orderEmbOfFin hcard_eq
    have hf_smono : StrictMono f := f.strictMono
    have hs_mem : s ∈ S :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, π₁.head_eq⟩)
    have ht_mem : t ∈ S :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Fin.last _, Finset.mem_univ _, π₁.last_eq⟩)
    -- Helper: every element of S is ≥ s and ≤ t
    have hS_bounds : ∀ x ∈ S, s ≤ x ∧ x ≤ t := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
        constructor
        · have := π₁.strictMono.monotone (Fin.zero_le k); rw [π₁.head_eq] at this
          linarith
        · have := π₁.strictMono.monotone (Fin.le_last k); rw [π₁.last_eq] at this
          linarith
      · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
        constructor
        · have := π₂.strictMono.monotone (Fin.zero_le k); rw [π₂.head_eq] at this
          linarith
        · have := π₂.strictMono.monotone (Fin.le_last k); rw [π₂.last_eq] at this
          linarith
    -- f maps into S
    have hf_val : ∀ i, f i ∈ S := fun i => Finset.orderEmbOfFin_mem S hcard_eq i
    -- f(index of x) = x for x ∈ S
    have hf_surj : ∀ x ∈ S, ∃ i, f i = x := by
      intro x hx
      exact ⟨(S.orderIsoOfFin hcard_eq).symm ⟨x, hx⟩, by
        simp [f, Finset.orderEmbOfFin, Finset.coe_orderIsoOfFin_apply,
          OrderIso.apply_symm_apply]⟩
    have hf0 : f 0 = s := by
      apply le_antisymm
      · obtain ⟨i, hi⟩ := hf_surj s hs_mem
        calc f 0 ≤ f i := hf_smono.monotone (Fin.zero_le i)
          _ = s := hi
      · exact (hS_bounds _ (hf_val 0)).1
    have hflast : f (Fin.last (N₀ + 1)) = t := by
      apply le_antisymm
      · exact (hS_bounds _ (hf_val (Fin.last (N₀ + 1)))).2
      · obtain ⟨i, hi⟩ := hf_surj t ht_mem
        calc t = f i := hi.symm
          _ ≤ f (Fin.last (N₀ + 1)) := hf_smono.monotone (Fin.le_last i)
    refine ⟨N₀, ⟨f, hf_smono, hf0, hflast⟩, ?_, ?_⟩
    · intro k
      have hk_mem : π₁.points k ∈ S :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
      exact ⟨(S.orderIsoOfFin hcard_eq).symm ⟨π₁.points k, hk_mem⟩, by
        simp [f, Finset.orderEmbOfFin, Finset.coe_orderIsoOfFin_apply,
          OrderIso.apply_symm_apply]⟩
    · intro k
      have hk_mem : π₂.points k ∈ S :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
      exact ⟨(S.orderIsoOfFin hcard_eq).symm ⟨π₂.points k, hk_mem⟩, by
        simp [f, Finset.orderEmbOfFin, Finset.coe_orderIsoOfFin_apply,
          OrderIso.apply_symm_apply]⟩
  -- === Cauchy property ===
  have cauchy : ∀ {s t : ℝ} (hst : s ≤ t), ∀ ε > 0, ∃ δ > 0,
      ∀ {N₁ N₂ : ℕ} (π₁ : Partition s t N₁) (π₂ : Partition s t N₂),
      π₁.mesh < δ → π₂.mesh < δ →
      |π₁.riemannSum A - π₂.riemannSum A| < ε := by
    intro s t hst ε hε
    by_cases hω_zero : (ω s t : ℝ) = 0
    · refine ⟨1, one_pos, fun {N₁ N₂} π₁ π₂ _ _ => ?_⟩
      have h1 : |π₁.riemannSum A - A s t| ≤ 0 :=
        (maximalInequality ω hθ hA hst π₁).trans
          (by rw [hω_zero, Real.zero_rpow (by linarith : θ ≠ 0), mul_zero])
      have h2 : |π₂.riemannSum A - A s t| ≤ 0 :=
        (maximalInequality ω hθ hA hst π₂).trans
          (by rw [hω_zero, Real.zero_rpow (by linarith : θ ≠ 0), mul_zero])
      have h1' : π₁.riemannSum A = A s t := by
        have h1nn := abs_nonneg (π₁.riemannSum A - A s t)
        have h1z : |π₁.riemannSum A - A s t| = 0 := le_antisymm h1 h1nn
        linarith [abs_eq_zero.mp h1z]
      have h2' : π₂.riemannSum A = A s t := by
        have h2nn := abs_nonneg (π₂.riemannSum A - A s t)
        have h2z : |π₂.riemannSum A - A s t| = 0 := le_antisymm h2 h2nn
        linarith [abs_eq_zero.mp h2z]
      rw [h1', h2', sub_self, abs_zero]; exact hε
    · have hω_pos : 0 < (ω s t : ℝ) := by
        cases (NNReal.coe_nonneg (ω s t)).lt_or_eq with
        | inl h => exact h
        | inr h => exact absurd h.symm hω_zero
      set target := ε / (2 * C * (ω s t : ℝ))
      have htarget_pos : 0 < target := div_pos hε (by positivity)
      have hθ1_pos : 0 < θ - 1 := by linarith
      set ε₀ := target ^ (1 / (θ - 1)) / 2
      have hε₀_pos : 0 < ε₀ := by positivity
      obtain ⟨δ, hδ_pos, hδ⟩ := ω.unif_diag_cont hst ε₀ hε₀_pos
      refine ⟨δ, hδ_pos, fun {N₁ N₂} π₁ π₂ hmesh₁ hmesh₂ => ?_⟩
      obtain ⟨N₀, π₀, href₁, href₂⟩ := common_refine hst π₁ π₂
      have hb₁ := riemannSum_refine_bound hθ hA hst π₀ π₁ href₁
      have hb₂ := riemannSum_refine_bound hθ hA hst π₀ π₂ href₂
      have hωmax_bound : ∀ {N : ℕ} (π : Partition s t N), π.mesh < δ →
          ⨆ k : Fin (N + 1),
            (ω (π.points k.castSucc) (π.points k.succ) : ℝ) < ε₀ := by
        intro N π hmesh
        rw [← sSup_range,
          Set.Finite.csSup_lt_iff (Set.finite_range _) (Set.range_nonempty _)]
        rintro _ ⟨k, rfl⟩
        have hpts_s : s ≤ π.points k.castSucc := by
          have := π.strictMono.monotone (Fin.zero_le k.castSucc); rwa [π.head_eq] at this
        have hpts_t : π.points k.succ ≤ t := by
          have := π.strictMono.monotone (Fin.le_last k.succ); rwa [π.last_eq] at this
        have hle : π.points k.castSucc ≤ π.points k.succ :=
          le_of_lt (π.strictMono Fin.castSucc_lt_succ)
        have hmesh_bdd : BddAbove (Set.range (fun j : Fin (N + 1) =>
            π.points j.succ - π.points j.castSucc)) :=
          ⟨t - s, fun x ⟨j, hj⟩ => hj ▸ by
            linarith [π.strictMono.monotone (Fin.zero_le j.castSucc),
              π.strictMono.monotone (Fin.le_last j.succ), π.head_eq, π.last_eq]⟩
        exact hδ hpts_s hle hpts_t (lt_of_le_of_lt (le_ciSup hmesh_bdd k) hmesh)
      set ωm₁ := ⨆ k : Fin (N₁ + 1),
        (ω (π₁.points k.castSucc) (π₁.points k.succ) : ℝ)
      set ωm₂ := ⨆ k : Fin (N₂ + 1),
        (ω (π₂.points k.castSucc) (π₂.points k.succ) : ℝ)
      have bound_each : ∀ (x : ℝ), 0 ≤ x → x < ε₀ →
          C * x ^ (θ - 1) * (ω s t : ℝ) < ε / 2 := by
        intro x hx hxε₀
        have hε₀_nn : (0 : ℝ) ≤ ε₀ := hε₀_pos.le
        have htarget_nn : (0 : ℝ) ≤ target := htarget_pos.le
        -- x < ε₀ and x ^ (θ-1) is monotone (θ-1 > 0), so x^(θ-1) < ε₀^(θ-1)
        have step1 : x ^ (θ - 1) < ε₀ ^ (θ - 1) :=
          Real.rpow_lt_rpow hx hxε₀ hθ1_pos
        -- ε₀ = target^(1/(θ-1)) / 2 ≤ target^(1/(θ-1))
        have step2 : ε₀ ≤ target ^ (1 / (θ - 1)) :=
          div_le_self (Real.rpow_nonneg htarget_nn _) (by norm_num)
        -- ε₀^(θ-1) ≤ target^(1/(θ-1))^(θ-1) = target
        have step3 : ε₀ ^ (θ - 1) ≤ target := by
          calc ε₀ ^ (θ - 1) ≤ (target ^ (1 / (θ - 1))) ^ (θ - 1) :=
                Real.rpow_le_rpow hε₀_nn step2 (by linarith)
            _ = target := by
                rw [← Real.rpow_mul htarget_nn,
                  show (1 / (θ - 1) : ℝ) * (θ - 1) = 1 from by field_simp,
                  Real.rpow_one]
        calc C * x ^ (θ - 1) * (ω s t : ℝ)
            < C * ε₀ ^ (θ - 1) * (ω s t : ℝ) := by
              apply mul_lt_mul_of_pos_right
              · exact mul_lt_mul_of_pos_left step1 hC_pos
              · exact hω_pos
          _ ≤ C * target * (ω s t : ℝ) := by
              apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left step3 hC_pos.le
              · exact hω_pos.le
          _ = ε / 2 := by simp only [target]; field_simp
      calc |π₁.riemannSum A - π₂.riemannSum A|
          = |(π₁.riemannSum A - π₀.riemannSum A) +
            (π₀.riemannSum A - π₂.riemannSum A)| := by ring_nf
        _ ≤ |π₁.riemannSum A - π₀.riemannSum A| +
            |π₀.riemannSum A - π₂.riemannSum A| := abs_add_le _ _
        _ = |π₀.riemannSum A - π₁.riemannSum A| +
            |π₀.riemannSum A - π₂.riemannSum A| := by rw [abs_sub_comm]
        _ ≤ C * ωm₁ ^ (θ - 1) * (ω s t : ℝ) +
            C * ωm₂ ^ (θ - 1) * (ω s t : ℝ) := add_le_add hb₁ hb₂
        _ < ε / 2 + ε / 2 := add_lt_add
            (bound_each ωm₁ (Real.iSup_nonneg (fun k => by positivity))
              (hωmax_bound π₁ hmesh₁))
            (bound_each ωm₂ (Real.iSup_nonneg (fun k => by positivity))
              (hωmax_bound π₂ hmesh₂))
        _ = ε := by ring
  -- === Limit existence ===
  have limit_exists : ∀ {s t : ℝ} (hst : s ≤ t),
      ∃ L : ℝ, (|L - A s t| ≤ C * (ω s t : ℝ) ^ θ) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ {N : ℕ} (π : Partition s t N), π.mesh < δ →
        |π.riemannSum A - L| < ε) := by
    intro s t hst
    rcases eq_or_lt_of_le hst with rfl | hst'
    · -- s = t: trivial partition, L = A s s
      refine ⟨A s s, ?_, ?_⟩
      · simp [ω.zero_diag, Real.zero_rpow (by linarith : θ ≠ 0)]
      · intro ε hε; refine ⟨1, one_pos, fun {N} π _ => ?_⟩
        -- Any partition with s = t must have all points equal to s
        have hall : ∀ k, π.points k = s := by
          intro k
          have h1 := π.strictMono.monotone (Fin.zero_le k)
          have h2 := π.strictMono.monotone (Fin.le_last k)
          rw [π.head_eq] at h1; rw [π.last_eq] at h2; linarith
        have hrS : π.riemannSum A = ∑ _k : Fin (N + 1), A s s := by
          simp only [Partition.riemannSum]; congr 1; ext k
          rw [hall k.castSucc, hall k.succ]
        -- When s = t and N ≥ 1, all points are s, so riemannSum = (N+1) * A(s,s)
        -- But wait, we need riemannSum = A(s,s) in general... Actually no.
        -- For N = 0, riemannSum = A(s,s). For N > 0, riemannSum = (N+1)*A(s,s).
        -- Hmm, this is a problem. Let me reconsider.
        -- Actually the partition requires strictly monotone points, but s = t.
        -- So Partition s s N requires N + 2 strictly increasing points between s and s,
        -- which is only possible when N + 2 ≤ 1, i.e., N = 0 (actually N + 2 ≥ 2 always).
        -- Wait, we need strict monotonicity of N + 2 points all between s and s.
        -- That's impossible for N + 2 ≥ 2 unless... it is only possible for N + 2 = ... no.
        -- Actually `Partition s s N` with `s = t` and `N ≥ 0` would require `N + 2` strictly
        -- increasing reals all between `s` and `s`, which is impossible when `N + 2 ≥ 2`.
        -- But `N + 2 ≥ 2` always. So there is no `Partition s s N` for any `N`.
        -- The hypothesis `π : Partition s s N` is vacuously satisfiable only if `N + 2 < 2`, impossible.
        -- So the conclusion holds vacuously... Actually no. `Partition s s 0` requires 2 strictly
        -- increasing points, head = s, last = s. StrictMono on Fin 2 means points 0 < points 1,
        -- but both = s. Contradiction. So `Partition s s N` is empty for all N.
        exact absurd (π.strictMono (show (0 : Fin (N + 2)) < Fin.last (N + 1) from by
          simp [Fin.lt_iff_val_lt_val, Fin.val_last])) (by rw [π.head_eq, π.last_eq]; exact lt_irrefl s)
    · -- s < t: use Cauchy property to get a limit
      -- Build a sequence of partitions with mesh → 0
      have hseq : ∀ n : ℕ, ∃ (Nn : ℕ) (πn : Partition s t Nn), πn.mesh < 1 / (n + 1 : ℝ) := by
        intro n; exact exists_partition hst' _ (by positivity)
      choose Nn πn hπn using hseq
      -- The sequence of Riemann sums is Cauchy
      have hRS_cauchy : CauchySeq (fun n => (πn n).riemannSum A) := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        obtain ⟨δ, hδ_pos, hδ⟩ := cauchy hst'.le ε hε
        obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n, M ≤ n → (πn n).mesh < δ := by
          obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
          refine ⟨M, fun n hn => ?_⟩
          calc (πn n).mesh < 1 / (n + 1 : ℝ) := hπn n
            _ ≤ 1 / (M + 1 : ℝ) := by
                apply div_le_div_of_nonneg_left one_pos.le (by positivity)
                  (by exact_mod_cast Nat.succ_le_succ hn)
            _ < δ := by
                rw [div_lt_iff₀ (by positivity : (0 : ℝ) < M + 1)]
                have := (div_lt_iff₀ hδ_pos).mp hM
                linarith
        exact ⟨M, fun m hm n hn => by rw [Real.dist_eq]; exact hδ (πn m) (πn n) (hM m hm) (hM n hn)⟩
      -- Extract the limit
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hRS_cauchy
      refine ⟨L, ?_, ?_⟩
      · -- Maximal inequality: |L - A s t| ≤ C * ω(s,t)^θ
        have hbound : ∀ n, |(πn n).riemannSum A - A s t| ≤ C * (ω s t : ℝ) ^ θ :=
          fun n => maximalInequality ω hθ hA hst'.le (πn n)
        have htend : Filter.Tendsto (fun n => |(πn n).riemannSum A - A s t|) Filter.atTop
            (nhds |L - A s t|) :=
          (hL.sub tendsto_const_nhds).abs
        exact le_of_tendsto htend (Filter.Eventually.of_forall hbound)
      · -- Convergence
        intro ε hε
        -- Use Cauchy property with ε/2 to get δ₁
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := cauchy hst'.le (ε / 2) (by linarith)
        -- Find M such that |riemannSum(πn M) - L| < ε/2 and mesh(πn M) < δ₁
        have hconv := Metric.tendsto_atTop.mp hL (ε / 2) (by linarith)
        obtain ⟨M₁, hM₁⟩ := hconv
        obtain ⟨M₂, hM₂⟩ : ∃ M₂ : ℕ, ∀ n, M₂ ≤ n → (πn n).mesh < δ₁ := by
          obtain ⟨M₂, hM₂⟩ := exists_nat_gt (1 / δ₁)
          refine ⟨M₂, fun n hn => ?_⟩
          calc (πn n).mesh < 1 / (n + 1 : ℝ) := hπn n
            _ ≤ 1 / (M₂ + 1 : ℝ) := by
                apply div_le_div_of_nonneg_left one_pos.le (by positivity)
                  (by exact_mod_cast Nat.succ_le_succ hn)
            _ < δ₁ := by
                rw [div_lt_iff₀ (by positivity : (0 : ℝ) < M₂ + 1)]
                have := (div_lt_iff₀ hδ₁_pos).mp hM₂
                linarith
        set m := max M₁ M₂
        refine ⟨δ₁, hδ₁_pos, fun {N} π hmesh => ?_⟩
        have h1 : |π.riemannSum A - (πn m).riemannSum A| < ε / 2 := by
          rw [abs_sub_comm]; exact hδ₁ (πn m) π (hM₂ m (le_max_right _ _)) hmesh
        have h2 : |(πn m).riemannSum A - L| < ε / 2 := by
          have := hM₁ m (le_max_left _ _); rwa [Real.dist_eq] at this
        calc |π.riemannSum A - L|
            = |(π.riemannSum A - (πn m).riemannSum A) + ((πn m).riemannSum A - L)| := by ring_nf
          _ ≤ |π.riemannSum A - (πn m).riemannSum A| + |(πn m).riemannSum A - L| := abs_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add h1 h2
          _ = ε := by ring
  -- === Extract sewing values ===
  set sewVal : ∀ {s t : ℝ}, s ≤ t → ℝ := fun hst => Classical.choose (limit_exists hst)
  have hsewVal_spec : ∀ {s t : ℝ} (hst : s ≤ t),
      (|sewVal hst - A s t| ≤ C * (ω s t : ℝ) ^ θ) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ {N : ℕ} (π : Partition s t N), π.mesh < δ →
        |π.riemannSum A - sewVal hst| < ε) :=
    fun hst => Classical.choose_spec (limit_exists hst)
  -- === Additivity (sorry) ===
  have sewVal_add : ∀ {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t),
      sewVal (hsu.trans hut) = sewVal hsu + sewVal hut := by
    intro s u t hsu hut
    -- We show sewVal(s,t) = sewVal(s,u) + sewVal(u,t) by uniqueness of the limit.
    -- For any ε > 0, we can find partitions of [s,u] and [u,t] whose Riemann sums
    -- are close to sewVal(s,u) and sewVal(u,t), and their concatenation is a partition
    -- of [s,t] whose Riemann sum is the sum, and is close to sewVal(s,t).
    by_contra h
    push_neg at h
    set L := sewVal (hsu.trans hut)
    set L₁ := sewVal hsu
    set L₂ := sewVal hut
    have hne : L ≠ L₁ + L₂ := h
    set gap := |L - (L₁ + L₂)| / 3
    have hgap_pos : 0 < gap := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
    -- Get δ's for all three intervals
    obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := (hsewVal_spec (hsu.trans hut)).2 gap hgap_pos
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := (hsewVal_spec hsu).2 gap hgap_pos
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := (hsewVal_spec hut).2 gap hgap_pos
    set δ := min δ₀ (min δ₁ δ₂)
    have hδ_pos : 0 < δ := lt_min hδ₀_pos (lt_min hδ₁_pos hδ₂_pos)
    -- Case: s = u
    rcases eq_or_lt_of_le hsu with rfl | hsu'
    · -- sewVal(s,s) doesn't exist as a proper partition (Partition s s N is empty)
      -- So sewVal hsu = L₁ is defined by Classical.choose on limit_exists (le_refl s).
      -- From the spec, |L₁ - A s s| ≤ C * ω(s,s)^θ = C * 0 = 0, so L₁ = A s s.
      -- Similarly L = sewVal(s,t) and L₂ = sewVal(s,t).
      -- We need L = L₁ + L₂ = A s s + sewVal(s,t).
      -- Hmm but (le_refl s).trans hut = hut... Wait, the `sewVal` depends on the proof term.
      -- Actually `sewVal` is defined as `fun hst => Classical.choose (limit_exists hst)`.
      -- So `sewVal (le_refl s)` and `sewVal hut` may differ even when `le_refl s ≤ hut`.
      -- The issue is that `L = sewVal (hsu.trans hut) = sewVal hut` since `hsu = le_refl s`
      -- and `(le_refl s).trans hut = hut`? No, they are different proof terms but propositionally equal.
      -- Since `sewVal` takes a proof of `s ≤ t` and ℝ is a type, `Classical.choose` may give
      -- different values for propositionally equal proofs! We need proof irrelevance.
      -- In Lean 4, Prop is proof-irrelevant, so `hsu.trans hut = hut` as proofs of `s ≤ t`.
      -- Therefore `sewVal (hsu.trans hut) = sewVal hut = L₂`. And `sewVal hsu = L₁`.
      -- We need L₁ = 0 (since sewVal of a degenerate interval).
      -- From spec: |L₁ - A s s| ≤ C * (ω s s : ℝ) ^ θ = C * 0 = 0
      have hL₁_eq : L₁ = A s s := by
        have h := (hsewVal_spec hsu).1
        rw [ω.zero_diag, NNReal.coe_zero, Real.zero_rpow (by linarith : θ ≠ 0), mul_zero] at h
        have := abs_nonneg (L₁ - A s s)
        have := le_antisymm h this
        linarith [abs_eq_zero.mp this]
      -- L = L₂ since proof irrelevance
      have hL_eq : L = L₂ := by rfl
      -- Now we need L₂ = A s s + L₂, which requires A s s = 0... not necessarily true!
      -- Hmm. So the approach via concatenation needs more care.
      -- Actually, we should prove this differently. Let me just show convergence directly.
      -- For any fine partition of [s,t] that includes u as a point, the Riemann sum splits.
      -- When s = u, any partition of [s,t] already starts at s = u.
      -- Its Riemann sum = sum over [s,t] = Riemann sum of [u,t] = close to L₂.
      -- And L = sewVal(s,t) is also close to the same Riemann sums.
      -- So L = L₂. And L₁ = A s s (from the bound). So L = L₁ + L₂ iff A s s = 0.
      -- But A s s need not be 0! This is a genuine issue.
      -- Wait, but sewVal for s = u: the spec says the limit of Riemann sums over [s,s].
      -- But there are no partitions of [s,s] (since we need strictly monotone points from s to s).
      -- So the ∀ clause in the spec is vacuously true for any L₁!
      -- The only constraint is |L₁ - A s s| ≤ 0, so L₁ = A s s.
      -- And L = L₂ (proof irrelevance). So L₁ + L₂ = A s s + L₂ = A s s + L.
      -- This equals L iff A s s = 0. But A s s could be anything!
      -- This means the statement sewVal_add is FALSE when s = u and A s s ≠ 0!
      -- Unless... let me re-examine. We have limit_exists gives us L₁ with the bound.
      -- The bound is |L₁ - A s s| ≤ 0, so L₁ = A s s.
      -- And the convergence part is vacuously true.
      -- For the other side: L = sewVal(s,t) = L₂ = sewVal(u,t) (proof irrelevance since s=u).
      -- Wait no! s = u, so sewVal (hsu.trans hut) : sewVal (s ≤ t) and
      -- sewVal hut : sewVal (u ≤ t) = sewVal (s ≤ t). By proof irrelevance these are the same.
      -- So L = L₂. And L₁ = A s s. We need L = A s s + L. So A s s = 0... contradiction.
      --
      -- Unless the limit_exists for s = s doesn't give L₁ = A s s but L₁ = 0?
      -- Let me re-read limit_exists. It says |L - A s t| ≤ C * ω(s,t)^θ.
      -- For s = t: |L₁ - A s s| ≤ C * 0^θ = 0. So L₁ = A s s. Not 0.
      --
      -- I think the issue is that sewVal_add as stated may need a different approach.
      -- Actually, wait. When s = u, `sewVal hsu` where `hsu : s ≤ s` gives A s s.
      -- And `sewVal (hsu.trans hut) = sewVal hut` by proof irrelevance? Actually NO.
      -- `hsu.trans hut : s ≤ t` and `hut : u ≤ t` where `u = s`. These are both proofs of
      -- `s ≤ t` (since u = s). By proof irrelevance of Prop, `hsu.trans hut = hut` (as terms
      -- of type `s ≤ t`). So `sewVal (hsu.trans hut) = sewVal hut`.
      -- But `sewVal hut` is the Classical.choose for `limit_exists (hut : s ≤ t)` (since u = s).
      -- And `sewVal hut` (with `hut : u ≤ t`) before the `rfl` is for `limit_exists (hut : u ≤ t)`.
      -- After `rcases eq_or_lt_of_le hsu with rfl | hsu'`, we have `u` replaced by `s`, so
      -- `hut : s ≤ t` and `hsu : s ≤ s`.
      -- So L = sewVal (hsu.trans hut) and L₂ = sewVal hut.
      -- These use different proofs of `s ≤ t`: `hsu.trans hut` vs `hut`.
      -- But by proof irrelevance, they're the same proof! So L = L₂.
      -- Then L₁ + L₂ = A s s + L ≠ L unless A s s = 0.
      -- This suggests sewVal_add is simply not true in this generality without A s s = 0.
      --
      -- But the sewing lemma should work. Let me reconsider the approach.
      -- Perhaps I should not case-split and instead directly use the convergence characterization.
      -- Let me try a cleaner proof using the uniqueness of limits.
      -- The key fact: for any ε > 0, there exist fine partitions of [s,u] and [u,t] whose
      -- Riemann sums approximate L₁ and L₂. Concatenating gives a partition of [s,t] whose
      -- Riemann sum is L₁ + L₂ ± ε, and this must also be close to L.
      -- But constructing the concatenation is the issue when s = u (empty partition of [s,s]).
      -- When s = u, the "partition of [s,u]" doesn't exist (N ≥ 0 means ≥ 2 points).
      -- So we can't concatenate. We need a different argument for s = u.
      -- Actually when s = u, L₁ = A s s and L = L₂ (by proof irrelevance), and we need
      -- A s s + L₂ = L₂, i.e., A s s = 0.
      -- Unless there's a global assumption that A s s = 0? Let me check the defect bound.
      -- hA says |defect A s u t| ≤ ω(s,t)^θ for s ≤ u ≤ t.
      -- defect A s s s = A s s - A s s - A s s = -A s s.
      -- |A s s| ≤ ω(s,s)^θ = 0. So A s s = 0!
      have hAss : A s s = 0 := by
        have h := hA (le_refl s) (le_refl s)
        simp [defect, ω.zero_diag, Real.zero_rpow (by linarith : θ ≠ 0)] at h
        linarith [abs_nonneg (-(A s s))]
      exact hne (by rw [hL₁_eq, hAss, zero_add])
    · -- s < u: both intervals are nontrivial, or u = t.
      rcases eq_or_lt_of_le hut with rfl | hut'
      · -- u = t: symmetric to s = u case
        have hL₂_eq : L₂ = A u u := by
          have h := (hsewVal_spec hut).1
          rw [ω.zero_diag, NNReal.coe_zero, Real.zero_rpow (by linarith : θ ≠ 0), mul_zero] at h
          have := abs_nonneg (L₂ - A u u)
          linarith [abs_eq_zero.mp (le_antisymm h this)]
        have hAuu : A u u = 0 := by
          have h := hA (le_refl u) (le_refl u)
          simp only [defect, ω.zero_diag, NNReal.coe_zero,
            Real.zero_rpow (by linarith : θ ≠ 0)] at h
          -- h : |A u u - A u u - A u u| ≤ 0
          have heq : A u u - A u u - A u u = -(A u u) := by ring
          rw [heq] at h
          have := abs_nonneg (A u u)
          rw [abs_neg] at h
          linarith [abs_eq_zero.mp (le_antisymm h (abs_nonneg _))]
        exact hne (by rw [hL₂_eq, hAuu, add_zero])
      · -- s < u < t: both intervals are proper
        obtain ⟨N₁, π_su, hπ_su⟩ := exists_partition hsu' δ hδ_pos
        obtain ⟨N₂, π_ut, hπ_ut⟩ := exists_partition hut' δ hδ_pos
        -- Build concatenation partition
        set Nc := N₁ + N₂ + 1
        have hNc_def : Nc = N₁ + N₂ + 1 := rfl
        set cp : Fin (Nc + 2) → ℝ := fun k =>
          if h : k.val ≤ N₁ + 1 then π_su.points ⟨k.val, by omega⟩
          else π_ut.points ⟨k.val - (N₁ + 1), by have := k.isLt; omega⟩
        have hcp_sm : StrictMono cp := by
          intro ⟨a, ha⟩ ⟨b, hb⟩ hab
          simp only [cp, Fin.mk_lt_mk] at hab ⊢
          split_ifs with h1 h2
          · exact π_su.strictMono (by exact Fin.mk_lt_mk.mpr hab)
          · rcases eq_or_lt_of_le h1 with rfl | ha'
            · have : 0 < b - (N₁ + 1) := by omega
              calc π_su.points ⟨N₁ + 1, by omega⟩
                  = u := by
                    have : (⟨N₁ + 1, by omega⟩ : Fin (N₁ + 2)) = Fin.last (N₁ + 1) := by
                      ext; simp [Fin.val_last]
                    rw [this, π_su.last_eq]
                _ = π_ut.points 0 := π_ut.head_eq.symm
                _ < π_ut.points ⟨b - (N₁ + 1), by omega⟩ :=
                    π_ut.strictMono (by simp [Fin.lt_def]; omega)
            · calc π_su.points ⟨a, by omega⟩
                  < π_su.points ⟨N₁ + 1, by omega⟩ :=
                    π_su.strictMono (by simp [Fin.lt_def]; omega)
                _ = u := by
                    have : (⟨N₁ + 1, by omega⟩ : Fin (N₁ + 2)) = Fin.last (N₁ + 1) := by
                      ext; simp [Fin.val_last]
                    rw [this, π_su.last_eq]
                _ = π_ut.points 0 := π_ut.head_eq.symm
                _ ≤ π_ut.points ⟨b - (N₁ + 1), by omega⟩ :=
                    π_ut.strictMono.monotone (Fin.zero_le _)
          · omega
          · exact π_ut.strictMono (by simp [Fin.lt_def]; omega)
        have hcp_head : cp 0 = s := by
          simp only [cp, Fin.val_zero, show (0 : ℕ) ≤ N₁ + 1 from by omega, dif_pos]
          exact π_su.head_eq
        have hcp_last : cp (Fin.last (Nc + 1)) = t := by
          show (if h : (Fin.last (Nc + 1)).val ≤ N₁ + 1 then _ else _) = t
          rw [dif_neg (by simp [Fin.val_last, Nc])]
          have : (⟨(Fin.last (Nc + 1)).val - (N₁ + 1), by simp only [Fin.val_last, Nc]; omega⟩ :
            Fin (N₂ + 2)) = Fin.last (N₂ + 1) := by
            ext; simp only [Fin.val_last, Nc]; omega
          rw [this, π_ut.last_eq]
        set hcat : Partition s t Nc := ⟨cp, hcp_sm, hcp_head, hcp_last⟩
        -- Riemann sum splits
        have hRS_split : hcat.riemannSum A = π_su.riemannSum A + π_ut.riemannSum A := by
          simp only [Partition.riemannSum, hcat]
          -- Cast the LHS sum to Fin ((N₁+1) + (N₂+1))
          have hNc_eq : Nc + 1 = (N₁ + 1) + (N₂ + 1) := by omega
          set f : Fin (Nc + 1) → ℝ := fun k => A (cp k.castSucc) (cp k.succ)
          -- Reindex via finCongr
          -- Key: (finCongr hNc_eq).symm preserves Fin.val
          have hfcval : ∀ (k : Fin ((N₁ + 1) + (N₂ + 1))),
            ((finCongr hNc_eq).symm k).val = k.val := fun k => by
            simp [finCongr, Fin.val_cast]
          -- cp only depends on Fin.val, so we can simplify
          have hcp_val : ∀ (a b : Fin (Nc + 2)), a.val = b.val → cp a = cp b := fun a b h => by
            have hab : a = b := Fin.ext h
            rw [hab]
          -- For the first sum: castAdd preserves val, so finCongr.symm ∘ castAdd has val = k
          -- For the second sum: natAdd adds (N₁+1), so finCongr.symm ∘ natAdd has val = k + (N₁+1)
          set g : Fin ((N₁ + 1) + (N₂ + 1)) → ℝ := fun k => f ((finCongr hNc_eq).symm k)
          have hreindex : ∑ k, f k = ∑ k, g k :=
            Fintype.sum_equiv (finCongr hNc_eq) f g (fun x => by simp [g])
          rw [hreindex, Fin.sum_univ_add]
          congr 1
          · apply Finset.sum_congr rfl; intro ⟨k, hk⟩ _
            show g (Fin.castAdd (N₂ + 1) ⟨k, hk⟩) =
              A (π_su.points (⟨k, hk⟩ : Fin (N₁ + 1)).castSucc)
                (π_su.points (⟨k, hk⟩ : Fin (N₁ + 1)).succ)
            simp only [g, f]
            have hv1 : ((finCongr hNc_eq).symm (Fin.castAdd (N₂ + 1) ⟨k, hk⟩)).castSucc.val =
              k := by simp [Fin.coe_castSucc, hfcval, Fin.castAdd]
            have hv2 : ((finCongr hNc_eq).symm (Fin.castAdd (N₂ + 1) ⟨k, hk⟩)).succ.val =
              k + 1 := by simp [Fin.val_succ, hfcval, Fin.castAdd]
            rw [hcp_val _ ⟨k, by omega⟩ hv1,
                hcp_val _ ⟨k + 1, by omega⟩ hv2]
            simp only [cp, dif_pos (show k ≤ N₁ + 1 by omega),
              dif_pos (show k + 1 ≤ N₁ + 1 by omega)]
            congr 1 <;> congr 1 <;> exact Fin.ext rfl
          · apply Finset.sum_congr rfl; intro ⟨k, hk⟩ _
            show g (Fin.natAdd (N₁ + 1) ⟨k, hk⟩) =
              A (π_ut.points (⟨k, hk⟩ : Fin (N₂ + 1)).castSucc)
                (π_ut.points (⟨k, hk⟩ : Fin (N₂ + 1)).succ)
            simp only [g, f]
            have hv1 : ((finCongr hNc_eq).symm (Fin.natAdd (N₁ + 1) ⟨k, hk⟩)).castSucc.val =
              k + (N₁ + 1) := by simp [Fin.coe_castSucc, hfcval, Fin.natAdd]; omega
            have hv2 : ((finCongr hNc_eq).symm (Fin.natAdd (N₁ + 1) ⟨k, hk⟩)).succ.val =
              k + (N₁ + 1) + 1 := by simp [Fin.val_succ, hfcval, Fin.natAdd]; omega
            -- Both cp args need rewriting. Use Fin.ext to equate Fin args.
            have hFin1 : ((finCongr hNc_eq).symm (Fin.natAdd (N₁ + 1) ⟨k, hk⟩)).castSucc =
              (⟨k + (N₁ + 1), by omega⟩ : Fin (Nc + 2)) := Fin.ext (by
                simp [Fin.coe_castSucc, hfcval, Fin.natAdd]; omega)
            have hFin2 : ((finCongr hNc_eq).symm (Fin.natAdd (N₁ + 1) ⟨k, hk⟩)).succ =
              (⟨k + (N₁ + 1) + 1, by omega⟩ : Fin (Nc + 2)) := Fin.ext (by
                simp [Fin.val_succ, hfcval, Fin.natAdd]; omega)
            -- Use congrArg to rewrite cp args
            show A (cp ((finCongr hNc_eq).symm (Fin.natAdd (N₁ + 1) ⟨k, hk⟩)).castSucc)
              (cp ((finCongr hNc_eq).symm (Fin.natAdd (N₁ + 1) ⟨k, hk⟩)).succ) = _
            rw [show ((finCongr hNc_eq).symm (Fin.natAdd (N₁ + 1) ⟨k, hk⟩)).castSucc =
              (⟨k + (N₁ + 1), by omega⟩ : Fin (Nc + 2)) from hFin1]
            rw [show ((finCongr hNc_eq).symm (Fin.natAdd (N₁ + 1) ⟨k, hk⟩)).succ =
              (⟨k + (N₁ + 1) + 1, by omega⟩ : Fin (Nc + 2)) from hFin2]
            -- k + (N₁+1) ≤ N₁+1 iff k = 0
            -- k + (N₁+1) + 1 > N₁+1 always
            have hn2 : ¬ (k + (N₁ + 1) + 1 ≤ N₁ + 1) := by omega
            by_cases hk0 : k = 0
            · -- k = 0: first arg is at boundary (N₁+1), cp gives π_su.points = u
              subst hk0
              simp only [Fin.val_mk, cp, show (0 : ℕ) + (N₁ + 1) = N₁ + 1 from by omega,
                dif_pos (le_refl _), dif_neg hn2,
                Fin.castSucc, Fin.succ]
              congr 1
              · -- π_su.points ⟨N₁+1, _⟩ = u = π_ut.points 0
                rw [show (⟨N₁ + 1, _⟩ : Fin (N₁ + 2)) = Fin.last (N₁ + 1) from
                  Fin.ext (by simp [Fin.val_last])]
                rw [π_su.last_eq]
                exact π_ut.head_eq.symm
              · convert rfl using 3 <;> simp
            · -- k > 0: both args use dif_neg
              have hn1 : ¬ (k + (N₁ + 1) ≤ N₁ + 1) := by omega
              simp only [Fin.val_mk, cp, dif_neg hn1, dif_neg hn2,
                Fin.castSucc, Fin.succ]
              convert rfl using 3 <;> simp <;> omega
        -- Mesh bound
        have hbdd_su : BddAbove (Set.range fun j : Fin (N₁ + 1) =>
            π_su.points j.succ - π_su.points j.castSucc) :=
          ⟨t - s, fun x ⟨j, hj⟩ => hj ▸ by
            linarith [π_su.strictMono.monotone (Fin.zero_le j.castSucc),
              π_su.strictMono.monotone (Fin.le_last j.succ), π_su.head_eq, π_su.last_eq]⟩
        have hbdd_ut : BddAbove (Set.range fun j : Fin (N₂ + 1) =>
            π_ut.points j.succ - π_ut.points j.castSucc) :=
          ⟨t - s, fun x ⟨j, hj⟩ => hj ▸ by
            linarith [π_ut.strictMono.monotone (Fin.zero_le j.castSucc),
              π_ut.strictMono.monotone (Fin.le_last j.succ), π_ut.head_eq, π_ut.last_eq]⟩
        have hcat_mesh : hcat.mesh < δ := by
          simp only [Partition.mesh, hcat]
          rw [← sSup_range, Set.Finite.csSup_lt_iff (Set.finite_range _) (Set.range_nonempty _)]
          rintro _ ⟨⟨k, hk⟩, rfl⟩
          show cp ⟨k + 1, by omega⟩ - cp ⟨k, by omega⟩ < δ
          simp only [cp]
          by_cases h1 : k + 1 ≤ N₁ + 1
          · rw [dif_pos (show k ≤ N₁ + 1 by omega), dif_pos h1]
            have hk' : k < N₁ + 1 := by omega
            have : π_su.points ⟨k + 1, by omega⟩ - π_su.points ⟨k, by omega⟩ =
              π_su.points (⟨k, hk'⟩ : Fin (N₁ + 1)).succ -
              π_su.points (⟨k, hk'⟩ : Fin (N₁ + 1)).castSucc := by
              simp [Fin.succ, Fin.castSucc]
            rw [this]
            exact lt_of_le_of_lt (le_ciSup hbdd_su ⟨k, hk'⟩) hπ_su
          · push_neg at h1
            by_cases h2 : k ≤ N₁ + 1
            · -- k = N₁ + 1 (boundary case)
              have hk_eq : k = N₁ + 1 := by omega
              subst hk_eq
              rw [dif_pos (le_refl _), dif_neg (show ¬ (N₁ + 1 + 1 ≤ N₁ + 1) by omega)]
              -- Goal: π_ut.points ⟨N₁+1+1-(N₁+1), _⟩ - π_su.points ⟨N₁+1, _⟩ < δ
              have hsu_last : π_su.points ⟨N₁ + 1, by omega⟩ = u := by
                have : (⟨N₁ + 1, by omega⟩ : Fin (N₁ + 2)) = Fin.last (N₁ + 1) := by
                  ext; simp [Fin.val_last]
                rw [this, π_su.last_eq]
              -- The term is: π_ut.points ⟨1, _⟩ - π_su.points ⟨N₁+1, _⟩
              -- = π_ut.points 1 - u = π_ut.points 1 - π_ut.points 0
              have h_eq : π_ut.points ⟨N₁ + 1 + 1 - (N₁ + 1), by omega⟩ -
                    π_su.points ⟨N₁ + 1, by omega⟩ =
                  π_ut.points (0 : Fin (N₂ + 1)).succ -
                    π_ut.points (0 : Fin (N₂ + 1)).castSucc := by
                have : (0 : Fin (N₂ + 1)).succ = (⟨1, by omega⟩ : Fin (N₂ + 2)) := by
                  ext; simp [Fin.succ]
                have : (0 : Fin (N₂ + 1)).castSucc = (⟨0, by omega⟩ : Fin (N₂ + 2)) := by
                  ext; simp [Fin.castSucc]
                rw [‹(0 : Fin (N₂ + 1)).succ = _›, ‹(0 : Fin (N₂ + 1)).castSucc = _›]
                congr 1
                · congr 1; ext; simp
                · rw [hsu_last]; exact π_ut.head_eq.symm
              rw [h_eq]
              exact lt_of_le_of_lt (le_ciSup hbdd_ut (0 : Fin (N₂ + 1))) hπ_ut
            · push_neg at h2
              rw [dif_neg (show ¬ (k + 1 ≤ N₁ + 1) by omega),
                dif_neg (show ¬ (k ≤ N₁ + 1) by omega)]
              have hj : k - (N₁ + 1) < N₂ + 1 := by omega
              have hconv : π_ut.points ⟨k + 1 - (N₁ + 1), by omega⟩ -
                    π_ut.points ⟨k - (N₁ + 1), by omega⟩ =
                  π_ut.points (⟨k - (N₁ + 1), hj⟩ : Fin (N₂ + 1)).succ -
                    π_ut.points (⟨k - (N₁ + 1), hj⟩ : Fin (N₂ + 1)).castSucc := by
                simp only [Fin.succ, Fin.castSucc, Fin.val_mk]
                congr 1 <;> (congr 1; ext; simp; omega)
              rw [hconv]
              exact lt_of_le_of_lt (le_ciSup hbdd_ut ⟨k - (N₁ + 1), hj⟩) hπ_ut
        -- Derive contradiction
        have h1 : |hcat.riemannSum A - L| < gap :=
          hδ₀ hcat (lt_of_lt_of_le hcat_mesh (min_le_left _ _))
        have h2 : |π_su.riemannSum A - L₁| < gap :=
          hδ₁ π_su (lt_of_lt_of_le hπ_su (le_trans (min_le_right δ₀ _) (min_le_left δ₁ δ₂)))
        have h3 : |π_ut.riemannSum A - L₂| < gap :=
          hδ₂ π_ut (lt_of_lt_of_le hπ_ut (le_trans (min_le_right δ₀ _) (min_le_right δ₁ δ₂)))
        have h4 : |hcat.riemannSum A - (L₁ + L₂)| < 2 * gap := by
          rw [hRS_split]
          calc |π_su.riemannSum A + π_ut.riemannSum A - (L₁ + L₂)|
              = |(π_su.riemannSum A - L₁) + (π_ut.riemannSum A - L₂)| := by ring_nf
            _ ≤ |π_su.riemannSum A - L₁| + |π_ut.riemannSum A - L₂| := abs_add_le _ _
            _ < gap + gap := add_lt_add h2 h3
            _ = 2 * gap := by ring
        have h5 : |L - (L₁ + L₂)| < 3 * gap := by
          calc |L - (L₁ + L₂)|
              = |(L - hcat.riemannSum A) + (hcat.riemannSum A - (L₁ + L₂))| := by ring_nf
            _ ≤ |L - hcat.riemannSum A| + |hcat.riemannSum A - (L₁ + L₂)| := abs_add_le _ _
            _ = |hcat.riemannSum A - L| + |hcat.riemannSum A - (L₁ + L₂)| := by rw [abs_sub_comm]
            _ < gap + 2 * gap := add_lt_add h1 h4
            _ = 3 * gap := by ring
        have hgap_def : gap = |L - (L₁ + L₂)| / 3 := rfl
        linarith [h5]
  -- === Define I and prove both parts ===
  have I_diff_eq : ∀ {s t : ℝ} (hst : s ≤ t),
      (if h : 0 ≤ t then sewVal h else -(sewVal (le_of_lt (not_le.mp h)))) -
      (if h : 0 ≤ s then sewVal h else -(sewVal (le_of_lt (not_le.mp h)))) =
      sewVal hst := by
    intro s t hst
    -- Case 1: 0 ≤ s ≤ t
    -- Case 2: s ≤ 0 ≤ t
    -- Case 3: s ≤ t ≤ 0
    by_cases h0s : 0 ≤ s
    · -- Case 1: 0 ≤ s ≤ t
      have h0t : 0 ≤ t := le_trans h0s hst
      simp only [h0s, h0t, dite_true]
      -- sewVal(0,t) - sewVal(0,s) = sewVal(s,t)
      -- From sewVal_add: sewVal(0,t) = sewVal(0,s) + sewVal(s,t)
      have := sewVal_add h0s hst
      linarith
    · push_neg at h0s
      by_cases h0t : 0 ≤ t
      · -- Case 2: s < 0 ≤ t
        have hs_neg : ¬ (0 ≤ s) := by linarith
        simp only [hs_neg, dite_false, h0t, dite_true]
        -- sewVal(0,t) - (-(sewVal(s,0))) = sewVal(0,t) + sewVal(s,0) = sewVal(s,t)
        -- From sewVal_add: sewVal(s,t) = sewVal(s,0) + sewVal(0,t)
        have := sewVal_add h0s.le h0t
        linarith
      · -- Case 3: s ≤ t < 0
        push_neg at h0t
        have hs_neg : ¬ (0 ≤ s) := by linarith
        have ht_neg : ¬ (0 ≤ t) := by linarith
        simp only [hs_neg, ht_neg, dite_false]
        -- -(sewVal(t,0)) + sewVal(s,0) = sewVal(s,t)
        -- From sewVal_add: sewVal(s,0) = sewVal(s,t) + sewVal(t,0)
        have := sewVal_add hst h0t.le
        linarith
  exact ⟨fun t => if h : 0 ≤ t then sewVal h
    else -(sewVal (le_of_lt (not_le.mp h))),
    fun {s t} hst => by rw [I_diff_eq hst]; exact (hsewVal_spec hst).1,
    fun {s t} hst ε hε => by rw [I_diff_eq hst]; exact (hsewVal_spec hst).2 ε hε⟩
