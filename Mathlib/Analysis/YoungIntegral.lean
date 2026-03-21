/-
Copyright (c) 2025 Emilio Ferrucci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilio Ferrucci
-/
import Mathlib.Topology.EMetricSpace.PVariation
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.BoundedVariation

open Filter
open scoped Topology

set_option linter.style.longFile 2800
set_option linter.style.setOption false
set_option linter.flexible false

/-!
# Young Integral

We define Riemann-Stieltjes sums and prove the Young-Loève estimate, bounding the difference
between a Riemann-Stieltjes sum and the trivial partition approximation in terms of the
$p$-variation of $f$ and the $q$-variation of $g$, when $1/p + 1/q > 1$.

We prove existence and uniqueness of the Young integral. The proof follows the second proof of the
Sewing lemma, namely Lemma 4.2 in *A Course on Rough Paths* by Friz and Hairer, with the
difference that we work with variation instead of Hölder regularity.

### Main definitions

* `IsSuperadditiveOn a b ω`: interval superadditivity on the simplex over `[a, b]`.
* `IsControlOn a b ω`: a control on `[a, b]`, i.e. a superadditive interval function that is zero
  on the diagonal and tends to `0` on collapsing intervals.
* `young_control f g p q`: the interval function
  `(pVariationPowOn f (Set.Icc s t) p).toReal + (pVariationPowOn g (Set.Icc s t) q).toReal`
  used in the Young-Loève estimate.
* `young_loeve_constant p q`: a constant depending only on `p` and `q` used in the
  Young-Loève estimate.
* `Partition a b`: a partition of the interval `[a, b]`.
* `Partition.Refines π ρ`: the partition `π` is a refinement of the partition `ρ`.
* `Partition.common_refinement π ρ`: the common refinement obtained by taking the union of the
  partition points of `π` and `ρ` and removing duplicates.
* `Partition.restrict π hs ht hst`: the partition obtained by restricting `π` to the subinterval
  cut out by two of its partition points.
* `Partition.rsSum`: Riemann-Stieltjes sum of `f dg` over a partition.

### Main statements

* `not_isSuperadditiveOn_of_forall_lt_skip`: a finite combinatorial criterion forcing failure of
  superadditivity on an interval.
* `young_loeve_bound`: the Young-Loève estimate for a Riemann-Stieltjes sum over a partition of
  `[a, b]`.
* `Partition.rsSum_go_insert_point`: inserting one partition point changes the recursive
  Riemann-Stieltjes sum by a local three-point term.

-/

/-- An interval function on `ℝ × ℝ` is superadditive on `[a, b]` if it is nonnegative and
superadditive on ordered triples in the simplex over `[a, b]` (we require non-negativity since
it is needed in the definition of control). -/
def IsSuperadditiveOn (a b : ℝ) (ω : ℝ → ℝ → ℝ) : Prop :=
  (∀ ⦃s t : ℝ⦄, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ω s t) ∧
    ∀ ⦃s t u : ℝ⦄,
      a ≤ s → s ≤ t → t ≤ u → u ≤ b → ω s t + ω t u ≤ ω s u

/-- A control on `[a, b]` is a non-negative, superadditive interval function that vanishes on the
diagonal and tends to `0` on collapsing intervals inside `[a, b]`.

This is weaker than the standard definition in the literature, where one also requires continuity
on the whole simplex `a ≤ s ≤ t ≤ b`. The weaker notion is enough for the results in
this file. -/
def IsControlOn (a b : ℝ) (ω : ℝ → ℝ → ℝ) : Prop :=
  IsSuperadditiveOn a b ω ∧
    (∀ ⦃s : ℝ⦄, a ≤ s → s ≤ b → ω s s = 0) ∧
    (∀ ⦃x : ℝ⦄, x ∈ Set.Icc a b →
      ∀ ⦃s t : ℕ → ℝ⦄,
        (∀ n, s n ∈ Set.Icc a (t n)) → (∀ n, t n ∈ Set.Icc (s n) b) →
        Tendsto s atTop (𝓝 x) → Tendsto t atTop (𝓝 x) →
          Tendsto (fun n => ω (s n) (t n)) atTop (𝓝 0))

lemma isControlOn_pVariationPowOn {E : Type*} [PseudoEMetricSpace E] (f : ℝ → E) {a b p : ℝ}
    (hp : 1 ≤ p) (hf : ContinuousOn f (Set.Icc a b))
    (hpv : FinitePVariationOn f (Set.Icc a b) p) :
    IsControlOn a b (fun s t => (pVariationPowOn f (Set.Icc s t) p).toReal) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro s t has hst htb
      exact ENNReal.toReal_nonneg
    · intro s t u has hst htu hub
      have hst_ne_top : pVariationPowOn f (Set.Icc s t) p ≠ ⊤ :=
        ne_top_of_le_ne_top hpv
          (pVariationPowOn.mono f (Set.Icc_subset_Icc has (htu.trans hub)))
      have htu_ne_top : pVariationPowOn f (Set.Icc t u) p ≠ ⊤ :=
        ne_top_of_le_ne_top hpv
          (pVariationPowOn.mono f (Set.Icc_subset_Icc (has.trans hst) hub))
      have hsu_ne_top : pVariationPowOn f (Set.Icc s u) p ≠ ⊤ :=
        ne_top_of_le_ne_top hpv (pVariationPowOn.mono f (Set.Icc_subset_Icc has hub))
      have hleft : ∀ x ∈ Set.Icc s t, ∀ y ∈ Set.Icc t u, x ≤ y := by
        intro x hx y hy
        exact hx.2.trans hy.1
      have hadd := pVariationPowOn.add_le_union f (p := p) hleft
      have hunion : Set.Icc s t ∪ Set.Icc t u = Set.Icc s u := by
        ext x
        simp [hst, htu]
      rw [← ENNReal.toReal_add hst_ne_top htu_ne_top]
      exact ENNReal.toReal_mono hsu_ne_top (by simpa [hunion] using hadd)
  · intro s has hsb
    have hp0 : 0 < p := by linarith
    have hzero : pVariationPowOn f (Set.Icc s s) p = 0 := by
      refine le_antisymm ?_ bot_le
      apply iSup_le
      rintro ⟨n, u, hu, hus⟩
      have hs : ∀ i, u i = s := fun i => by simpa using hus i
      calc
        ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ p = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          simp [hs i, hs (i + 1), hp0]
        _ ≤ 0 := le_rfl
    simpa [Set.Icc_self] using congrArg ENNReal.toReal hzero
  · intro x hx s t hst htb hs ht
    have hfin : ∀ n, pVariationPowOn f (Set.Icc (s n) (t n)) p ≠ ⊤ := fun n =>
      ne_top_of_le_ne_top hpv (pVariationPowOn.mono f (Set.Icc_subset_Icc (hst n).1 (htb n).2))
    simpa [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal_zero_iff hfin).2
        (pVariationPowOn.tendsto_pVariationPowOn_of_tendsto hp hf hpv hx hst htb hs ht)

lemma isControlOn_add {a b : ℝ} {ω₁ ω₂ : ℝ → ℝ → ℝ}
    (hω₁ : IsControlOn a b ω₁) (hω₂ : IsControlOn a b ω₂) :
    IsControlOn a b (fun s t => ω₁ s t + ω₂ s t) := by
  rcases hω₁ with ⟨hsuper₁, hdiag₁, hcont₁⟩
  rcases hω₂ with ⟨hsuper₂, hdiag₂, hcont₂⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases hsuper₁ with ⟨hnonneg₁, hsuper₁⟩
    rcases hsuper₂ with ⟨hnonneg₂, hsuper₂⟩
    refine ⟨?_, ?_⟩
    · intro s t has hst htb
      exact add_nonneg (hnonneg₁ has hst htb) (hnonneg₂ has hst htb)
    · intro s t u has hst htu hub
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add (hsuper₁ has hst htu hub) (hsuper₂ has hst htu hub)
  · intro s has hsb
    simp [hdiag₁ has hsb, hdiag₂ has hsb]
  · intro x hx s t hst htb hs ht
    simpa using (hcont₁ hx hst htb hs ht).add (hcont₂ hx hst htb hs ht)


/-- The control used in the Young-Loève estimate, obtained by summing the `p`-variation power of
`f` and the `q`-variation power of `g` on subintervals. -/
noncomputable def young_control (f g : ℝ → ℝ) (p q : ℝ) (s t : ℝ) : ℝ :=
  (pVariationPowOn f (Set.Icc s t) p).toReal + (pVariationPowOn g (Set.Icc s t) q).toReal

/-- The interval function `young_control f g p q` is a control on `[a, b]` whenever `f` and `g`
are continuous and have finite `p`- and `q`-variation on `[a, b]`. -/
lemma isControlOn_young_control (f g : ℝ → ℝ) {a b p q : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p)
    (hgq : FinitePVariationOn g (Set.Icc a b) q) :
    IsControlOn a b (young_control f g p q) := by
  apply_rules [ isControlOn_add, isControlOn_pVariationPowOn ]

/-- A partition of `[a, b]` is a list of real numbers that is strictly increasing,
starts at `a`, and ends at `b`. -/
structure Partition (a b : ℝ) where
  /-- The list of partition points. -/
  pts : List ℝ
  /-- The partition points are strictly increasing. -/
  sorted : pts.IsChain (· < ·)
  /-- The first partition point is `a`. -/
  first : pts.head? = some a
  /-- The last partition point is `b`. -/
  last : pts.getLast? = some b

/-- Chain the even skipped intervals in a finite increasing sequence. -/
lemma sum_skip_even_le
    {m n : ℕ} {ω : ℝ → ℝ → ℝ} {skip : ℕ → ℝ} {u : Fin (m + 1) → ℝ}
    (hω : IsSuperadditiveOn (u 0) (u ⟨m, by omega⟩) ω)
    (hu : StrictMono u)
    (hn : n ≤ m / 2)
    (hskip :
      ∀ j, ∀ hjm : j + 2 ≤ m,
        skip j =
          ω (u ⟨j, by
              exact lt_of_lt_of_le (by omega : j < j + 2) (le_trans hjm (Nat.le_succ m))
            ⟩)
            (u ⟨j + 2, by
              exact lt_of_le_of_lt hjm (Nat.lt_succ_self m)
            ⟩)) :
    Finset.sum (Finset.range n) (fun k => skip (2 * k)) ≤
        ω (u 0) (u ⟨2 * n, by omega⟩) := by
  rcases hω with ⟨hnonneg, hsuper⟩
  have hu_mono : Monotone u := hu.monotone
  induction n with
  | zero =>
      let i0 : Fin (m + 1) := 0
      let im : Fin (m + 1) := ⟨m, by omega⟩
      have hi0im : u i0 ≤ u im := by
        have h : (0 : ℕ) ≤ m := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      simpa [i0, im] using hnonneg le_rfl le_rfl hi0im
  | succ n ih =>
      let i0 : Fin (m + 1) := 0
      let i2n : Fin (m + 1) := ⟨2 * n, by omega⟩
      let i2n2 : Fin (m + 1) := ⟨2 * n + 2, by omega⟩
      have hn' : n ≤ m / 2 := by omega
      have hi0i2n : u i0 ≤ u i2n := by
        have h : (0 : ℕ) ≤ 2 * n := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      have hi2ni2n2 : u i2n ≤ u i2n2 := by
        have h : 2 * n ≤ 2 * n + 2 := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      have hi2n2im : u i2n2 ≤ u ⟨m, by omega⟩ := by
        have h : 2 * n + 2 ≤ m := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      rw [Finset.sum_range_succ]
      have h2n : 2 * n + 2 ≤ m := by omega
      rw [hskip (2 * n) h2n]
      calc
        Finset.sum (Finset.range n) (fun k => skip (2 * k)) + ω (u i2n) (u i2n2)
            ≤ ω (u i0) (u i2n) + ω (u i2n) (u i2n2) := by
              gcongr
              simpa [i0, i2n] using ih hn' hskip
        _ ≤ ω (u i0) (u i2n2) := by
              exact hsuper le_rfl hi0i2n hi2ni2n2 hi2n2im
        _ = ω (u 0) (u ⟨2 * (n + 1), by omega⟩) := by
              simp [i0, i2n2, two_mul, add_assoc, add_left_comm, add_comm]

/-- Chain the odd skipped intervals in a finite increasing sequence. -/
lemma sum_skip_odd_le
    {m n : ℕ} {ω : ℝ → ℝ → ℝ} {skip : ℕ → ℝ} {u : Fin (m + 1) → ℝ}
    (hω : IsSuperadditiveOn (u 0) (u ⟨m, by omega⟩) ω)
    (hu : StrictMono u)
    (hn : n ≤ (m - 1) / 2)
    (hnm : 2 * n + 1 ≤ m)
    (hskip :
      ∀ j, ∀ hjm : j + 2 ≤ m,
        skip j =
          ω (u ⟨j, by
              exact lt_of_lt_of_le (by omega : j < j + 2) (le_trans hjm (Nat.le_succ m))
            ⟩)
            (u ⟨j + 2, by
              exact lt_of_le_of_lt hjm (Nat.lt_succ_self m)
            ⟩)) :
    Finset.sum (Finset.range n) (fun k => skip (2 * k + 1)) ≤
        ω (u ⟨1, by omega⟩)
          (u ⟨2 * n + 1, by
            exact lt_of_le_of_lt hnm (Nat.lt_succ_self m)⟩) := by
  rcases hω with ⟨hnonneg, hsuper⟩
  have hu_mono : Monotone u := hu.monotone
  induction n with
  | zero =>
      let i1 : Fin (m + 1) := ⟨1, by omega⟩
      let im : Fin (m + 1) := ⟨m, by omega⟩
      have hi01 : u (0 : Fin (m + 1)) ≤ u i1 := by
        have h : (0 : ℕ) ≤ 1 := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      have hi1im : u i1 ≤ u im := by
        have h : 1 ≤ m := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      simpa [i1, im] using hnonneg hi01 le_rfl hi1im
  | succ n ih =>
      let i1 : Fin (m + 1) := ⟨1, by omega⟩
      let i2n1 : Fin (m + 1) := ⟨2 * n + 1, by omega⟩
      let i2n3 : Fin (m + 1) := ⟨2 * n + 3, by omega⟩
      have hn' : n ≤ (m - 1) / 2 := by omega
      have hnm' : 2 * n + 1 ≤ m := by omega
      have hi01 : u (0 : Fin (m + 1)) ≤ u i1 := by
        have h : (0 : ℕ) ≤ 1 := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      have hi1i2n1 : u i1 ≤ u i2n1 := by
        have h : 1 ≤ 2 * n + 1 := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      have hi2n1i2n3 : u i2n1 ≤ u i2n3 := by
        have h : 2 * n + 1 ≤ 2 * n + 3 := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      have hi2n3im : u i2n3 ≤ u ⟨m, by omega⟩ := by
        have h : 2 * n + 3 ≤ m := by omega
        exact hu_mono (Fin.le_iff_val_le_val.2 h)
      rw [Finset.sum_range_succ]
      have h2n : 2 * n + 3 ≤ m := by omega
      rw [hskip (2 * n + 1) h2n]
      calc
        Finset.sum (Finset.range n) (fun k => skip (2 * k + 1)) + ω (u i2n1) (u i2n3)
            ≤ ω (u i1) (u i2n1) + ω (u i2n1) (u i2n3) := by
              gcongr
              simpa [i1, i2n1] using ih hn' hnm' hskip
        _ ≤ ω (u i1) (u i2n3) := by
              exact hsuper hi01 hi1i2n1 hi2n1i2n3 hi2n3im
        _ =
            ω (u ⟨1, by omega⟩)
              (u ⟨2 * (n + 1) + 1, by
                  exact lt_of_le_of_lt hnm (Nat.lt_succ_self m)
                ⟩) := by
              simp [i1, i2n3, two_mul, add_assoc, add_left_comm, add_comm]

/-- If every skip-one interval exceeds the pigeonhole threshold,
then `ω` is not superadditive. -/
theorem not_isSuperadditiveOn_of_forall_lt_skip
    {m : ℕ} (hm : 2 ≤ m) {ω : ℝ → ℝ → ℝ} {u : Fin (m + 1) → ℝ}
    (hu : StrictMono u)
    (hbad :
      ∀ j, ∀ hjm : j + 2 ≤ m,
        (2 / (m - 1 : ℝ)) * ω (u 0) (u ⟨m, by omega⟩) <
          ω (u ⟨j, by
              exact lt_of_lt_of_le (by omega : j < j + 2) (le_trans hjm (Nat.le_succ m))
            ⟩)
            (u ⟨j + 2, by
              exact lt_of_le_of_lt hjm (Nat.lt_succ_self m)
            ⟩)) :
    ¬ IsSuperadditiveOn (u 0) (u ⟨m, by omega⟩) ω := by
  intro hω
  rcases hω with ⟨hnonneg, hsuper⟩
  have hω' : IsSuperadditiveOn (u 0) (u ⟨m, by omega⟩) ω := ⟨hnonneg, hsuper⟩
  let W : ℝ := ω (u 0) (u ⟨m, by omega⟩)
  let skip : ℕ → ℝ := fun j =>
    if hjm : j + 2 ≤ m then
      ω (u ⟨j, by
            exact lt_of_lt_of_le (by omega : j < j + 2) (le_trans hjm (Nat.le_succ m))
          ⟩)
        (u ⟨j + 2, by
            exact lt_of_le_of_lt hjm (Nat.lt_succ_self m)
          ⟩)
    else
      0
  have hskip :
      ∀ j, ∀ hjm : j + 2 ≤ m,
        skip j =
          ω (u ⟨j, by
              exact lt_of_lt_of_le (by omega : j < j + 2) (le_trans hjm (Nat.le_succ m))
            ⟩)
            (u ⟨j + 2, by
              exact lt_of_le_of_lt hjm (Nat.lt_succ_self m)
            ⟩) := by
    intro j hjm
    simp [skip, hjm]
  have hm1_pos : 0 < m - 1 := by omega
  have hm1_ne : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hlower :
      2 * W < Finset.sum (Finset.range (m - 1)) skip := by
    have hsum_bad :
        Finset.sum (Finset.range (m - 1)) (fun _ => (2 / (((m - 1 : ℕ) : ℝ))) * W) <
          Finset.sum (Finset.range (m - 1)) skip := by
      have hm_cast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
        norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
      refine Finset.sum_lt_sum_of_nonempty
        (by simpa using (Finset.nonempty_range_iff.mpr hm1_pos.ne')) ?_
      intro j hj
      have hjm : j + 2 ≤ m := by
        have hjlt : j < m - 1 := Finset.mem_range.mp hj
        omega
      have hbad' := hbad j hjm
      simpa [skip, hjm, W, hm_cast] using hbad'
    rw [Finset.sum_const, Finset.card_range] at hsum_bad
    have hcalc : ((m - 1 : ℕ) : ℝ) * ((2 / (((m - 1 : ℕ) : ℝ))) * W) = 2 * W := by
      field_simp [hm1_ne]
    have hsum_bad' :
        ((m - 1 : ℕ) : ℝ) * ((2 / (((m - 1 : ℕ) : ℝ))) * W) <
          Finset.sum (Finset.range (m - 1)) skip := by
      simpa [nsmul_eq_mul] using hsum_bad
    simpa [hcalc] using hsum_bad'
  have heven_reindex :
      Finset.sum ((Finset.range (m - 1)).filter Even) skip =
        Finset.sum (Finset.range (m / 2)) (fun k => skip (2 * k)) := by
    symm
    refine Finset.sum_bij' (fun k _ => 2 * k) (fun j _ => j / 2) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      refine Finset.mem_filter.mpr ?_
      constructor
      · simp [Finset.mem_range] at hk ⊢
        omega
      · simp
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hj, hjeven⟩
      obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hjeven
      simp [Finset.mem_range] at hj ⊢
      omega
    · intro k hk
      simp
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨_, hjeven⟩
      obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hjeven
      simp
    · intro k hk
      simp [skip]
  have hodd_reindex :
      Finset.sum ((Finset.range (m - 1)).filter Odd) skip =
        Finset.sum (Finset.range ((m - 1) / 2)) (fun k => skip (2 * k + 1)) := by
    symm
    refine Finset.sum_bij' (fun k _ => 2 * k + 1) (fun j _ => j / 2) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      refine Finset.mem_filter.mpr ?_
      constructor
      · simp [Finset.mem_range] at hk ⊢
        omega
      · refine ⟨k, by ring⟩
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hj, hjodd⟩
      obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp hjodd
      subst hk
      simp [Finset.mem_range] at hj ⊢
      omega
    · intro k hk
      change (2 * k + 1) / 2 = k
      omega
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨_, hjodd⟩
      obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp hjodd
      subst hk
      have hkdiv : (2 * k + 1) / 2 = k := by
        omega
      simp [hkdiv]
    · intro k hk
      simp [skip]
  have heven_le_W :
      Finset.sum ((Finset.range (m - 1)).filter Even) skip ≤ W := by
    rw [heven_reindex]
    have hsum :=
      sum_skip_even_le (hω := hω') (hu := hu) (hn := le_rfl) (skip := skip) (hskip := hskip)
    let imid : Fin (m + 1) := ⟨2 * (m / 2), by omega⟩
    let im : Fin (m + 1) := ⟨m, by omega⟩
    have h0mid_nat : (0 : ℕ) ≤ 2 * (m / 2) := by omega
    have hmidm_nat : 2 * (m / 2) ≤ m := by omega
    have h0mid : u 0 ≤ u imid := by
      exact hu.monotone (Fin.le_iff_val_le_val.2 h0mid_nat)
    have hmidm : u imid ≤ u im := by
      exact hu.monotone (Fin.le_iff_val_le_val.2 hmidm_nat)
    have htail_nonneg : 0 ≤ ω (u imid) (u im) := by
      exact hnonneg h0mid hmidm le_rfl
    have htail :
        ω (u 0) (u imid) + ω (u imid) (u im) ≤ W := by
      simpa [W, imid, im] using hsuper le_rfl h0mid hmidm le_rfl
    linarith
  have hodd_le_W :
      Finset.sum ((Finset.range (m - 1)).filter Odd) skip ≤ W := by
    rw [hodd_reindex]
    have hsum :=
      sum_skip_odd_le (hω := hω') (hu := hu) (hn := le_rfl) (hnm := by omega)
        (skip := skip) (hskip := hskip)
    let i1 : Fin (m + 1) := ⟨1, by omega⟩
    let imid : Fin (m + 1) := ⟨2 * ((m - 1) / 2) + 1, by
      exact lt_of_le_of_lt (by omega) (Nat.lt_succ_self m)⟩
    let im : Fin (m + 1) := ⟨m, by omega⟩
    have h01_nat : (0 : ℕ) ≤ 1 := by omega
    have h0mid_nat : (0 : ℕ) ≤ 2 * ((m - 1) / 2) + 1 := by omega
    have h1mid_nat : 1 ≤ 2 * ((m - 1) / 2) + 1 := by omega
    have hmidm_nat : 2 * ((m - 1) / 2) + 1 ≤ m := by omega
    have h01 : u 0 ≤ u i1 := by
      exact hu.monotone (Fin.le_iff_val_le_val.2 h01_nat)
    have h0mid : u 0 ≤ u imid := by
      exact hu.monotone (Fin.le_iff_val_le_val.2 h0mid_nat)
    have h1mid : u i1 ≤ u imid := by
      exact hu.monotone (Fin.le_iff_val_le_val.2 h1mid_nat)
    have hmidm : u imid ≤ u im := by
      exact hu.monotone (Fin.le_iff_val_le_val.2 hmidm_nat)
    have hodd_to_m :
        ω (u i1) (u imid) ≤ ω (u i1) (u im) := by
      have htail_nonneg : 0 ≤ ω (u imid) (u im) := by
        exact hnonneg h0mid hmidm le_rfl
      have htail :
          ω (u i1) (u imid) + ω (u imid) (u im) ≤ ω (u i1) (u im) := by
        exact hsuper h01 h1mid hmidm le_rfl
      linarith
    have h1m_le_W : ω (u i1) (u im) ≤ W := by
      have h1m : u i1 ≤ u im := by
        exact hu.monotone (Fin.le_iff_val_le_val.2 (by omega : 1 ≤ m))
      have h01_nonneg : 0 ≤ ω (u 0) (u i1) := by
        exact hnonneg le_rfl h01 h1m
      have hsplit :
          ω (u 0) (u i1) + ω (u i1) (u im) ≤ W := by
        simpa [W, i1, im] using hsuper le_rfl h01 h1m le_rfl
      linarith
    linarith
  have hupper : Finset.sum (Finset.range (m - 1)) skip ≤ 2 * W := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range (m - 1)) (p := Even)]
    have hnot_even_iff_odd : ∀ j : ℕ, ¬ Even j ↔ Odd j := by
      intro j
      exact (Nat.not_even_iff_odd : ¬ Even j ↔ Odd j)
    simp_rw [hnot_even_iff_odd]
    linarith [heven_le_W, hodd_le_W]
  linarith

private lemma finset_sort_isChain (s : Finset ℝ) : (s.sort (· ≤ ·)).IsChain (· < ·) := by
  rw [List.isChain_iff_pairwise]
  have h := Finset.sortedLT_sort s
  rw [List.SortedLT] at h
  exact List.pairwise_iff_get.mpr (fun i j hij => h hij)

private lemma finset_sort_head?_eq_min' (s : Finset ℝ) (hs : s.Nonempty) :
    (s.sort (· ≤ ·)).head? = some (s.min' hs) := by
  have hne : (s.sort (· ≤ ·)) ≠ [] := by
    simp [← List.length_pos_iff_ne_nil, Finset.length_sort]
    exact hs
  rw [List.head?_eq_some_head hne]
  congr
  have hhead_mem : (s.sort (· ≤ ·)).head hne ∈ s := by
    rw [← Finset.mem_sort (· ≤ ·)]
    exact List.head_mem hne
  have hlen : 0 < (s.sort (· ≤ ·)).length := by
    rwa [List.length_pos_iff_ne_nil]
  apply le_antisymm
  · have hsorted := Finset.pairwise_sort s (· ≤ ·)
    have hhead_le : ∀ x ∈ s.sort (· ≤ ·), (s.sort (· ≤ ·)).head hne ≤ x := by
      intro x hx
      obtain ⟨⟨i, hi⟩, hget⟩ := List.get_of_mem hx
      rw [← hget]
      cases i with
      | zero => simp [List.head_eq_getElem]
      | succ i =>
        have h0i : (⟨0, hlen⟩ : Fin (s.sort (· ≤ ·)).length) < ⟨i + 1, hi⟩ := by
          exact Fin.mk_lt_mk.mpr (by omega)
        have := List.pairwise_iff_get.mp hsorted ⟨0, hlen⟩ ⟨i + 1, hi⟩ h0i
        simp [List.head_eq_getElem] at this ⊢
        exact this
    exact hhead_le _ ((Finset.mem_sort _).mpr (Finset.min'_mem s hs))
  · exact Finset.min'_le s _ hhead_mem

private lemma finset_sort_getLast?_eq_max' (s : Finset ℝ) (hs : s.Nonempty) :
    (s.sort (· ≤ ·)).getLast? = some (s.max' hs) := by
  set l := s.sort (· ≤ ·) with hl_def
  have hne : l ≠ [] := by
    simp [hl_def, ← List.length_pos_iff_ne_nil, Finset.length_sort]
    exact hs
  rw [List.getLast?_eq_some_getLast hne]
  congr
  have hlast_mem : l.getLast hne ∈ s := by
    rw [← Finset.mem_sort (· ≤ ·), ← hl_def]
    exact List.getLast_mem hne
  apply le_antisymm
  · exact Finset.le_max' s _ hlast_mem
  · apply Finset.max'_le s hs
    intro x hx
    have hsorted := Finset.pairwise_sort s (· ≤ ·)
    rw [← hl_def] at hsorted
    have hx_mem : x ∈ l := (Finset.mem_sort _).mpr hx
    obtain ⟨⟨i, hi⟩, hget⟩ := List.get_of_mem hx_mem
    rw [← hget, List.getLast_eq_getElem]
    have hlast_idx : l.length - 1 < l.length := by omega
    by_cases hcase : i = l.length - 1
    · subst hcase; simp
    · exact List.pairwise_iff_get.mp hsorted ⟨i, hi⟩ ⟨l.length - 1, hlast_idx⟩
        (Fin.mk_lt_mk.mpr (by omega))

private lemma le_of_mem_chain_head {l : List ℝ} (hchain : l.IsChain (· < ·))
    {a : ℝ} (hhead : l.head? = some a) {x : ℝ} (hx : x ∈ l) : a ≤ x := by
  rw [List.isChain_iff_pairwise] at hchain
  have hne : l ≠ [] := by rintro rfl; simp at hhead
  have ha : a = l.head hne := by
    rw [List.head?_eq_some_head hne] at hhead
    exact (Option.some_injective _ hhead).symm
  subst ha
  obtain ⟨⟨i, hi⟩, hget⟩ := List.get_of_mem hx
  rw [← hget]
  cases i with
  | zero => simp [List.head_eq_getElem]
  | succ i =>
    have h0 : (⟨0, by omega⟩ : Fin l.length) < ⟨i + 1, hi⟩ := Fin.mk_lt_mk.mpr (by omega)
    have hlt := List.pairwise_iff_get.mp hchain _ _ h0
    change l[0] < l[i + 1] at hlt
    rw [show l.head hne = l[0] from by simp [List.head_eq_getElem]]
    exact le_of_lt hlt

private lemma le_of_mem_chain_getLast {l : List ℝ} (hchain : l.IsChain (· < ·))
    {b : ℝ} (hlast : l.getLast? = some b) {x : ℝ} (hx : x ∈ l) : x ≤ b := by
  rw [List.isChain_iff_pairwise] at hchain
  have hne : l ≠ [] := by rintro rfl; simp at hlast
  have hb : b = l.getLast hne := by
    rw [List.getLast?_eq_some_getLast hne] at hlast
    exact (Option.some_injective _ hlast).symm
  subst hb
  obtain ⟨⟨i, hi⟩, hget⟩ := List.get_of_mem hx
  rw [← hget]
  have hlast_idx : l.length - 1 < l.length := by omega
  by_cases hcase : i = l.length - 1
  · subst hcase; simp [List.getLast_eq_getElem]
  · have hlt : (⟨i, hi⟩ : Fin l.length) <
        ⟨l.length - 1, hlast_idx⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    have hlt := List.pairwise_iff_get.mp hchain _ _ hlt
    change l[i] < l[l.length - 1] at hlt
    rw [show l.getLast hne = l[l.length - 1] from by simp [List.getLast_eq_getElem]]
    exact le_of_lt hlt

namespace Partition

variable {a b : ℝ}

/-- A partition `π` refines a partition `ρ` if every partition point of `ρ` is also a partition
point of `π`. -/
def Refines (π ρ : Partition a b) : Prop :=
  ∀ x ∈ ρ.pts, x ∈ π.pts

private lemma exists_common_refinement (π ρ : Partition a b) :
    ∃ τ : Partition a b, τ.pts = (π.pts.toFinset ∪ ρ.pts.toFinset).sort := by
  set S := π.pts.toFinset ∪ ρ.pts.toFinset with hS_def
  have hS_ne : S.Nonempty := by
    have : a ∈ π.pts := List.mem_of_mem_head? π.first
    exact ⟨a, Finset.mem_union_left _ (List.mem_toFinset.mpr this)⟩
  refine ⟨⟨S.sort (· ≤ ·), finset_sort_isChain S, ?_, ?_⟩, rfl⟩
  · rw [finset_sort_head?_eq_min' S hS_ne]
    congr
    apply le_antisymm
    · apply Finset.min'_le
      exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_of_mem_head? π.first))
    · apply Finset.le_min'
      intro x hx
      rcases Finset.mem_union.mp hx with hxπ | hxρ
      · exact le_of_mem_chain_head π.sorted π.first (List.mem_toFinset.mp hxπ)
      · exact le_of_mem_chain_head ρ.sorted ρ.first (List.mem_toFinset.mp hxρ)
  · rw [finset_sort_getLast?_eq_max' S hS_ne]
    congr
    apply le_antisymm
    · apply Finset.max'_le
      intro x hx
      rcases Finset.mem_union.mp hx with hxπ | hxρ
      · exact le_of_mem_chain_getLast π.sorted π.last (List.mem_toFinset.mp hxπ)
      · exact le_of_mem_chain_getLast ρ.sorted ρ.last (List.mem_toFinset.mp hxρ)
    · apply Finset.le_max'
      exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_of_mem_getLast? π.last))

/-- The union of two partitions of `[a, b]`, obtained by taking the union of their partition
points and removing duplicates. -/
noncomputable def common_refinement (π ρ : Partition a b) : Partition a b :=
  Classical.choose (exists_common_refinement π ρ)

lemma common_refinement_refines_left (π ρ : Partition a b) :
    (common_refinement π ρ).Refines π := by
  intro x hx
  have hmem : x ∈ (π.pts.toFinset ∪ ρ.pts.toFinset).sort := by
    rw [Finset.mem_sort]
    exact Finset.mem_union.mpr <| Or.inl <| List.mem_toFinset.mpr hx
  simpa [common_refinement, Classical.choose_spec (exists_common_refinement π ρ)] using hmem

lemma common_refinement_refines_right (π ρ : Partition a b) :
    (common_refinement π ρ).Refines ρ := by
  intro x hx
  have hmem : x ∈ (π.pts.toFinset ∪ ρ.pts.toFinset).sort := by
    rw [Finset.mem_sort]
    exact Finset.mem_union.mpr <| Or.inr <| List.mem_toFinset.mpr hx
  simpa [common_refinement, Classical.choose_spec (exists_common_refinement π ρ)] using hmem

private lemma exists_restrict (π : Partition a b) {s t : ℝ}
    (hs : s ∈ π.pts) (ht : t ∈ π.pts) (hst : s ≤ t) :
    ∃ σ : Partition s t, σ.pts = ({x ∈ π.pts.toFinset | x ∈ Set.Icc s t}).sort := by
  set S := {x ∈ π.pts.toFinset | x ∈ Set.Icc s t} with hS_def
  have hS_ne : S.Nonempty := ⟨s, by simp [hS_def, Set.mem_Icc, hs, hst]⟩
  refine ⟨⟨S.sort (· ≤ ·), finset_sort_isChain S, ?_, ?_⟩, rfl⟩
  · rw [finset_sort_head?_eq_min' S hS_ne]
    congr
    apply le_antisymm
    · apply Finset.min'_le
      simp [hS_def, Set.mem_Icc, hs, hst]
    · apply Finset.le_min'
      intro x hx
      simp [hS_def, Set.mem_Icc] at hx
      exact hx.2.1
  · rw [finset_sort_getLast?_eq_max' S hS_ne]
    congr
    apply le_antisymm
    · apply Finset.max'_le
      intro x hx
      simp [hS_def, Set.mem_Icc] at hx
      exact hx.2.2
    · apply Finset.le_max'
      simp [hS_def, Set.mem_Icc, ht, hst]

/-- Restrict a partition to the subinterval cut out by two of its partition points. -/
noncomputable def restrict (π : Partition a b) {s t : ℝ}
    (hs : s ∈ π.pts) (ht : t ∈ π.pts) (hst : s ≤ t) : Partition s t :=
  Classical.choose (exists_restrict π hs ht hst)

/-- Riemann-Stieltjes sum of `f dg` over a partition `π`.
For `π.pts = [u₀, u₁, ..., uₘ]`, this is `∑ i, f(uᵢ) * (g(uᵢ₊₁) - g(uᵢ))`. -/
noncomputable def rsSum (π : Partition a b) (f g : ℝ → ℝ) : ℝ :=
  match π.pts with
  | [] => 0
  | x :: xs => go x xs
where
  go : ℝ → List ℝ → ℝ
    | _, [] => 0
    | x, y :: rest => f x * (g y - g x) + go y rest

/-- Split `rsSum.go` at an intermediate point `y`. -/
private lemma rsSum_go_append (f g : ℝ → ℝ) (x y : ℝ) (l₁ l₂ : List ℝ) :
    rsSum.go f g x (l₁ ++ y :: l₂) = rsSum.go f g x (l₁ ++ [y]) + rsSum.go f g y l₂ := by
  induction l₁ generalizing x with
  | nil =>
      simp [rsSum.go]
  | cons z l₁ ih =>
      simp [rsSum.go, ih, add_assoc]

/-- Adding one point `v` between consecutive points `u` and `w` changes the Riemann-Stieltjes
sum by a local three-point term. -/
theorem rsSum_go_insert_point (f g : ℝ → ℝ) (x u v w : ℝ) (l₁ l₂ : List ℝ) :
    rsSum.go f g x (l₁ ++ u :: v :: w :: l₂) - rsSum.go f g x (l₁ ++ u :: w :: l₂) =
      (f v - f u) * (g w - g v) := by
  rw [rsSum_go_append (l₂ := v :: w :: l₂), rsSum_go_append (l₂ := w :: l₂)]
  simp [rsSum.go]
  ring

/-- A constant depending only on `p` and `q` in the Young-Loève estimate. -/
noncomputable def young_loeve_constant (p q : ℝ) : ℝ :=
  2 ^ (1 / p + 1 / q) * ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (1 / p + 1 / q)

lemma summable_young_loeve_constant_series {p q : ℝ} (hpq : 1 < 1 / p + 1 / q) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (1 / p + 1 / q)) := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 / p + 1 / q)) :=
    (Real.summable_one_div_nat_rpow (p := 1 / p + 1 / q)).2 hpq
  exact ((_root_.summable_nat_add_iff
    (f := fun n : ℕ => 1 / (n : ℝ) ^ (1 / p + 1 / q)) 1).2 hsum)

/-
PROBLEM
The p-variation power controls individual increments: for `u ≤ v` both in `s`,
`edist (f v) (f u) ^ p ≤ pVariationPowOn f s p`.

PROVIDED SOLUTION
Use the two-point monotone sequence u_0 = u, u_1 = v to witness that pVariationPowOn f s p ≥ edist(f
v, f u)^p. The key is to apply le_iSup_of_le with the pair (1, ⟨fun i => if i = 0 then u else v,
monotone_proof, membership_proof⟩).
-/
set_option linter.style.refine false in
lemma edist_pow_le_pVariationPowOn {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) {s : Set ℝ} {u v : ℝ} (p : ℝ)
    (hu : u ∈ s) (hv : v ∈ s) (huv : u ≤ v) :
    edist (f v) (f u) ^ p ≤ pVariationPowOn f s p := by
  refine' le_trans _
    (le_ciSup _ ⟨1, ⟨fun i => if i = 0 then u else v, _, _⟩⟩) <;>
    norm_num [hu, hv, huv]
  · exact fun i j hij => by
      rcases i with (_ | _ | i) <;>
        rcases j with (_ | _ | j) <;> tauto
  · grind +ring

/-
PROBLEM
For real-valued functions, `|f(v) - f(u)| ≤ (pVariationPowOn f s p).toReal ^ (1/p)` when
`u ≤ v`, both are in `s`, and the `p`-variation is finite.

PROVIDED SOLUTION
From edist_pow_le_pVariationPowOn, we have edist(f v, f u)^p ≤ pVariationPowOn f s p.
Taking ENNReal.toReal and then the 1/p-th power (which is monotone for 1/p > 0 since p ≥ 1):
(edist(f v, f u)^p).toReal^(1/p) ≤ (pVariationPowOn f s p).toReal^(1/p).

For the LHS: |f v - f u| = dist(f v, f u) = (edist(f v, f u)).toReal (since f is real-valued, edist
is finite).
And (edist(f v, f u).toReal^p)^(1/p) = edist(f v, f u).toReal (for p ≥ 1 and nonneg base).

The key steps:
1. edist(f v, f u) ≤ pVariationPowOn(f,s,p)^(1/p) in ENNReal
2. Apply ENNReal.toReal_mono to get the real version
3. Note |f v - f u| = Real.dist (f v) (f u) = (edist (f v) (f u)).toReal

Use ENNReal.rpow_le_rpow and the fact that x^(1/p) is monotone. We need edist(f v)(f u) ≠ ⊤ (true
for real-valued functions since dist is finite). Also need pVariationPowOn ≠ ⊤ (given as hfin).

Actually, the cleanest approach: edist(f v, f u)^p ≤ pVariationPowOn f s p (from
edist_pow_le_pVariationPowOn). Since hfin says pVariationPowOn ≠ ⊤, we have edist(f v, f u)^p ≠ ⊤.
Take ENNReal.toReal of both sides (monotone since both are finite). Then (edist(f v, f u)^p).toReal
= (edist(f v, f u)).toReal^p (by ENNReal.toReal_rpow). So (edist(f v, f u)).toReal^p ≤
(pVariationPowOn f s p).toReal. Now take the 1/p-th root of both sides (using Real.rpow_le_rpow with
1/p ≥ 0): ((edist(f v, f u)).toReal^p)^(1/p) ≤ (pVariationPowOn f s p).toReal^(1/p). The LHS
simplifies to (edist(f v, f u)).toReal^(p * 1/p) = (edist(f v, f u)).toReal^1 = (edist(f v, f
u)).toReal. And (edist(f v, f u)).toReal = dist(f v, f u) = |f v - f u| for real-valued f.

Key lemmas: edist_pow_le_pVariationPowOn, ENNReal.toReal_mono, ENNReal.toReal_rpow,
Real.rpow_le_rpow, Real.rpow_natCast or similar, Real.dist_eq, edist_dist.
-/
lemma abs_sub_le_pVariationPowOn_toReal_rpow
    (f : ℝ → ℝ) {s : Set ℝ} {u v : ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hu : u ∈ s) (hv : v ∈ s) (huv : u ≤ v)
    (hfin : pVariationPowOn f s p ≠ ⊤) :
    |f v - f u| ≤ (pVariationPowOn f s p).toReal ^ (1 / p) := by
  have := hfin; simp_all +decide;
  have := edist_pow_le_pVariationPowOn f p hu hv huv;
  have h_abs : |f v - f u| ^ p ≤ (pVariationPowOn f s p).toReal := by
    convert ENNReal.toReal_mono _ this using 1;
    · rw [ ← ENNReal.toReal_rpow, edist_dist ] ; norm_num [ Real.dist_eq ];
    · assumption;
  exact le_trans
    (by
      rw [← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ (by positivity), Real.rpow_one])
    (Real.rpow_le_rpow (by positivity) h_abs (by positivity))

/-
PROBLEM
The core analytic ingredient: for `u ≤ v ≤ w`, the product of increments is bounded by the
Young control raised to `1/p + 1/q`.

PROVIDED SOLUTION
Use abs_sub_le_pVariationPowOn_toReal_rpow twice:
1. |f v - f u| ≤ (pVariationPowOn f (Icc u w) p).toReal^(1/p)  (using u ≤ v and Icc u w contains u,v
since u ≤ v ≤ w)
2. |g w - g v| ≤ (pVariationPowOn g (Icc u w) q).toReal^(1/q)  (using v ≤ w and Icc u w contains
v,w)

For step 2 we need |g w - g v| which has the arguments in wrong order for
abs_sub_le_pVariationPowOn_toReal_rpow (which bounds |f v - f u| with u ≤ v). Since g w - g v and v
≤ w, this is fine - apply with g, v, w.

Then multiply:
|f v - f u| * |g w - g v| ≤ A^(1/p) * B^(1/q)
where A = (pVariationPowOn f (Icc u w) p).toReal and B = (pVariationPowOn g (Icc u w) q).toReal.

Now we need A^(1/p) * B^(1/q) ≤ (A + B)^(1/p + 1/q).
Since A ≤ A + B and B ≤ A + B (both nonneg as ENNReal.toReal), and 1/p > 0, 1/q > 0:
A^(1/p) ≤ (A+B)^(1/p)  (by Real.rpow_le_rpow)
B^(1/q) ≤ (A+B)^(1/q)  (by Real.rpow_le_rpow)
So A^(1/p) * B^(1/q) ≤ (A+B)^(1/p) * (A+B)^(1/q) = (A+B)^(1/p + 1/q)  (by Real.rpow_add_of_nonneg
since A+B ≥ 0).

And A + B = young_control f g p q u w by definition.
-/
lemma abs_sub_mul_abs_sub_le_young_control_rpow
    (f g : ℝ → ℝ) {u v w p q : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hfin_f : pVariationPowOn f (Set.Icc u w) p ≠ ⊤)
    (hfin_g : pVariationPowOn g (Set.Icc u w) q ≠ ⊤) :
    |f v - f u| * |g w - g v| ≤
      (young_control f g p q u w) ^ (1 / p + 1 / q) := by
  -- Applying the bounds from Lemma 25 to each term in the product.
  have h_bound1 : |f v - f u| ≤ (pVariationPowOn f (Set.Icc u w) p).toReal ^ (1 / p) := by
    exact abs_sub_le_pVariationPowOn_toReal_rpow f hp
      (Set.mem_Icc.mpr ⟨le_refl u, huv.trans hvw⟩)
      (Set.mem_Icc.mpr ⟨huv, hvw⟩) huv hfin_f
  have h_bound2 : |g w - g v| ≤ (pVariationPowOn g (Set.Icc u w) q).toReal ^ (1 / q) := by
    convert abs_sub_le_pVariationPowOn_toReal_rpow g
      (show 1 ≤ q by linarith)
      (show v ∈ Set.Icc u w by constructor <;> linarith)
      (show w ∈ Set.Icc u w by constructor <;> linarith)
      (by linarith) _ using 1
    aesop
  refine le_trans (mul_le_mul h_bound1 h_bound2 (by positivity) (by positivity)) ?_
  rw [Real.rpow_add'] <;> norm_num
  · gcongr <;> norm_num [ young_control ];
    positivity;
  · exact add_nonneg ( ENNReal.toReal_nonneg ) ( ENNReal.toReal_nonneg );
  · positivity

/-
PROBLEM
Every partition has at least one point.

PROVIDED SOLUTION
Since π.first = pts.head? = some a, the list is not empty (head? of [] is none).
-/
lemma pts_ne_nil (π : Partition a b) : π.pts ≠ [] := by
  cases π ; aesop

/-
PROBLEM
A partition of a non-degenerate interval has at least two points.

PROVIDED SOLUTION
Since head? = some a we have length ≥ 1. If length = 1, then pts = [c] for some c, so head? = some c
= some a and getLast? = some c = some b, giving a = c = b. But hab : a < b contradicts a = b. So
length ≥ 2.
-/
set_option linter.style.multiGoal false in
lemma pts_length_ge_two (π : Partition a b) (hab : a < b) : 2 ≤ π.pts.length := by
  rcases π with ⟨l, hl₁, hl₂, hl₃⟩
  rcases l with (_ | ⟨a, _ | ⟨b, l⟩⟩) <;> simp_all +decide
  aesop
  aesop

/-
PROBLEM
A partition with exactly two points has `rsSum = f(a) * (g(b) - g(a))`.

PROVIDED SOLUTION
If pts has length 2, then pts = [x, y] for some x, y. From head? = some a we get x = a. From
getLast? = some b we get y = b. So pts = [a, b]. Then rsSum matches on a :: [b] giving rsSum.go f g
a [b] = f a * (g b - g a) + rsSum.go f g b [] = f a * (g b - g a) + 0 = f a * (g b - g a).
-/
lemma rsSum_of_length_two (f g : ℝ → ℝ) (π : Partition a b)
    (hlen : π.pts.length = 2) :
    π.rsSum f g = f a * (g b - g a) := by
  rcases π with ⟨ _ | ⟨ x, _ | ⟨ y, _ | h ⟩ ⟩ ⟩ <;> norm_num at *;
  · -- Since `x = a` and `y = b`, we can substitute these values into the rsSum.
    have hx : x = a := by
      aesop
    have hy : y = b := by
      aesop;
    -- Substitute hx and hy into the rsSum and simplify.
    simp [hx, hy, Partition.rsSum];
    simp [rsSum.go];
  · linarith

/-
PROBLEM
When a = b, the rsSum of any partition is 0.

PROVIDED SOLUTION
When a = b (the partition is of [a,a]), every point x in π.pts satisfies a ≤ x ≤ a (by
le_of_mem_chain_head and le_of_mem_chain_getLast), so x = a for all points. Since the list is sorted
by strict inequality (IsChain (· < ·)), and all elements equal a, the list must have exactly one
element [a]. Then rsSum matches on a :: [] giving rsSum.go f g a [] = 0.
-/
lemma rsSum_of_eq (f g : ℝ → ℝ) (π : Partition a a) : π.rsSum f g = 0 := by
  -- By definition of partition, if `π.pts` has at least two
  -- elements, then `π.pts` is strictly increasing and
  -- contains `a` and `a`.
  by_cases h_len : π.pts.length ≥ 2;
  · -- The list is strictly increasing and every point equals `a`,
    -- contradicting `π.pts.length ≥ 2`.
    have h_contra : ∀ x ∈ π.pts, x = a := by
      intros x hx; exact le_antisymm (by
      have := le_of_mem_chain_getLast π.sorted π.last hx; aesop;) (by
      apply le_of_mem_chain_head π.sorted π.first hx);
    rcases π with ⟨l, hl₁, hl₂, hl₃⟩
    rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩) <;> simp_all +decide
    exact absurd ( hl₁ ) ( by simp +decide [ h_contra ] );
  · interval_cases _ : π.pts.length <;> simp_all +decide;
    · cases π ; aesop;
    · unfold Partition.rsSum;
      rw [ List.length_eq_one_iff ] at * ; aesop

/-
PROBLEM
The Young-Loève constant is nonnegative.

PROVIDED SOLUTION
young_loeve_constant p q = 2^(1/p+1/q) * ∑' n, 1/((n+1):ℝ)^(1/p+1/q). Both factors are nonneg:
2^(1/p+1/q) ≥ 0 since 2 > 0, and the tsirelson series has nonneg terms.
-/
lemma young_loeve_constant_nonneg {p q : ℝ} (_hp : 1 ≤ p) (_hq : 1 ≤ q)
    (_hpq : 1 / p + 1 / q > 1) : 0 ≤ young_loeve_constant p q := by
  exact mul_nonneg ( Real.rpow_nonneg zero_le_two _ ) ( tsum_nonneg fun _ => by positivity )

/-
PROBLEM
The Young control is nonneg.

PROVIDED SOLUTION
young_control f g p q s t = (pVariationPowOn f (Set.Icc s t) p).toReal + (pVariationPowOn g (Set.Icc
s t) q).toReal. Both terms are nonneg since ENNReal.toReal is nonneg.
-/
lemma young_control_nonneg (f g : ℝ → ℝ) (p q s t : ℝ) :
    0 ≤ young_control f g p q s t := by
  exact add_nonneg ( ENNReal.toReal_nonneg ) ( ENNReal.toReal_nonneg )

/-
PROBLEM
The partition points form a strictly monotone function.

PROVIDED SOLUTION
The partition has π.sorted : π.pts.IsChain (· < ·). Use List.isChain_iff_pairwise to convert to
List.Pairwise, then use List.pairwise_iff_get to get the result for indices.
-/
lemma get_strictMono (π : Partition a b) :
    StrictMono (fun i : Fin π.pts.length => π.pts.get i) := by
  intro i j hij; have := List.pairwise_iff_get.mp ( List.isChain_iff_pairwise.mp π.sorted ) ; aesop;

/-
PROBLEM
The first partition point is `a`.

PROVIDED SOLUTION
From π.first : π.pts.head? = some a. Since h : 0 < π.pts.length, the list is nonempty.
List.head?_eq_some_head gives head? = some (head _). Then π.pts.get ⟨0, h⟩ = π.pts.head _ by
List.head_eq_getElem or similar.
-/
lemma get_first (π : Partition a b) (h : 0 < π.pts.length) :
    π.pts.get ⟨0, h⟩ = a := by
  have := π.first; rw [ List.head?_eq_getElem? ] at this; aesop;

/-
PROBLEM
The last partition point is `b`.

PROVIDED SOLUTION
From π.last : π.pts.getLast? = some b. Since the list is nonempty (h : 0 < length), getLast? = some
(getLast _). Then π.pts.get ⟨length - 1, _⟩ = getLast _ by List.getLast_eq_getElem or similar.
-/
lemma get_last (π : Partition a b) (h : 0 < π.pts.length) :
    π.pts.get ⟨π.pts.length - 1, by omega⟩ = b := by
  convert congr_arg Option.get! π.last using 1
  generalize_proofs at *;
  grind

/-
PROBLEM
Removing an interior point from a partition yields a valid partition.
Specifically, if `π.pts = l₁ ++ [u, v, w] ++ l₂`, then `l₁ ++ [u, w] ++ l₂` forms a
valid partition of `[a, b]` (obtained by dropping `v`).

PROVIDED SOLUTION
We need to show that erasing the (j+1)-th element from π.pts preserves the chain property, the first
element, and the last element.

For the chain: π.pts.IsChain (· < ·) implies the list is pairwise (· < ·). After erasing any
element, the remaining list is still pairwise (since pairwise is preserved under subsequences). Then
convert back to IsChain.

For the first: since j + 1 ≥ 1 > 0, erasing position j+1 doesn't change head?.

For the last: since j + 2 < π.pts.length, we have j + 1 < π.pts.length - 1, so erasing position j+1
doesn't change getLast?.

The length is π.pts.length - 1 by List.length_eraseIdx (since j+1 < π.pts.length).

Key lemmas: List.IsChain, List.Pairwise, List.isChain_iff_pairwise, List.Pairwise.eraseIdx (or
Sublist.pairwise), List.length_eraseIdx, head? and getLast? of eraseIdx.
-/
lemma eraseIdx_isPartition (π : Partition a b)
    {j : ℕ} (hj : j + 2 < π.pts.length) :
    ∃ ρ : Partition a b,
      ρ.pts = π.pts.eraseIdx (j + 1) ∧
      ρ.pts.length = π.pts.length - 1 := by
  use ⟨π.pts.eraseIdx (j + 1), by
    have h_chain : List.Pairwise (· < ·) (π.pts.eraseIdx (j + 1)) := by
      have := π.sorted
      generalize_proofs at *;
      exact (by
      exact List.Pairwise.eraseIdx _ ( List.IsChain.pairwise this ))
    generalize_proofs at *; (
    exact?), by
    have h_head : (π.pts.eraseIdx (j + 1)).head? = some (π.pts.head?.getD a) := by
      cases h : π.pts <;> aesop;
    cases π ; aesop, by
    have h_last : π.pts.getLast? = some b := by
      exact π.last
    generalize_proofs at *; (
    grind +ring)⟩
  generalize_proofs at *;
  simp [List.length_eraseIdx];
  exact fun h => absurd h ( by linarith )

/-
PROBLEM
The rsSum difference when removing an interior point.

PROVIDED SOLUTION
We need to relate the rsSum of π to the rsSum of π with element j+1 erased.

Key idea: Write π.pts as (take (j+1)) ++ [pts[j+1]] ++ (drop (j+2)).
Since head? = some a and 0 < length (from hj), π.pts = head :: tail where head = a.
The tail of π.pts has the form tail = (tail.take j) ++ [pts[j], pts[j+1], pts[j+2]] ++ rest.

Actually, let me think about this differently.
π.pts has head = pts[0] and tail = [pts[1], ..., pts[n-1]].
rsSum = rsSum.go f g pts[0] (tail).

After erasing index j+1, the list becomes pts[0] :: (tail with index j erased from tail). Wait,
eraseIdx on the full list at position j+1 removes the (j+1)-th element. If π.pts = h :: tl, then (h
:: tl).eraseIdx (j+1) = h :: (tl.eraseIdx j). So ρ.pts = pts[0] :: (tl.eraseIdx j).

Now, tl = tl.take j ++ [tl[j]] ++ tl.drop(j+1).
And in the full list, tl[j] = pts[j+1]. Before tl[j] is tl[j-1] = pts[j], and after is tl[j+1] =
pts[j+2].

So tl = tl.take(j-1) ++ [pts[j], pts[j+1], pts[j+2]] ++ rest where rest = tl.drop(j+2).

Wait, this is getting complicated. Let me use a different approach.

Actually, the cleanest way is to split the list at the right position and use rsSum_go_insert_point
directly.

π.pts = [pts[0], ..., pts[j], pts[j+1], pts[j+2], ..., pts[n-1]]
tail = [pts[1], ..., pts[j], pts[j+1], pts[j+2], ..., pts[n-1]]

Set l₁ = [pts[1], ..., pts[j-1]] (i.e., tail.take(j-1)), so tail = l₁ ++ [pts[j], pts[j+1],
pts[j+2]] ++ l₂ where l₂ = [pts[j+3], ...].

rsSum(π) = rsSum.go f g pts[0] (l₁ ++ pts[j] :: pts[j+1] :: pts[j+2] :: l₂)
rsSum(ρ) = rsSum.go f g pts[0] (l₁ ++ pts[j] :: pts[j+2] :: l₂)

By rsSum_go_insert_point:
rsSum(π) - rsSum(ρ) = (f(pts[j+1]) - f(pts[j])) * (g(pts[j+2]) - g(pts[j+1]))

This is exactly what we need. The proof requires showing the list decomposition.

Use List.take_append_drop to split the tail into the appropriate parts.
-/
set_option linter.style.multiGoal false in
lemma rsSum_eraseIdx_diff (π : Partition a b) (f g : ℝ → ℝ)
    {j : ℕ} (hj : j + 2 < π.pts.length)
    (ρ : Partition a b) (hρ : ρ.pts = π.pts.eraseIdx (j + 1)) :
    π.rsSum f g - ρ.rsSum f g =
      (f (π.pts.get ⟨j + 1, by omega⟩) - f (π.pts.get ⟨j, by omega⟩)) *
      (g (π.pts.get ⟨j + 2, hj⟩) - g (π.pts.get ⟨j + 1, by omega⟩)) := by
  -- By definition of rsSum, we can split the list into the
  -- parts before and after the erased element.
  have h_rsSum_split :
      π.rsSum f g =
          rsSum.go f g (π.pts.get ⟨0, by linarith⟩)
            (π.pts.take (j + 1) ++ [π.pts.get ⟨j + 1, by linarith⟩] ++
              π.pts.drop (j + 2)) ∧
        ρ.rsSum f g =
          rsSum.go f g (π.pts.get ⟨0, by linarith⟩)
            (π.pts.take (j + 1) ++ π.pts.drop (j + 2)) := by
    have hρ_pts : ρ.pts = π.pts.take (j + 1) ++ π.pts.drop (j + 2) := by
      rw [ hρ, List.eraseIdx_eq_take_drop_succ ]
    generalize_proofs at *;
    unfold Partition.rsSum
    generalize_proofs at *;
    unfold rsSum.go; aesop;
  generalize_proofs at *;
  convert rsSum_go_insert_point f g
      (π.pts.get ⟨0, by linarith⟩) (π.pts.get ⟨j, by linarith⟩)
      (π.pts.get ⟨j + 1, by linarith⟩) (π.pts.get ⟨j + 2, hj⟩)
      (List.take j π.pts) (List.drop (j + 3) π.pts) using 1
  norm_num [h_rsSum_split]
  simp +arith +decide [ List.take_add_one ];
  rw [ List.getElem?_eq_getElem ] ; norm_num [ ‹j < π.pts.length› ];
  linarith

/-
PROBLEM
The finite p-variation on a sub-interval is finite when the p-variation on the full interval
is finite.

PROVIDED SOLUTION
FinitePVariationOn means pVariationPowOn f (Set.Icc a b) p ≠ ⊤. By pVariationPowOn.mono with
Set.Icc_subset_Icc has htb, we get pVariationPowOn f (Set.Icc s t) p ≤ pVariationPowOn f (Set.Icc a
b) p. So pVariationPowOn f (Set.Icc s t) p ≠ ⊤ since it's ≤ a finite value.
-/
lemma FinitePVariationOn.subinterval {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) {a b s t p : ℝ}
    (has : a ≤ s) (htb : t ≤ b)
    (hfin : FinitePVariationOn f (Set.Icc a b) p) :
    FinitePVariationOn f (Set.Icc s t) p := by
  by_contra h_contra
  obtain ⟨h_le, h_ne_top⟩ :
      pVariationPowOn f (Set.Icc s t) p ≤ pVariationPowOn f (Set.Icc a b) p ∧
        pVariationPowOn f (Set.Icc a b) p ≠ ⊤ := by
    exact ⟨ pVariationPowOn.mono f ( Set.Icc_subset_Icc has htb ), hfin ⟩;
  exact h_contra ( ne_of_lt ( lt_of_le_of_lt h_le ( lt_top_iff_ne_top.mpr h_ne_top ) ) )

/-
PROBLEM
By contrapositive of `not_isSuperadditiveOn_of_forall_lt_skip`: if `ω` is superadditive on
`[u 0, u m]` and `2 ≤ m`, then there exists `j` with `j + 2 ≤ m` such that
`ω(u j, u (j+2)) ≤ (2/(m-1)) * ω(u 0, u m)`.

PROVIDED SOLUTION
This is the contrapositive of not_isSuperadditiveOn_of_forall_lt_skip.

By contradiction: assume the conclusion is false, i.e., for all j with j+2 ≤ m, we have ω(u_j,
u_{j+2}) > (2/(m-1)) * ω(u_0, u_m). But this is exactly the hypothesis hbad of
not_isSuperadditiveOn_of_forall_lt_skip, which would conclude ¬IsSuperadditiveOn, contradicting
hsuper.

Formally: by_contra h; push_neg at h (so h says for all j, j+2 ≤ m → the strict inequality holds);
exact not_isSuperadditiveOn_of_forall_lt_skip hm hu h hsuper.

Actually, push_neg on the negation of ∃ j, ∃ hjm, ω ... ≤ ... gives ∀ j, ∀ hjm, ¬(ω ... ≤ ...) which
is ∀ j, ∀ hjm, (2/(m-1))*ω < ω. This is exactly the hbad hypothesis of
not_isSuperadditiveOn_of_forall_lt_skip. Then apply that theorem to get ¬IsSuperadditiveOn,
contradicting hsuper.
-/
lemma exists_good_index_of_superadditive
    {m : ℕ} (hm : 2 ≤ m) {ω : ℝ → ℝ → ℝ} {u : Fin (m + 1) → ℝ}
    (hu : StrictMono u)
    (hsuper : IsSuperadditiveOn (u 0) (u ⟨m, by omega⟩) ω) :
    ∃ j : ℕ, ∃ hjm : j + 2 ≤ m,
      ω (u ⟨j, by omega⟩) (u ⟨j + 2, by omega⟩) ≤
        (2 / (m - 1 : ℝ)) * ω (u 0) (u ⟨m, by omega⟩) := by
  by_contra h;
  -- Apply the hypothesis `h` to obtain that for all `j`,
  -- `j + 2 ≤ m` implies `ω(u j, u (j+2)) > (2/(m-1)) *
  -- ω(u 0, u m)`.
  push_neg at h;
  exact not_isSuperadditiveOn_of_forall_lt_skip hm hu h hsuper

/-
PROBLEM
Algebraic step: the partial sum grows by the correct term.

PROVIDED SOLUTION
Since n ≥ 3:
- (n-1)-2 = n-3 in ℕ (by omega)
- n-2 = (n-3)+1 in ℕ (by omega)

So by Finset.sum_range_succ:
  ∑ k ∈ range(n-2), f(k) = ∑ k ∈ range(n-3), f(k) + f(n-3)

where f(k) = 1/((k+1):ℝ)^θ. So f(n-3) = 1/((n-3+1):ℝ)^θ = 1/((n-2):ℝ)^θ.

The RHS = 2^θ * (∑ k ∈ range(n-3), 1/(k+1)^θ + 1/(n-2)^θ)
        = 2^θ * ∑ k ∈ range(n-3), 1/(k+1)^θ + 2^θ * 1/(n-2)^θ

The LHS = 2^θ * ∑ k ∈ range(n-3), 1/(k+1)^θ + (2/(n-2))^θ

So need: (2/(n-2))^θ ≤ 2^θ * 1/(n-2)^θ = 2^θ/(n-2)^θ

But (2/(n-2))^θ = 2^θ/(n-2)^θ by Real.div_rpow (since 2 ≥ 0 and (n:ℝ)-2 ≥ 0 because n ≥ 3).

So this is equality, hence ≤ holds.

Cast note: ((n-3+1 : ℕ) : ℝ) = ((n-2 : ℕ) : ℝ) = (n : ℝ) - 2 since n ≥ 3.

Use: Nat.sub_add_cancel, push_cast, Finset.sum_range_succ, mul_add, Real.div_rpow.
-/
lemma partial_sum_step {n : ℕ} (hn : 3 ≤ n) (θ : ℝ) :
    2 ^ θ * ∑ k ∈ Finset.range ((n - 1) - 2), 1 / ((k + 1 : ℕ) : ℝ) ^ θ +
      (2 / ((n : ℝ) - 2)) ^ θ ≤
    2 ^ θ * ∑ k ∈ Finset.range (n - 2), 1 / ((k + 1 : ℕ) : ℝ) ^ θ := by
  rcases n with ( _ | _ | _ | n ) <;> norm_num [ Finset.sum_range_succ ] at *;
  simp +zetaDelta at *;
  rw [ Finset.sum_range_succ ];
  rw [ Real.div_rpow ] <;> try linarith;
  ring_nf
  convert le_refl _
  change (1 : ℝ) = (Nat.rawCast 1 : ℝ)
  simp [Nat.rawCast]

/-
PROBLEM
The key induction step: given a partition with m ≥ 3 points, find a good index,
remove that point, and bound the resulting error.

PROVIDED SOLUTION
Set m = π.pts.length, n = m - 1 (so n ≥ 2 since m ≥ 3).

Define U : Fin (n + 1) → ℝ by U(i) = π.pts.get ⟨i.val, by omega⟩ (note n+1 = m).
U is StrictMono by get_strictMono (with appropriate casting).
U(0) = a by get_first.
U(⟨n, _⟩) = b by get_last (since n = m-1).

Have IsSuperadditiveOn a b (young_control f g p q) from (isControlOn_young_control ...).1.
Since U(0) = a and U(⟨n,_⟩) = b, rewrite to get IsSuperadditiveOn (U 0) (U ⟨n,_⟩) ω.

Apply exists_good_index_of_superadditive with m := n, hm := 2 ≤ n (since n ≥ 2), to get:
  j, hjm : j + 2 ≤ n, and hj_bound : ω(U(j), U(j+2)) ≤ (2/(n-1)) * ω(a,b)

Note: j + 2 ≤ n means j + 2 ≤ m - 1, so j + 2 < m. Also n - 1 = m - 2.

Get ρ from eraseIdx_isPartition π (j := j) (hj : j + 2 < m).
This gives ρ.pts = π.pts.eraseIdx(j+1) and ρ.pts.length = m - 1.

By rsSum_eraseIdx_diff:
  π.rsSum f g - ρ.rsSum f g = (f(U(j+1)) - f(U(j))) * (g(U(j+2)) - g(U(j+1)))

So |π.rsSum f g - ρ.rsSum f g| = |f(U(j+1)) - f(U(j))| * |g(U(j+2)) - g(U(j+1))| (by abs_mul)

By abs_sub_mul_abs_sub_le_young_control_rpow (with u = U(j), v = U(j+1), w = U(j+2)):
  ≤ young_control(U(j), U(j+2))^θ where θ = 1/p + 1/q

We need U(j) ≤ U(j+1) ≤ U(j+2) (from StrictMono, these follow from j < j+1 < j+2).
We need FinitePVariationOn f (Set.Icc (U j) (U (j+2))) p and similarly for g: use
FinitePVariationOn.subinterval.
For the subinterval bounds, we need a ≤ U(j) and U(j+2) ≤ b, which follow from:
  a = U(0) ≤ U(j) (from StrictMono and 0 ≤ j)
  U(j+2) ≤ U(n) = b (from StrictMono and j+2 ≤ n)

So |π.rsSum - ρ.rsSum| ≤ young_control(U(j), U(j+2))^θ ≤ ((2/(n-1)) * W)^θ where W =
young_control(a,b).

Use Real.rpow_le_rpow: since 0 ≤ young_control(U(j),U(j+2)) ≤ (2/(n-1)) * W and θ ≥ 0:
  young_control(U(j), U(j+2))^θ ≤ ((2/(n-1)) * W)^θ

Then ((2/(n-1)) * W)^θ = (2/(n-1))^θ * W^θ by Real.mul_rpow (for nonneg factors).

And n - 1 = m - 2, so (2/(n-1))^θ = (2/(m-2))^θ.

Provide ρ with the length and bound properties.
-/
set_option linter.style.multiGoal false in
lemma young_loeve_induction_step (f g : ℝ → ℝ) {a b p q : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (_hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (_hab : a < b)
    (π : Partition a b)
    (hm : 3 ≤ π.pts.length) :
    ∃ (ρ : Partition a b),
      ρ.pts.length = π.pts.length - 1 ∧
      |π.rsSum f g - ρ.rsSum f g| ≤
        (2 / (π.pts.length - 2 : ℝ)) ^ (1 / p + 1 / q) *
        (young_control f g p q a b) ^ (1 / p + 1 / q) := by
  -- Apply the existence of a good index j to find such a ρ.
  obtain ⟨j, hjm, hj_bound⟩ : ∃ j : ℕ, ∃ hjm : j + 2 ≤ π.pts.length - 1,
    (young_control f g p q (π.pts.get ⟨j, by omega⟩) (π.pts.get ⟨j + 2, by omega⟩)) ≤
      (2 / (π.pts.length - 2 : ℝ)) * (young_control f g p q a b) := by
        have h_exists_good_index : ∃ j : ℕ, ∃ hjm : j + 2 ≤ π.pts.length - 1,
            (young_control f g p q (π.pts.get ⟨j, by omega⟩) (π.pts.get ⟨j + 2, by omega⟩)) ≤
              (2 / (π.pts.length - 2 : ℝ)) * (young_control f g p q a b) := by
          have h_superadditive : IsSuperadditiveOn a b (young_control f g p q) := by
            apply (isControlOn_young_control f g hp hq hf hg hfp hgq).left
          have h_exists_good_index : ∃ j : ℕ, ∃ hjm : j + 2 ≤ π.pts.length - 1,
            (young_control f g p q (π.pts.get ⟨j, by omega⟩) (π.pts.get ⟨j + 2, by omega⟩)) ≤
              (2 / (π.pts.length - 2 : ℝ)) * (young_control f g p q a b) := by
            have h_mono : StrictMono (fun i : Fin π.pts.length => π.pts.get i) := by
              exact?
            convert exists_good_index_of_superadditive
              (show 2 ≤ π.pts.length - 1 from Nat.le_sub_one_of_lt hm) _ _ using 1
            rotate_left;
            use fun s t => young_control f g p q s t;
            use fun i => π.pts.get ⟨ i, by omega ⟩;
            · exact fun i j hij => h_mono hij;
            · convert h_superadditive using 1;
              · exact get_first π ( by linarith );
              · exact get_last π ( by linarith );
            · congr! 3;
              congr! 2;
              · rw [ Nat.cast_sub ] <;> push_cast <;> ring ; linarith;
              · congr! 1;
                · exact Eq.symm ( get_first π ( by linarith ) );
                · exact Eq.symm ( get_last π ( by linarith ) );
          exact h_exists_good_index;
        exact h_exists_good_index;
  -- By definition of `Partition.eraseIdx`, we can construct `ρ` with the desired properties.
  obtain ⟨ρ, hρ⟩ :
      ∃ ρ : Partition a b,
        ρ.pts = π.pts.eraseIdx (j + 1) ∧ ρ.pts.length = π.pts.length - 1 := by
    exact eraseIdx_isPartition π ( by omega )
  generalize_proofs at *; (
  -- By definition of `Partition.rsSum`, we can write the difference as:
  have h_diff :
      |π.rsSum f g - ρ.rsSum f g| =
        |f (π.pts.get ⟨j + 1, by omega⟩) - f (π.pts.get ⟨j, by omega⟩)| *
          |g (π.pts.get ⟨j + 2, by omega⟩) - g (π.pts.get ⟨j + 1, by omega⟩)| := by
    rw [ ← abs_mul ] ; rw [ rsSum_eraseIdx_diff ] ; aesop;
  generalize_proofs at *; (
  -- Apply the bound from `abs_sub_mul_abs_sub_le_young_control_rpow`.
  have h_bound :
      |f (π.pts.get ⟨j + 1, by omega⟩) - f (π.pts.get ⟨j, by omega⟩)| *
          |g (π.pts.get ⟨j + 2, by omega⟩) - g (π.pts.get ⟨j + 1, by omega⟩)| ≤
        (young_control f g p q
          (π.pts.get ⟨j, by omega⟩) (π.pts.get ⟨j + 2, by omega⟩)) ^ (1 / p + 1 / q) := by
    have h_mono : StrictMono (fun i : Fin π.pts.length => π.pts.get i) := get_strictMono π
    apply abs_sub_mul_abs_sub_le_young_control_rpow f g hp hq
      (h_mono.monotone (Nat.le_succ _))
      (h_mono.monotone (Nat.le_succ _)) <;> generalize_proofs at *
    · apply_rules [FinitePVariationOn.subinterval]
      · exact le_trans
          (by linarith [get_first π (by linarith)])
          (h_mono.monotone (Nat.zero_le _))
      · have h_last : π.pts.get ⟨π.pts.length - 1, by omega⟩ = b := by
          exact get_last π (by linarith) |> fun h => h.trans (by aesop)
        have h_le :
            π.pts.get ⟨j + 2, by omega⟩ ≤ π.pts.get ⟨π.pts.length - 1, by omega⟩ := by
          exact h_mono.monotone (show j + 2 ≤ π.pts.length - 1 by omega)
        linarith
    · apply_rules [FinitePVariationOn.subinterval]
      · exact le_trans
          (by linarith [get_first π (by linarith)])
          (h_mono.monotone (Nat.zero_le _))
      · have h_last : π.pts.get ⟨π.pts.length - 1, by omega⟩ = b := by
          exact get_last π (by linarith) |> fun h => h.trans (by aesop)
        have h_le :
            π.pts.get ⟨j + 2, by omega⟩ ≤ π.pts.get ⟨π.pts.length - 1, by omega⟩ := by
          exact h_mono.monotone (show j + 2 ≤ π.pts.length - 1 by omega)
        linarith
  generalize_proofs at *; (
  refine ⟨ ρ, hρ.2, h_diff.symm ▸ h_bound.trans ?_ ⟩
  generalize_proofs at *; (
  rw [← Real.mul_rpow] <;>
    try
      linarith [show (0 : ℝ) ≤ 2 / (π.pts.length - 2) by
        exact div_nonneg zero_le_two (sub_nonneg_of_le <| mod_cast by linarith)]
  · exact Real.rpow_le_rpow
      (by
        exact le_trans (by norm_num)
          (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
      hj_bound (by positivity)
  · exact young_control_nonneg f g p q a b))))

lemma young_loeve_bound_aux (f g : ℝ → ℝ) {a b p q : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (hab : a < b)
    (π : Partition a b) :
    |f a * (g b - g a) - π.rsSum f g| ≤
      (2 ^ (1 / p + 1 / q) *
        ∑ k ∈ Finset.range (π.pts.length - 2),
          1 / ((k + 1 : ℕ) : ℝ) ^ (1 / p + 1 / q)) *
      (young_control f g p q a b) ^ (1 / p + 1 / q) := by
  set θ := 1 / p + 1 / q with hθ_def
  set W := young_control f g p q a b with hW_def
  suffices h_ind : ∀ n, ∀ ρ : Partition a b, ρ.pts.length = n →
      |f a * (g b - g a) - ρ.rsSum f g| ≤
        (2 ^ θ * ∑ k ∈ Finset.range (n - 2), 1 / ((k + 1 : ℕ) : ℝ) ^ θ) * W ^ θ by
    exact h_ind π.pts.length π rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro ρ hρ_len
  by_cases hn : n ≤ 2
  · -- Base case: n ≤ 2. Since n ≥ 2 (from pts_length_ge_two), n = 2.
    have hn2 : n = 2 := by
      have := pts_length_ge_two ρ hab; omega
    subst hn2
    rw [rsSum_of_length_two f g ρ hρ_len, sub_self, abs_zero]
    simp
  · -- Inductive case: n ≥ 3.
    push_neg at hn
    obtain ⟨σ, hσ_len, hσ_bound⟩ := young_loeve_induction_step f g hp hq hpq hf hg hfp hgq hab ρ
      (by omega)
    have hσ_len' : σ.pts.length = n - 1 := by omega
    have hih := ih (n - 1) (by omega) σ hσ_len'
    calc |f a * (g b - g a) - ρ.rsSum f g|
        = |(f a * (g b - g a) - σ.rsSum f g) + (σ.rsSum f g - ρ.rsSum f g)| := by ring_nf
      _ ≤ |f a * (g b - g a) - σ.rsSum f g| + |σ.rsSum f g - ρ.rsSum f g| :=
          abs_add_le _ _
      _ ≤ |f a * (g b - g a) - σ.rsSum f g| + |ρ.rsSum f g - σ.rsSum f g| := by
          rw [abs_sub_comm (σ.rsSum f g) (ρ.rsSum f g)]
      _ ≤ (2 ^ θ * ∑ k ∈ Finset.range ((n - 1) - 2), 1 / ((k + 1 : ℕ) : ℝ) ^ θ) * W ^ θ +
          (2 / (n - 2 : ℝ)) ^ θ * W ^ θ := by
          gcongr
          rwa [hρ_len] at hσ_bound
      _ = (2 ^ θ * ∑ k ∈ Finset.range ((n - 1) - 2), 1 / ((k + 1 : ℕ) : ℝ) ^ θ +
          (2 / (n - 2 : ℝ)) ^ θ) * W ^ θ := by ring
      _ ≤ (2 ^ θ * ∑ k ∈ Finset.range (n - 2), 1 / ((k + 1 : ℕ) : ℝ) ^ θ) * W ^ θ := by
          have h3n : 3 ≤ n := by omega
          have := partial_sum_step h3n θ
          nlinarith [Real.rpow_nonneg (young_control_nonneg f g p q a b) θ]

/-
PROBLEM
The partial sum of the Young-Loève series is at most the full constant.

PROVIDED SOLUTION
young_loeve_constant p q = 2^θ * ∑' n, 1/((n+1):ℝ)^θ where θ = 1/p+1/q.

The finite partial sum ∑ k ∈ Finset.range n, 1/((k+1):ℝ)^θ ≤ ∑' n, 1/((n+1):ℝ)^θ by sum_le_tsum (the
partial sum of a nonneg series is ≤ the tsum). The series is summable by
summable_young_loeve_constant_series.

Then multiply both sides by 2^θ ≥ 0.

Key lemmas: sum_le_tsum, summable_young_loeve_constant_series.
-/
lemma partial_sum_le_young_loeve_constant {p q : ℝ} (hpq : 1 / p + 1 / q > 1) (n : ℕ) :
    2 ^ (1 / p + 1 / q) *
      ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℝ) ^ (1 / p + 1 / q) ≤
    young_loeve_constant p q := by
  refine mul_le_mul_of_nonneg_left ?_ ( by positivity );
  convert Summable.sum_le_tsum _ _ _;
  all_goals try infer_instance;
  · exact fun _ _ => by positivity;
  · simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 hpq

/-
PROBLEM
If `f` and `g` are continuous on `[a, b]`, have finite `p`- and `q`-variation, and satisfy
`1 / p + 1 / q > 1`, then the error between `f a * (g b - g a)` and every Riemann-Stieltjes sum
of `f dg` over partitions of `[a, b]` is controlled by `young_loeve_constant p q` times
`(young_control f g p q a b) ^ (1 / p + 1 / q)`.

PROVIDED SOLUTION
Case split on whether a = b or a < b.

If a = b: rsSum = 0 by rsSum_of_eq, and f a * (g a - g a) = 0, so LHS = 0, which is ≤ the RHS since
young_loeve_constant_nonneg and young_control_nonneg give RHS ≥ 0.

If a ≤ b but not a = b, then a < b. Use young_loeve_bound_aux to get:
|f a * (g b - g a) - π.rsSum f g| ≤ (2^θ * ∑ k ∈ range(n-2), ...) * W^θ

Then use partial_sum_le_young_loeve_constant to bound the partial sum constant by
young_loeve_constant:
(2^θ * ∑...) ≤ young_loeve_constant

Finally multiply by W^θ ≥ 0 (since young_control_nonneg and rpow_nonneg).

But wait, we also need a ≤ b for the partition to exist. Actually, if a > b, the partition structure
requires head? = some a and getLast? = some b, but the chain (· < ·) would require all elements to
be strictly increasing. If a > b, then the list would need its first element ≤ last element (from
transitivity), but head is a > b = last, contradiction. So a ≤ b is implicit.

Actually for the degenerate case: if a > b, then from the chain condition and first/last, the list
must be empty or have contradictory elements. We can handle this with pts_ne_nil showing the list is
nonempty, then showing a ≤ b from the partition structure. But it's easier to just handle both a = b
and a < b, extracting a ≤ b from the partition.

Simplest approach: Use `le_or_lt a b` (or just `eq_or_lt_of_le` after establishing a ≤ b). Actually,
let me use `lt_or_eq_of_le` on a ≤ b (which follows from the partition). Or just: by_cases h : a =
b.

Case a = b: subst h; simp [rsSum_of_eq]; apply mul_nonneg; exact young_loeve_constant_nonneg hp hq
hpq; exact Real.rpow_nonneg (young_control_nonneg f g p q a a) _

Case a ≠ b: Then a < b (since partition implies a ≤ b). Apply young_loeve_bound_aux, then use
partial_sum_le_young_loeve_constant with mul_le_mul_of_nonneg_right.
-/
set_option linter.style.multiGoal false in
theorem young_loeve_bound (f g : ℝ → ℝ) {a b p q : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (π : Partition a b) :
    |f a * (g b - g a) - π.rsSum f g| ≤
      young_loeve_constant p q * (young_control f g p q a b) ^ (1 / p + 1 / q) := by
  by_cases h : a = b;
  · -- When `a = b`, the interval is a single point, so the
    -- Riemann-Stieltjes sum is zero.
    have h_zero : π.rsSum f g = 0 := by
      convert rsSum_of_eq f g _;
      swap;
      exact ⟨π.pts, π.sorted, h ▸ π.first, π.last⟩;
      congr! 1;
    -- Since $a = b$, the RS sum is zero, so the absolute
    -- difference is zero.
    simp [h_zero, h];
    apply mul_nonneg; exact?; exact Real.rpow_nonneg (young_control_nonneg f g p q b b) _;
  · by_cases h' : a < b;
    · have := young_loeve_bound_aux f g hp hq hpq hf hg hfp hgq h' π;
      exact this.trans <|
        mul_le_mul_of_nonneg_right
          (by simpa using partial_sum_le_young_loeve_constant hpq (π.pts.length - 2))
          (Real.rpow_nonneg (young_control_nonneg f g p q a b) _)
    · have h_empty : π.pts = [a] := by
        have h_empty : ∀ x ∈ π.pts, x = a := by
          have h_empty : ∀ x ∈ π.pts, a ≤ x ∧ x ≤ b := by
            intro x hx
            have h_sorted : List.IsChain (· < ·) π.pts := π.sorted
            have h_first : π.pts.head? = some a := π.first
            have h_last : π.pts.getLast? = some b := π.last
            exact
              ⟨le_of_mem_chain_head h_sorted h_first hx,
                le_of_mem_chain_getLast h_sorted h_last hx⟩
          exact fun x hx => by linarith [ h_empty x hx ] ;
        rcases π with ⟨ _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩, h₁, h₂, h₃ ⟩ <;> aesop;
      have := π.last; aesop;

/-- Compare Riemann-Stieltjes sums over two partitions by inserting the common refinement as an
intermediate term and applying the triangle inequality. -/
theorem abs_rsSum_sub_le_common_refinement (π ρ : Partition a b)
    (f g : ℝ → ℝ) :
    |π.rsSum f g - ρ.rsSum f g| ≤
      |π.rsSum f g - (common_refinement π ρ).rsSum f g| +
        |ρ.rsSum f g - (common_refinement π ρ).rsSum f g| := by
  let τ := common_refinement π ρ
  calc
    |π.rsSum f g - ρ.rsSum f g|
      = |(π.rsSum f g - τ.rsSum f g) + (τ.rsSum f g - ρ.rsSum f g)| := by
          congr
          ring
    _ ≤ |π.rsSum f g - (common_refinement π ρ).rsSum f g| +
          |τ.rsSum f g - ρ.rsSum f g| := by
        simpa [τ] using abs_add_le (π.rsSum f g - τ.rsSum f g) (τ.rsSum f g - ρ.rsSum f g)
    _ = |π.rsSum f g - (common_refinement π ρ).rsSum f g| +
          |ρ.rsSum f g - (common_refinement π ρ).rsSum f g| := by
        simp [τ, abs_sub_comm]

/-
PROBLEM
rsSum.go is additive: splitting at a point decomposes the sum.

PROVIDED SOLUTION
Since s ∈ l, we can decompose l = l₁ ++ s :: l₂ (by List.mem_iff_get or induction on l). Then by
rsSum_go_append (already proved in the file), rsSum.go f g x l = rsSum.go f g x (l₁ ++ [s]) +
rsSum.go f g s l₂.

Use List.mem_iff_append or induction on l to find the split point, then apply rsSum_go_append.
-/
lemma rsSum_go_split_at (f g : ℝ → ℝ) (x : ℝ) (l : List ℝ) {s : ℝ}
    (hs : s ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ s :: l₂ ∧
      rsSum.go f g x l = rsSum.go f g x (l₁ ++ [s]) + rsSum.go f g s l₂ := by
  obtain ⟨l₁, l₂, hl₁l₂⟩ : ∃ l₁ l₂, l = l₁ ++ s :: l₂ := by
    exact?;
  refine ⟨ l₁, l₂, hl₁l₂, ?_ ⟩;
  convert rsSum_go_append f g x s l₁ l₂ using 1 ; aesop

/-- If `ρ` refines `π` with `π = [u₀, u₁]` (a single interval), then
|rsSum(π) - rsSum(ρ)| = |f(u₀)*(g(u₁)-g(u₀)) - rsSum(ρ)| ≤ ylc * yc(u₀,u₁)^θ
by young_loeve_bound. -/
lemma abs_rsSum_sub_of_refines_single_interval (f g : ℝ → ℝ)
    {s t p q : ℝ} (_hst : s ≤ t)
    (ρ : Partition s t)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc s t)) (hg : ContinuousOn g (Set.Icc s t))
    (hfp : FinitePVariationOn f (Set.Icc s t) p)
    (hgq : FinitePVariationOn g (Set.Icc s t) q) :
    |f s * (g t - g s) - ρ.rsSum f g| ≤
      young_loeve_constant p q * (young_control f g p q s t) ^ (1 / p + 1 / q) := by
  exact young_loeve_bound f g hp hq hpq hf hg hfp hgq ρ

lemma tail_partition (π : Partition a b) {c : ℝ} (hπ_len : 2 < π.pts.length)
    (hc : π.pts.get ⟨1, by omega⟩ = c) :
    ∃ π' : Partition c b, π'.pts = π.pts.tail ∧ π'.pts.length = π.pts.length - 1 := by
  use ⟨π.pts.tail, by
    exact π.sorted.tail;, by
    rcases n : π.pts with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> aesop, by
    rcases π with ⟨ _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩, h₁, h₂, h₃ ⟩ <;> aesop⟩
  generalize_proofs at *;
  aesop

lemma rsSum_cons (π : Partition a b) (f g : ℝ → ℝ)
    (hπ_len : 2 < π.pts.length) :
    π.rsSum f g = f a * (g (π.pts.get ⟨1, by omega⟩) - g a) +
      rsSum.go f g (π.pts.get ⟨1, by omega⟩) π.pts.tail.tail := by
  generalize_proofs at *;
  rcases π with ⟨ pts, hpts ⟩;
  rcases pts with ( _ | ⟨ a, _ | ⟨ b, pts ⟩ ⟩ ) <;> norm_num at *;
  cases ‹ ( a :: b :: pts ).head? = some _› ; aesop

lemma rsSum_split (ρ : Partition a b) (f g : ℝ → ℝ) {c : ℝ}
    (hc : c ∈ ρ.pts) (hac : a ≤ c) (_hcb : c ≤ b) :
    ∃ (ρ₁ : Partition a c) (ρ₂ : Partition c b),
      ρ.rsSum f g = ρ₁.rsSum f g + ρ₂.rsSum f g ∧
      (∀ x ∈ ρ₁.pts, x ∈ ρ.pts) ∧
      (∀ x ∈ ρ₂.pts, x ∈ ρ.pts) ∧
      (∀ x ∈ ρ.pts, c ≤ x → x ∈ ρ₂.pts) := by
  rcases ρ with ⟨pts, hpts⟩;
  obtain ⟨l₁, l₂, hl₁l₂⟩ : ∃ l₁ l₂, pts = l₁ ++ c :: l₂ := by
    exact?;
  use ⟨l₁ ++ [c], by
    grind, by
    grind, by
    grind⟩, ⟨c :: l₂, by
    grind, by
    rfl, by
    grind +ring⟩
  generalize_proofs at *;
  unfold Partition.rsSum;
  cases l₁ <;> simp_all +decide [ rsSum.go ];
  refine ⟨ ?_, ?_, ?_, ?_ ⟩;
  · exact?;
  · grind;
  · grind;
  · grind

lemma refines_tail (π ρ : Partition a b) (hρ : ρ.Refines π)
    (hπ_len : 2 < π.pts.length)
    {c : ℝ} (hc : π.pts.get ⟨1, by omega⟩ = c)
    (π' : Partition c b) (hπ' : π'.pts = π.pts.tail)
    (ρ' : Partition c b) (hρ'_pts : ∀ x ∈ ρ.pts, c ≤ x → x ∈ ρ'.pts) :
    ρ'.Refines π' := by
  intro x hx
  have hx_π : x ∈ π.pts := by
    exact List.mem_of_mem_tail ( hπ'.symm ▸ hx );
  have := le_of_mem_chain_head ( show List.IsChain ( · < · ) ( List.tail π.pts ) from by
                                  exact π.sorted.tail)
    (show List.head? (List.tail π.pts) = some c from by
      rcases n : π.pts with (_ | ⟨a, _ | ⟨b, l⟩⟩) <;> aesop)
    (by
      grind +ring : x ∈ List.tail π.pts)
  aesop

lemma young_control_superadditive (f g : ℝ → ℝ) (p q a c b : ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (hac : a ≤ c) (hcb : c ≤ b) :
    young_control f g p q a c + young_control f g p q c b ≤ young_control f g p q a b := by
  have := isControlOn_young_control f g hp hq hf hg hfp hgq;
  convert this.1.2 _ _ _ _ <;> linarith;

lemma rsSum_tail {c : ℝ} {l : List ℝ} (π' : Partition c b) (f g : ℝ → ℝ)
    (hpts : π'.pts = l)
    : π'.rsSum f g = rsSum.go f g c l.tail := by
  have h_rsSum_def : π'.rsSum f g = rsSum.go f g (π'.pts.head!) (π'.pts.tail) := by
    unfold Partition.rsSum; aesop;
  have := π'.first; ( have := π'.last; ( cases l <;> aesop; ) )

lemma finRange_sum_cons (π : Partition a b) {c : ℝ} (π' : Partition c b)
    (F : ℝ → ℝ → ℝ)
    (hπ_len : 2 < π.pts.length)
    (hc : π.pts.get ⟨1, by omega⟩ = c)
    (hπ' : π'.pts = π.pts.tail) :
    ((List.finRange (π.pts.length - 1)).map (fun i =>
      F (π.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
        (π.pts.get ⟨i.1 + 1, by omega⟩))).sum =
    F a c +
    ((List.finRange (π'.pts.length - 1)).map (fun i =>
      F (π'.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
        (π'.pts.get ⟨i.1 + 1, by omega⟩))).sum := by
  generalize_proofs at *;
  rcases π with ⟨ _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ⟩ <;> simp_all +decide [ List.finRange_succ ];
  simp_all +decide [ List.finRange ];
  congr! 2;
  grind +ring

set_option linter.style.multiGoal false in
lemma abs_rsSum_sub_le_sum_local (π ρ : Partition a b) (f g : ℝ → ℝ)
    {p q : ℝ} (hρ : ρ.Refines π)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q) :
    |π.rsSum f g - ρ.rsSum f g| ≤
      young_loeve_constant p q *
        ((List.finRange (π.pts.length - 1)).map (fun i =>
          (young_control f g p q
            (π.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
            (π.pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q))).sum := by
  set θ := 1 / p + 1 / q
  set ylc := young_loeve_constant p q
  suffices h_ind : ∀ (n : ℕ) (a b : ℝ) (π : Partition a b), π.pts.length = n →
      ∀ (ρ : Partition a b), ρ.Refines π →
      ContinuousOn f (Set.Icc a b) → ContinuousOn g (Set.Icc a b) →
      FinitePVariationOn f (Set.Icc a b) p → FinitePVariationOn g (Set.Icc a b) q →
      |π.rsSum f g - ρ.rsSum f g| ≤ ylc *
        ((List.finRange (π.pts.length - 1)).map (fun i =>
          (young_control f g p q
            (π.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
            (π.pts.get ⟨i.1 + 1, by omega⟩)) ^ θ)).sum by
    exact h_ind π.pts.length a b π rfl ρ hρ hf hg hfp hgq
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro a b π hπ_len ρ hρ hf hg hfp hgq
  by_cases hn : n ≤ 2
  · -- Base case: n ≤ 2
    interval_cases n <;> simp_all +decide [ List.finRange ];
    · exact absurd hπ_len ( pts_ne_nil π ) |> fun h => False.elim h;
    · have hab : a = b := by
        have := π.first; have := π.last; ( rw [ List.length_eq_one_iff ] at hπ_len; aesop; )
      subst hab
      simp [rsSum_of_eq]
    · have hπ_rsSum : π.rsSum f g = f a * (g b - g a) := by
        exact?;
      convert young_loeve_bound f g hp hq hpq hf hg hfp hgq ρ using 1
      aesop (simp_config := { singlePass := true })
      have := π.first; have := π.last; rw [ List.length_eq_two ] at hπ_len; aesop;
  · -- Inductive case: n ≥ 3
    push_neg at hn
    have hπ_len3 : 3 ≤ π.pts.length := by omega
    set c := π.pts.get ⟨1, by omega⟩ with hc_def
    obtain ⟨π', hπ'_pts, hπ'_len⟩ := tail_partition π (by omega) rfl
    have h_mono := get_strictMono π
    have hac : a ≤ c := by
      have h0 := get_first π (by omega : 0 < π.pts.length)
      linarith [h_mono.monotone
        (show (⟨0, by omega⟩ : Fin π.pts.length) ≤ ⟨1, by omega⟩ from Nat.zero_le 1)]
    have hcb : c ≤ b := by
      have hlast := get_last π (by omega : 0 < π.pts.length)
      have h1n : (⟨1, by omega⟩ : Fin π.pts.length) ≤ ⟨π.pts.length - 1, by omega⟩ := by
        change 1 ≤ π.pts.length - 1; omega
      linarith [h_mono.monotone h1n]
    have hc_mem : c ∈ ρ.pts := by
      apply hρ
      exact List.getElem_mem (by omega : 1 < π.pts.length)
    obtain ⟨ρ₁, ρ₂, hρ_split, hρ₁_mem, hρ₂_mem, hρ₂_ge⟩ :=
      rsSum_split ρ f g hc_mem hac hcb
    have hρ₂_ref : ρ₂.Refines π' :=
      refines_tail π ρ hρ (by omega) rfl π' hπ'_pts ρ₂ hρ₂_ge
    have hπ_decomp : π.rsSum f g = f a * (g c - g a) + π'.rsSum f g := by
      rw [rsSum_cons π f g (by omega)]
      congr 1
      exact (rsSum_tail π' f g hπ'_pts).symm
    calc |π.rsSum f g - ρ.rsSum f g|
        = |(f a * (g c - g a) + π'.rsSum f g) - (ρ₁.rsSum f g + ρ₂.rsSum f g)| := by
          rw [hπ_decomp, hρ_split]
      _ = |(f a * (g c - g a) - ρ₁.rsSum f g) + (π'.rsSum f g - ρ₂.rsSum f g)| := by ring_nf
      _ ≤ |f a * (g c - g a) - ρ₁.rsSum f g| + |π'.rsSum f g - ρ₂.rsSum f g| := abs_add_le _ _
      _ ≤ ylc * (young_control f g p q a c) ^ θ +
          ylc * ((List.finRange (π'.pts.length - 1)).map (fun i =>
            (young_control f g p q
              (π'.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
              (π'.pts.get ⟨i.1 + 1, by omega⟩)) ^ θ)).sum := by
          gcongr
          · exact young_loeve_bound f g hp hq hpq
              (hf.mono (Set.Icc_subset_Icc le_rfl hcb))
              (hg.mono (Set.Icc_subset_Icc le_rfl hcb))
              (FinitePVariationOn.subinterval f le_rfl hcb hfp)
              (FinitePVariationOn.subinterval g le_rfl hcb hgq) ρ₁
          · exact ih (n - 1) (by omega) c b π' (by omega) ρ₂ hρ₂_ref
              (hf.mono (Set.Icc_subset_Icc hac le_rfl))
              (hg.mono (Set.Icc_subset_Icc hac le_rfl))
              (FinitePVariationOn.subinterval f hac le_rfl hfp)
              (FinitePVariationOn.subinterval g hac le_rfl hgq)
      _ = ylc * ((young_control f g p q a c) ^ θ +
          ((List.finRange (π'.pts.length - 1)).map (fun i =>
            (young_control f g p q
              (π'.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
              (π'.pts.get ⟨i.1 + 1, by omega⟩)) ^ θ)).sum) := by ring
      _ = ylc * ((List.finRange (π.pts.length - 1)).map (fun i =>
            (young_control f g p q
              (π.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
              (π.pts.get ⟨i.1 + 1, by omega⟩)) ^ θ)).sum := by
          congr 1
          exact (finRange_sum_cons π π' (fun s t => (young_control f g p q s t) ^ θ)
            (by omega) rfl hπ'_pts).symm

lemma sum_rpow_le_max_rpow_mul_sum {l : List ℝ} {θ : ℝ} (hθ : 1 < θ)
    (hl : ∀ x ∈ l, 0 ≤ x) :
    (l.map (· ^ θ)).sum ≤ (l.map (· ^ (θ - 1))).foldr max 0 * l.sum := by
  have h_ineq :
      ∀ x ∈ l, x ^ θ ≤ (List.foldr max 0 (List.map (fun x => x ^ (θ - 1)) l)) * x := by
    intro x hx
    rw [show x ^ θ = x ^ (θ - 1) * x by
      rw [← Real.rpow_add_one'] <;> norm_num <;> linarith [hl x hx]]
    exact mul_le_mul_of_nonneg_right (by induction l <;> aesop) (hl x hx)
  convert List.sum_le_sum h_ineq using 1;
  rw [ List.sum_map_mul_left ];
  norm_num

lemma sum_le_of_superadditive_seq (ω : ℝ → ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hω_nn : ∀ i j, i ≤ j → j ≤ n → 0 ≤ ω (u i) (u j))
    (hω_super : ∀ i j k, i ≤ j → j ≤ k → k ≤ n →
      ω (u i) (u j) + ω (u j) (u k) ≤ ω (u i) (u k)) :
    ∑ i ∈ Finset.range n, ω (u i) (u (i + 1)) ≤ ω (u 0) (u n) := by
  induction n <;> simp_all +decide [ Finset.sum_range_succ ];
  rename_i n ih
  exact le_trans
    (add_le_add
      (ih (fun i j hij hj => hω_nn i j hij (by linarith))
        (fun i j k hij hjk hk => hω_super i j k hij hjk (by linarith)))
      le_rfl)
    (hω_super _ _ _ (by linarith) (by linarith) (by linarith))

set_option linter.style.refine false in
lemma sum_young_control_le (π : Partition a b) (f g : ℝ → ℝ) (p q : ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q) :
    ((List.finRange (π.pts.length - 1)).map (fun i =>
      young_control f g p q
        (π.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
        (π.pts.get ⟨i.1 + 1, by omega⟩))).sum ≤ young_control f g p q a b := by
  set n := π.pts.length - 1
  set u : ℕ → ℝ := fun i => if h : i < π.pts.length then π.pts.get ⟨i, h⟩ else b
  have h_list_eq_finset : ((List.finRange n).map (fun i =>
      young_control f g p q
        (π.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
        (π.pts.get ⟨i.1 + 1, by omega⟩))).sum =
      ∑ i ∈ Finset.range n, young_control f g p q (u i) (u (i + 1)) := by
    rw [ Finset.sum_range ]
    generalize_proofs at *;
    refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop
  rw [h_list_eq_finset]
  have h_len : 0 < π.pts.length := List.length_pos_iff.mpr (pts_ne_nil π)
  have hu0 : u 0 = a := by
    simp only [u, show (0 : ℕ) < π.pts.length from h_len, dite_true]
    exact get_first π h_len
  have hun : u n = b := by
    have h_lt : n < π.pts.length := Nat.sub_lt h_len Nat.one_pos
    simp only [u, show n < π.pts.length from h_lt, dite_true]
    exact get_last π h_len
  rw [← hu0, ← hun]
  apply sum_le_of_superadditive_seq
  · intros i j _ _; exact young_control_nonneg f g p q _ _
  · intro i j k hij hjk hkn
    have h_mono := get_strictMono π
    have hin : i < π.pts.length := by omega
    have hjn : j < π.pts.length := by omega
    have hkn' : k < π.pts.length := by omega
    have hui : u i = π.pts.get ⟨i, hin⟩ := by
      simp only [u, show i < π.pts.length from hin, dite_true]
    have huj : u j = π.pts.get ⟨j, hjn⟩ := by
      simp only [u, show j < π.pts.length from hjn, dite_true]
    have huk : u k = π.pts.get ⟨k, hkn'⟩ := by
      simp only [u, show k < π.pts.length from hkn', dite_true]
    rw [hui, huj, huk]
    have huij : π.pts.get ⟨i, hin⟩ ≤ π.pts.get ⟨j, hjn⟩ :=
      h_mono.monotone (show (⟨i, hin⟩ : Fin π.pts.length) ≤ ⟨j, hjn⟩ from hij)
    have hujk : π.pts.get ⟨j, hjn⟩ ≤ π.pts.get ⟨k, hkn'⟩ :=
      h_mono.monotone (show (⟨j, hjn⟩ : Fin π.pts.length) ≤ ⟨k, hkn'⟩ from hjk)
    have huia : a ≤ π.pts.get ⟨i, hin⟩ := by
      have h0 := get_first π (by omega : 0 < π.pts.length)
      linarith [h_mono.monotone
        (show (⟨0, by omega⟩ : Fin π.pts.length) ≤ ⟨i, hin⟩ from Nat.zero_le i)]
    have hukb : π.pts.get ⟨k, hkn'⟩ ≤ b := by
      have hlast := get_last π (by omega : 0 < π.pts.length)
      linarith [h_mono.monotone
        (show (⟨k, hkn'⟩ : Fin π.pts.length) ≤ ⟨π.pts.length - 1, by omega⟩ from by
          change k ≤ π.pts.length - 1
          omega)]
    exact young_control_superadditive f g p q
      (π.pts.get ⟨i, hin⟩) (π.pts.get ⟨j, hjn⟩) (π.pts.get ⟨k, hkn'⟩)
      hp hq
      (hf.mono (Set.Icc_subset_Icc huia hukb))
      (hg.mono (Set.Icc_subset_Icc huia hukb))
      (FinitePVariationOn.subinterval f huia hukb hfp)
      (FinitePVariationOn.subinterval g huia hukb hgq)
      huij hujk

set_option linter.style.refine false in
/-- If `ρ` refines `π`, then the difference between the two Riemann-Stieltjes sums is bounded by
the maximum local Young-control factor over the intervals of `π`, times the Young-Loève constant,
times the total control on `[a, b]`. -/
theorem abs_rsSum_sub_le_of_refines (π ρ : Partition a b) (f g : ℝ → ℝ)
    {p q : ℝ} (hρ : ρ.Refines π)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q) :
    |π.rsSum f g - ρ.rsSum f g| ≤
      let ωmax : ℝ :=
        ((List.finRange (π.pts.length - 1)).map fun i =>
          (young_control f g p q
            (π.pts.get ⟨i.1, by
              exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)
            ⟩)
            (π.pts.get ⟨i.1 + 1, by
              omega
            ⟩)) ^ (1 / p + 1 / q - 1)).foldr max 0
      ωmax * young_loeve_constant p q * young_control f g p q a b := by
  refine le_trans (abs_rsSum_sub_le_sum_local π ρ f g hρ hp hq hpq hf hg hfp hgq) ?_
  rw [mul_assoc, mul_comm]
  rw [← mul_assoc, mul_comm]
  refine' le_trans _ <|
    mul_le_mul_of_nonneg_left (sum_young_control_le π f g p q hp hq hf hg hfp hgq) ?_
  · rw [mul_right_comm]
    rw [mul_comm]
    gcongr
    · exact young_loeve_constant_nonneg hp hq hpq
    · convert sum_rpow_le_max_rpow_mul_sum
        (l := (List.finRange (π.pts.length - 1)).map fun i =>
          young_control f g p q
            (π.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
            (π.pts.get ⟨i.1 + 1, by omega⟩))
        (θ := 1 / p + 1 / q) hpq ?_ using 1
      · rw [List.map_map]
        rfl
      · rw [List.map_map]
        rfl
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact young_control_nonneg _ _ _ _ _ _
  · refine mul_nonneg ?_ ?_
    · induction (List.finRange (π.pts.length - 1)) <;> aesop
    · exact young_loeve_constant_nonneg hp hq hpq

/-- The mesh size of a partition is the maximum length of its consecutive subintervals. -/
noncomputable def mesh (π : Partition a b) : ℝ :=
  ((List.finRange (π.pts.length - 1)).map fun i =>
    π.pts.get ⟨i.1 + 1, by
      omega
    ⟩ - π.pts.get ⟨i.1, by
      exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)
    ⟩).foldr max 0

/-- A sequence of partitions has vanishing mesh size if the mesh tends to `0`. -/
def HasVanishingMeshSize (π : ℕ → Partition a b) : Prop :=
  Tendsto (fun n => (π n).mesh) atTop (𝓝 0)

set_option linter.style.refine false in
set_option linter.style.multiGoal false in
lemma exists_vanishing_mesh_sequence (a b : ℝ) (hab : a ≤ b) :
    ∃ π : ℕ → Partition a b, HasVanishingMeshSize π := by
  by_contra! h_contra;
  obtain ⟨π, hπ⟩ : ∃ π : ℕ → Partition a b, HasVanishingMeshSize π := by
    by_cases h_eq : a = b;
    · refine' ⟨ fun _ => ⟨ [ a ], _, _, _ ⟩, _ ⟩ <;> norm_num [ h_eq ];
      unfold HasVanishingMeshSize; aesop;
    · -- For `a < b`, use the uniform partitions of `[a, b]`.
      use fun n =>
        ⟨List.map (fun k : Fin (n + 2) => a + k.val * (b - a) / (n + 1))
            (List.finRange (n + 2)), by
        refine List.isChain_iff_getElem.mpr ?_
        simp +zetaDelta at *;
        exact fun i hi => by
          rw [div_lt_div_iff_of_pos_right (by positivity)]
          nlinarith
            [show (i : ℝ) + 1 ≤ n + 1 by
              norm_cast
              omega,
             sub_pos.mpr <| lt_of_le_of_ne hab h_eq], by
        norm_num [ List.finRange_succ ], by
        simp +decide [ List.finRange_succ ];
        induction n <;> simp_all +decide [ List.getLast? ];
        erw [ List.getLast_eq_getElem ] ; norm_num [ List.getElem_finRange ] ; ring;
        -- Combine like terms and simplify the expression.
        field_simp
        ring⟩
      generalize_proofs at *;
      refine' squeeze_zero_norm' _ _;
      use fun n => ( b - a ) / ( n + 1 );
      · refine Filter.eventually_atTop.mpr ⟨ 0, fun n hn => ?_ ⟩ ; norm_num [ Partition.mesh ];
        norm_num [ add_mul, div_sub_div_same ];
        induction n + 1 <;> simp_all +decide [ List.replicate ];
        · exact div_nonneg ( sub_nonneg.2 hab ) ( by positivity );
        · rw [abs_of_nonneg (by
            exact le_max_of_le_left (div_nonneg (sub_nonneg.mpr hab) (by positivity)))]
          exact max_le (by exact le_rfl) (by linarith [abs_le.mp ‹_›])
      · exact tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  exact h_contra π hπ

end Partition

lemma IsControlOn.uniform_diagonal_continuity {a b : ℝ} {ω : ℝ → ℝ → ℝ}
    (hω : IsControlOn a b ω) (_hab : a ≤ b) :
    ∀ ε > 0, ∃ δ > 0, ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b →
      s ≤ t → t - s ≤ δ → ω s t < ε := by
  intro ε hε
  by_contra! h
  have h' : ∀ n : ℕ, ∃ s t : ℝ,
      s ∈ Set.Icc a b ∧ t ∈ Set.Icc a b ∧ s ≤ t ∧ t - s ≤ 1 / (n + 1 : ℝ) ∧ ε ≤ ω s t := by
    intro n
    exact h (1 / (n + 1 : ℝ)) (by positivity)
  choose s t hs ht hst hdist hωge using h'
  have hdist0 : Tendsto (fun n => t n - s n) atTop (𝓝 0) := by
    refine squeeze_zero ?_ ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    · intro n
      exact sub_nonneg.mpr (hst n)
    · intro n
      exact hdist n
  have h_subseq : ∃ x ∈ Set.Icc a b, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => s (φ n)) atTop (𝓝 x) := by
    exact (isCompact_Icc (a := a) (b := b)).isSeqCompact fun n => hs n
  obtain ⟨x, hx, φ, hφmono, hφlim⟩ := h_subseq
  have hdistφ0 : Tendsto (fun n => t (φ n) - s (φ n)) atTop (𝓝 0) :=
    hdist0.comp hφmono.tendsto_atTop
  have htφlim : Tendsto (fun n => t (φ n)) atTop (𝓝 x) := by
    have hsum := hφlim.add hdistφ0
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  have hωlim := hω.2.2 hx
    (s := fun n => s (φ n)) (t := fun n => t (φ n))
    (fun n => ⟨(hs (φ n)).1, hst (φ n)⟩)
    (fun n => ⟨hst (φ n), (ht (φ n)).2⟩)
    hφlim htφlim
  have : ε ≤ 0 := by
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hωlim (fun n => hωge (φ n))
  linarith

namespace Partition

variable {a b : ℝ}

lemma le_of_partition (π : Partition a b) : a ≤ b := by
  exact le_of_mem_chain_head π.sorted π.first (List.mem_of_mem_getLast? π.last)

lemma mem_Icc_of_mem_pts (π : Partition a b) {x : ℝ} (hx : x ∈ π.pts) :
    x ∈ Set.Icc a b := by
  exact ⟨le_of_mem_chain_head π.sorted π.first hx, le_of_mem_chain_getLast π.sorted π.last hx⟩

lemma get_mem_Icc (π : Partition a b) (i : Fin π.pts.length) :
    π.pts.get i ∈ Set.Icc a b := by
  exact mem_Icc_of_mem_pts π (List.getElem_mem i.2)

lemma mesh_nonneg (π : Partition a b) : 0 ≤ π.mesh := by
  unfold mesh
  induction (List.finRange (π.pts.length - 1)).map (fun i =>
      π.pts.get ⟨i.1 + 1, by omega⟩ -
        π.pts.get ⟨i.1, by exact Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩) <;> simp_all

lemma le_foldr_max_of_mem {l : List ℝ} {x : ℝ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldr_cons]
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih hx) (le_max_right _ _)

lemma foldr_max_le_of_forall_le {l : List ℝ} {r : ℝ}
    (hl : ∀ x ∈ l, x ≤ r) : l.foldr max 0 ≤ max 0 r := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldr_cons]
      exact max_le
        (le_trans (hl x (by simp)) (le_max_right _ _))
        (ih (by intro y hy; exact hl y (by simp [hy])))

lemma foldr_max_lt_of_forall_lt {l : List ℝ} {ε : ℝ} (hε : 0 < ε)
    (hl : ∀ x ∈ l, x < ε) : l.foldr max 0 < ε := by
  induction l with
  | nil =>
      simpa using hε
  | cons x xs ih =>
      simp only [List.foldr_cons]
      exact max_lt (hl x (by simp)) (ih (by intro y hy; exact hl y (by simp [hy])))

lemma young_control_max_small_of_small_mesh {a b p q : ℝ} (f g : ℝ → ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (hab : a ≤ b) :
    ∀ ε > 0, ∃ δ > 0, ∀ π : Partition a b, π.mesh ≤ δ →
      ((List.finRange (π.pts.length - 1)).map fun i =>
        young_control f g p q
          (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
          (π.pts.get ⟨i.1 + 1, by omega⟩)).foldr max 0 < ε := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    IsControlOn.uniform_diagonal_continuity (isControlOn_young_control f g hp hq hf hg hfp hgq)
      hab ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro π hπδ
  apply foldr_max_lt_of_forall_lt hε
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  let s := π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩
  let t := π.pts.get ⟨i.1 + 1, by omega⟩
  have hs : s ∈ Set.Icc a b := by
    simpa [s] using π.get_mem_Icc ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩
  have ht : t ∈ Set.Icc a b := by
    simpa [t] using π.get_mem_Icc ⟨i.1 + 1, by omega⟩
  have hst : s ≤ t := by
    exact le_of_lt (π.get_strictMono (show (⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩ :
      Fin π.pts.length) < ⟨i.1 + 1, by omega⟩ from by simp))
  have htdiff : t - s ≤ π.mesh := by
    unfold mesh
    exact le_foldr_max_of_mem <| List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  exact hδ s t hs ht hst (le_trans htdiff hπδ)

lemma raw_young_control_max_tendsto_zero {a b p q : ℝ} (f g : ℝ → ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (π : ℕ → Partition a b) (hπ : Partition.HasVanishingMeshSize π) :
    Tendsto (fun n =>
      ((List.finRange ((π n).pts.length - 1)).map fun i =>
        young_control f g p q
          ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
          ((π n).pts.get ⟨i.1 + 1, by omega⟩)).foldr max 0) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    young_control_max_small_of_small_mesh f g hp hq hf hg hfp hgq (le_of_partition (π 0)) ε hε
  filter_upwards [Metric.tendsto_nhds.mp hπ δ hδpos] with n hn
  have hmeshlt : (π n).mesh < δ := by
    have habs : |(π n).mesh| < δ := by
      simpa [Real.dist_eq] using hn
    simpa [abs_of_nonneg ((π n).mesh_nonneg)] using habs
  have hmaxlt := hδ (π n) hmeshlt.le
  exact abs_lt.mpr ⟨by
    have hnonneg : 0 ≤ ((List.finRange ((π n).pts.length - 1)).map fun i =>
      young_control f g p q
        ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
        ((π n).pts.get ⟨i.1 + 1, by omega⟩)).foldr max 0 := by
      induction (List.finRange ((π n).pts.length - 1)).map (fun i =>
          young_control f g p q
            ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
            ((π n).pts.get ⟨i.1 + 1, by omega⟩)) <;> simp_all
    linarith
  , by
      change ((List.finRange ((π n).pts.length - 1)).map (fun i =>
        young_control f g p q
          ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
          ((π n).pts.get ⟨i.1 + 1, by omega⟩))).foldr max 0 - 0 < ε
      simpa using hmaxlt⟩

lemma omegamax_tendsto_zero {a b p q : ℝ} (f g : ℝ → ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (π : ℕ → Partition a b) (hπ : Partition.HasVanishingMeshSize π) :
    Tendsto (fun n =>
      ((List.finRange ((π n).pts.length - 1)).map fun i =>
        (young_control f g p q
          ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
          ((π n).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1)).foldr max 0)
      atTop (𝓝 0) := by
  let raw : ℕ → ℝ := fun n =>
    ((List.finRange ((π n).pts.length - 1)).map fun i =>
      young_control f g p q
        ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
        ((π n).pts.get ⟨i.1 + 1, by omega⟩)).foldr max 0
  have hraw : Tendsto raw atTop (𝓝 0) :=
    raw_young_control_max_tendsto_zero f g hp hq hf hg hfp hgq π hπ
  have hpow : Tendsto (fun n => raw n ^ (1 / p + 1 / q - 1)) atTop (𝓝 0) := by
    have hpow' := hraw.rpow_const (p := 1 / p + 1 / q - 1) (Or.inr (sub_nonneg.mpr hpq.le))
    convert hpow' using 1
    rw [Real.zero_rpow (sub_pos.mpr hpq).ne']
  refine squeeze_zero ?_ ?_ hpow
  · intro n
    induction (List.finRange ((π n).pts.length - 1)).map (fun i =>
        (young_control f g p q
          ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
          ((π n).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1)) <;> simp_all
  · intro n
    have hupper : ((List.finRange ((π n).pts.length - 1)).map fun i =>
        (young_control f g p q
          ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
          ((π n).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1)).foldr max 0 ≤
          raw n ^ (1 / p + 1 / q - 1) := by
      have hraw_nonneg : 0 ≤ raw n := by
        unfold raw
        induction (List.finRange ((π n).pts.length - 1)).map (fun i =>
            young_control f g p q
              ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
              ((π n).pts.get ⟨i.1 + 1, by omega⟩)) <;> simp_all
      have haux :
          ∀ x ∈ (List.finRange ((π n).pts.length - 1)).map (fun i =>
            (young_control f g p q
              ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
              ((π n).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1)),
            x ≤ raw n ^ (1 / p + 1 / q - 1) := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        have hy' : young_control f g p q
            ((π n).pts.get ⟨y.1, Nat.lt_of_lt_of_le y.2 (Nat.sub_le _ _)⟩)
            ((π n).pts.get ⟨y.1 + 1, by omega⟩) ≤ raw n := by
          exact le_foldr_max_of_mem (List.mem_map.mpr ⟨y, List.mem_finRange _, rfl⟩)
        have hnonneg :
            0 ≤ young_control f g p q
              ((π n).pts.get ⟨y.1, Nat.lt_of_lt_of_le y.2 (Nat.sub_le _ _)⟩)
              ((π n).pts.get ⟨y.1 + 1, by omega⟩) := by
          exact young_control_nonneg _ _ _ _ _ _
        exact Real.rpow_le_rpow hnonneg hy' (sub_nonneg.mpr hpq.le)
      have hfold := foldr_max_le_of_forall_le (r := raw n ^ (1 / p + 1 / q - 1)) haux
      have hrawpow_nonneg : 0 ≤ raw n ^ (1 / p + 1 / q - 1) := Real.rpow_nonneg hraw_nonneg _
      exact le_trans hfold (max_eq_right hrawpow_nonneg).le
    exact hupper

end Partition

/-- Along any sequence of partitions of `[a, b]` with vanishing mesh size, the Riemann-Stieltjes
sums converge under the Young hypotheses.

PROOF: We show that the sequence is Cauchy, from which it follows that it converges. First bound
|(π n).rsSum f g - (π m).rsSum f g| using abs_rsSum_sub_le_common_refinement. Let ρ_{m,n} be
the common refinement of π_n and π_m. Then we have to bound |(π n).rsSum f g - (ρ_{m,n}).rsSum f g|
and |(π m).rsSum f g - (ρ_{m,n}).rsSum f g|. Both terms are handled analogously using
abs_rsSum_sub_le_of_refines, and we obtain a bound like |(π n).rsSum f g - (π m).rsSum f g| ≤
(max_{[s,t] ∈ π_n} ω(s,t)^{1/p + 1/q - 1} + max_{[s,t] ∈ π_m} ω(s,t)^{1/p + 1/q - 1}) *
young_loeve_constant(p,q) * ω(a,b), which converges to zero as min(m,n) → ∞ by
isControlOn_young_control, specifically the condition of continuity on the diagonal of IsControlOn.
-/
theorem exists_tendsto_rsSum_of_vanishing_mesh {a b p q : ℝ} (f g : ℝ → ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (π : ℕ → Partition a b) (hπ : Partition.HasVanishingMeshSize π) :
    ∃ I : ℝ, Tendsto (fun n => (π n).rsSum f g) atTop (𝓝 I) := by
  have h_cauchy : CauchySeq (fun n => (π n).rsSum f g) := by
    have h_bound : ∀ n m,
        |(π n).rsSum f g - (π m).rsSum f g| ≤
          (Partition.young_loeve_constant p q * young_control f g p q a b) *
            ((List.finRange ((π n).pts.length - 1)).map (fun i =>
              (young_control f g p q
                ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
                ((π n).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1))).foldr max 0 +
          (Partition.young_loeve_constant p q * young_control f g p q a b) *
            ((List.finRange ((π m).pts.length - 1)).map (fun i =>
              (young_control f g p q
                ((π m).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
                ((π m).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1))).foldr max 0 := by
      intro n m
      have h_bound_n :
          |(π n).rsSum f g - (Partition.common_refinement (π n) (π m)).rsSum f g| ≤
            (Partition.young_loeve_constant p q * young_control f g p q a b) *
              ((List.finRange ((π n).pts.length - 1)).map (fun i =>
                (young_control f g p q
                  ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
                  ((π n).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1))).foldr max 0 := by
        convert Partition.abs_rsSum_sub_le_of_refines (π n)
          (Partition.common_refinement (π n) (π m)) f g
          (Partition.common_refinement_refines_left (π n) (π m))
          hp hq hpq hf hg hfp hgq using 1
        ring
      have h_bound_m :
          |(π m).rsSum f g - (Partition.common_refinement (π n) (π m)).rsSum f g| ≤
            (Partition.young_loeve_constant p q * young_control f g p q a b) *
              ((List.finRange ((π m).pts.length - 1)).map (fun i =>
                (young_control f g p q
                  ((π m).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
                  ((π m).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1))).foldr max 0 := by
        convert Partition.abs_rsSum_sub_le_of_refines (π m)
          (Partition.common_refinement (π n) (π m)) f g
          (Partition.common_refinement_refines_right (π n) (π m))
          hp hq hpq hf hg hfp hgq using 1
        ring
      exact abs_sub_le_iff.mpr ⟨
        by linarith [abs_le.mp h_bound_n, abs_le.mp h_bound_m],
        by linarith [abs_le.mp h_bound_n, abs_le.mp h_bound_m]⟩
    have h_max_zero :
        Tendsto (fun n =>
          ((List.finRange ((π n).pts.length - 1)).map (fun i =>
            (young_control f g p q
              ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
              ((π n).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1))).foldr max 0)
          atTop (𝓝 0) := by
      convert Partition.omegamax_tendsto_zero f g hp hq hpq hf hg hfp hgq π hπ using 1
    rw [Metric.cauchySeq_iff']
    intro ε hε_pos
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N,
        (Partition.young_loeve_constant p q * young_control f g p q a b) *
          ((List.finRange ((π n).pts.length - 1)).map (fun i =>
            (young_control f g p q
              ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
              ((π n).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1))).foldr max 0 < ε / 2 := by
      simpa using h_max_zero.const_mul _ |> fun h => h.eventually (gt_mem_nhds <| by linarith)
    exact ⟨N, fun n hn => by
      simpa [Real.dist_eq] using lt_of_le_of_lt (h_bound n N) (by linarith [hN n hn, hN N le_rfl])⟩
  exact cauchySeq_tendsto_of_complete h_cauchy


theorem tendsto_rsSum_of_vanishing_mesh_unique {a b p q : ℝ} (f g : ℝ → ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (π ρ : ℕ → Partition a b)
    (hπ : Partition.HasVanishingMeshSize π) (hρ : Partition.HasVanishingMeshSize ρ)
    {I J : ℝ}
    (hπlim : Tendsto (fun n => (π n).rsSum f g) atTop (𝓝 I))
    (hρlim : Tendsto (fun n => (ρ n).rsSum f g) atTop (𝓝 J)) :
    I = J := by
  contrapose! hρlim
  intro H
  convert exists_tendsto_rsSum_of_vanishing_mesh f g hp hq hpq hf hg hfp hgq
    (fun n => if n % 2 = 0 then π (n / 2) else ρ (n / 2)) _ using 1
  · constructor <;> intro hI
    · contradiction
    · obtain ⟨I, hI⟩ := hI
      have h_even : Filter.Tendsto (fun n => (π n).rsSum f g) Filter.atTop (nhds I) := by
        convert hI.comp (Filter.tendsto_id.nsmul_atTop two_pos) using 2
        norm_num [Nat.mul_mod]
      have h_odd : Filter.Tendsto (fun n => (ρ n).rsSum f g) Filter.atTop (nhds I) := by
        convert hI.comp
          (Filter.tendsto_add_atTop_nat 1 |>
            Filter.Tendsto.comp <| Filter.tendsto_id.nsmul_atTop two_pos) using 2
        · norm_num [Nat.add_div]
      exact hρlim <| tendsto_nhds_unique hπlim h_even ▸ tendsto_nhds_unique H h_odd ▸ rfl
  · rw [Partition.HasVanishingMeshSize] at *
    rw [Metric.tendsto_nhds] at *
    intro ε hε
    rcases Filter.eventually_atTop.mp (hπ ε hε) with ⟨N, hN⟩
    rcases Filter.eventually_atTop.mp (hρ ε hε) with ⟨M, hM⟩
    exact Filter.eventually_atTop.mpr ⟨2 * N + 2 * M, fun n hn => by
      split_ifs
      · exact hN _ (by linarith [Nat.div_add_mod n 2, Nat.mod_lt n two_pos])
      · exact hM _ (by linarith [Nat.div_add_mod n 2, Nat.mod_lt n two_pos])⟩


/-- The Young integral is the common limit of Riemann-Stieltjes sums along any vanishing-mesh
sequence of partitions. The definition uses an arbitrarily chosen vanishing-mesh sequence and the
uniqueness theorem above shows that the resulting value is independent of this choice. -/
noncomputable def youngIntegral (f g : ℝ → ℝ) (a b p q : ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (hab : a ≤ b) :
    ℝ := by
  let π : ℕ → Partition a b := Classical.choose (Partition.exists_vanishing_mesh_sequence a b hab)
  let hπ : Partition.HasVanishingMeshSize π :=
    Classical.choose_spec (Partition.exists_vanishing_mesh_sequence a b hab)
  exact Classical.choose
    (exists_tendsto_rsSum_of_vanishing_mesh f g hp hq hpq hf hg hfp hgq π hπ)

-- This says: for any vanishing-mesh sequence π, the RS sums converge to
-- `youngIntegral f g a b p q ...`. It combines existence of limits with uniqueness
-- to show any sequence converges to the canonical definition.
lemma tendsto_rsSum_nhds_youngIntegral_of_vanishing_mesh {a b p q : ℝ} (f g : ℝ → ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (hab : a ≤ b)
    (π : ℕ → Partition a b) (hπ : Partition.HasVanishingMeshSize π) :
    Tendsto (fun n => (π n).rsSum f g) atTop
      (𝓝 (youngIntegral f g a b p q hp hq hpq hf hg hfp hgq hab)) := by
  -- Apply the theorem `exists_tendsto_rsSum_of_vanishing_mesh` to the vanishing-mesh sequence π.
  obtain ⟨I, hI⟩ : ∃ I, Tendsto (fun n => (π n).rsSum f g) atTop (𝓝 I) := by
    exact exists_tendsto_rsSum_of_vanishing_mesh f g hp hq hpq hf hg hfp hgq π hπ;
  convert hI using 1;
  congr! 1;
  exact tendsto_rsSum_of_vanishing_mesh_unique f g hp hq hpq hf hg hfp hgq _ _
    (Classical.choose_spec (Partition.exists_vanishing_mesh_sequence a b hab)) hπ
    (Classical.choose_spec
      (exists_tendsto_rsSum_of_vanishing_mesh f g hp hq hpq hf hg hfp hgq _
        (Classical.choose_spec (Partition.exists_vanishing_mesh_sequence a b hab))))
    hI


/-- The cross term in the summation-by-parts formula for rsSum.go. -/
def rsSum_cross (f g : ℝ → ℝ) : ℝ → List ℝ → ℝ
  | _, [] => 0
  | x, y :: rest => (f y - f x) * (g y - g x) + rsSum_cross f g y rest

/-
PROBLEM
Discrete summation-by-parts identity for rsSum.go:
  go(f,g) + go(g,f) + cross(f,g) = f(last)*g(last) - f(x)*g(x)

PROVIDED SOLUTION
Induction on the list l. Base case: l = [], both sides simplify to 0.
Inductive step: l = y :: rest. Unfold rsSum.go, rsSum_cross, and List.getLastD at the head.
The LHS becomes
  f x * (g y - g x) + go f g y rest + g x * (f y - f x) + go g f y rest +
    (f y - f x) * (g y - g x) + rsSum_cross f g y rest.
Group the go and cross terms for the IH:
  go f g y rest + go g f y rest + rsSum_cross f g y rest =
    f (rest.getLastD y) * g (rest.getLastD y) - f y * g y.
Then the remaining terms are
  f x * (g y - g x) + g x * (f y - f x) + (f y - f x) * (g y - g x) =
    f y * g y - f x * g x,
which follows by ring. Combining gives the result. Note: for y :: rest,
getLastD x = rest.getLastD y.
-/
set_option linter.style.longLine false in
set_option linter.unusedSimpArgs false in
set_option linter.style.multiGoal false in
lemma rsSum_go_add_go_add_cross (f g : ℝ → ℝ) (x : ℝ) (l : List ℝ) :
    Partition.rsSum.go f g x l + Partition.rsSum.go g f x l + rsSum_cross f g x l =
      f (l.getLastD x) * g (l.getLastD x) - f x * g x := by
  induction l generalizing x <;> simp_all +decide [ sub_mul ] ; ring;
  · exact show 0 + 0 + 0 = 0 by norm_num;
  · rename_i k hk₁ hk₂; simp_all +decide [ Partition.rsSum.go, rsSum_cross ] ; ring;
    grind

/-
PROBLEM
The rsSum of a partition satisfies the summation-by-parts identity.

PROVIDED SOLUTION
Unfold rsSum and the match. Case split on π.pts.
If π.pts = [], then π.first gives head? = some a, contradiction since [].head? = none.
If π.pts = x :: xs, then rsSum f g = go f g x xs and rsSum g f = go g f x xs and the match gives
rsSum_cross f g x xs. By rsSum_go_add_go_add_cross,
  go f g x xs + go g f x xs + rsSum_cross f g x xs =
    f (xs.getLastD x) * g (xs.getLastD x) - f x * g x.
From π.first (head? = some a), x = a. From π.last (getLast? = some b), for x :: xs we have
getLast? = some (xs.getLastD x), so xs.getLastD x = b. Substituting gives
f b * g b - f a * g a.
-/
set_option linter.style.longLine false in
set_option linter.unusedSimpArgs false in
lemma Partition.rsSum_add_rsSum_add_cross {a b : ℝ} (π : Partition a b) (f g : ℝ → ℝ) :
    π.rsSum f g + π.rsSum g f + (match π.pts with | [] => 0 | x :: xs => rsSum_cross f g x xs) =
      f b * g b - f a * g a := by
  rcases π with ⟨ pts, hpts ⟩;
  cases pts <;> simp_all +decide [ List.getLast? ];
  · contradiction;
  · convert rsSum_go_add_go_add_cross f g _ _ using 1;
    grind

/-- The cross term for a partition equals rsSum_cross over its points. -/
def Partition.crossTerm {a b : ℝ} (π : Partition a b) (f g : ℝ → ℝ) : ℝ :=
  match π.pts with | [] => 0 | x :: xs => rsSum_cross f g x xs

/-- Finset-based version of the cross term. -/
noncomputable def Partition.crossTermFin {a b : ℝ} (π : Partition a b) (f g : ℝ → ℝ) : ℝ :=
  ((List.finRange (π.pts.length - 1)).map (fun i =>
    (f (π.pts.get ⟨i.1 + 1, by omega⟩) -
        f (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)) *
      (g (π.pts.get ⟨i.1 + 1, by omega⟩) -
        g (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)))).sum

/-
PROBLEM
The list-based and finset-based cross terms are equal.

PROVIDED SOLUTION
Unfold crossTerm and crossTermFin. The crossTerm matches on π.pts as [] or x :: xs,
giving rsSum_cross f g x xs. The crossTermFin uses List.finRange (π.pts.length - 1) to index.
Prove by induction on the list xs, showing that rsSum_cross f g x xs equals the
finRange-indexed sum. For the base case (xs = []), both are 0. For the cons case
(xs = y :: rest), rsSum_cross gives
  (f y - f x) * (g y - g x) + rsSum_cross f g y rest,
and the finRange sum splits similarly.

Actually, the cleanest approach: induction on π.pts.length - 1, or directly unfold both
definitions and show they agree by matching on π.pts and doing induction on the tail.
Use the fact that for x :: xs, get ⟨0, _⟩ = x and get ⟨i+1, _⟩ = xs.get ⟨i, _⟩.
-/
set_option linter.style.longLine false in
set_option linter.unusedSimpArgs false in
set_option linter.style.multiGoal false in
set_option linter.style.refine false in
lemma Partition.crossTerm_eq_crossTermFin {a b : ℝ} (π : Partition a b) (f g : ℝ → ℝ) :
    π.crossTerm f g = π.crossTermFin f g := by
  -- By definition of `rsSum_cross` and `crossTermFin`, we can show that they are equal by induction on the length of the partition's pts.
  have h_eq : ∀ (l : List ℝ), ∀ (x : ℝ), rsSum_cross f g x l = ((List.finRange l.length).map (fun i =>
    (f (l.get ⟨i.1, by omega⟩) - f (if i.1 = 0 then x else l.get ⟨i.1 - 1, by
      exact lt_of_le_of_lt ( Nat.pred_le _ ) i.2⟩)) *
    (g (l.get ⟨i.1, by omega⟩) - g (if i.1 = 0 then x else l.get ⟨i.1 - 1, by
      exact lt_of_le_of_lt ( Nat.pred_le _ ) i.2⟩)))).sum := by
      all_goals generalize_proofs at *;
      intro l x; induction l generalizing x <;> simp +decide [ *, List.finRange_succ ] ;
      · exact?;
      · rename_i k hk₁ hk₂ hk₃; simp_all +decide [ List.finRange_succ ] ;
        convert congr_arg ( fun y => ( f hk₁ - f x ) * ( g hk₁ - g x ) + y ) ( hk₃ hk₁ ) using 1 ; simp +decide [ List.finRange_succ ] ; ring!;
        congr! 2;
        grind
  generalize_proofs at *;
  rcases π with ⟨ _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩, h₀, h₁ ⟩ <;> simp_all +decide [ List.finRange_succ ];
  · cases h₁;
  · unfold Partition.crossTerm Partition.crossTermFin; aesop;
  · convert h_eq ( y :: l ) x using 1 ; simp +decide [ List.finRange ];
    unfold Partition.crossTermFin; simp +decide [ List.finRange_succ ] ; ring;
    congr! 1;
    refine' List.ext_get _ _ <;> simp +decide [ Function.comp ]

/-
PROBLEM
Bound |crossTermFin| in terms of sum of young_control^(1/p+1/q).

PROVIDED SOLUTION
Unfold crossTermFin. The absolute value of a sum is at most the sum of absolute values (Finset.abs_sum_le_sum_abs or similar). Then each |term| = |f(pts[i+1]) - f(pts[i])| * |g(pts[i+1]) - g(pts[i])| (by abs_mul). Each such product is ≤ young_control(pts[i], pts[i+1])^(1/p+1/q) by abs_sub_mul_abs_sub_le_young_control_rpow applied with u = pts[i], v = pts[i], w = pts[i+1]... wait, the existing lemma bounds |f v - f u| * |g w - g v| for u ≤ v ≤ w. For the 2-point case u = v = pts[i], w = pts[i+1], we get |f(pts[i]) - f(pts[i])| * |g(pts[i+1]) - g(pts[i])| = 0, which is useless.

Instead, use abs_sub_le_pVariationPowOn_toReal_rpow twice to get:
|f(pts[i+1]) - f(pts[i])| ≤ pVarPow_f(pts[i], pts[i+1])^(1/p)
|g(pts[i+1]) - g(pts[i])| ≤ pVarPow_g(pts[i], pts[i+1])^(1/q)
Multiply: product ≤ A^(1/p) * B^(1/q) where A = pVarPow_f, B = pVarPow_g.
Then A^(1/p) ≤ (A+B)^(1/p) and B^(1/q) ≤ (A+B)^(1/q) since A ≤ A+B and B ≤ A+B and rpow is monotone.
So product ≤ (A+B)^(1/p) * (A+B)^(1/q) = (A+B)^(1/p+1/q) = young_control^(1/p+1/q).

For the p-variation finiteness: pVarPow on subintervals [pts[i], pts[i+1]] is ≤ the global pVarPow on [a,b] which is finite (by hfp and hgq), so it's also finite. For the membership requirements of abs_sub_le_pVariationPowOn_toReal_rpow: pts[i] and pts[i+1] are both in Set.Icc pts[i] pts[i+1] (trivially), and pts[i] ≤ pts[i+1] (from the sorted/strictMono property of the partition).
-/
set_option linter.style.longLine false in
set_option linter.deprecated false in
set_option linter.style.multiGoal false in
set_option linter.style.refine false in
set_option linter.unusedVariables false in
lemma Partition.abs_crossTermFin_le {a b : ℝ} (π : Partition a b) (f g : ℝ → ℝ)
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q) :
    |π.crossTermFin f g| ≤
      ((List.finRange (π.pts.length - 1)).map (fun i =>
        (young_control f g p q
          (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)
          (π.pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q))).sum := by
  generalize_proofs at *;
  -- Apply the inequality |a * b| ≤ |a|^p * |b|^q for p, q ≥ 1 to each term in the sum.
  have h_term_bound : ∀ i : Fin (π.pts.length - 1), |(f (π.pts.get ⟨i.1 + 1, by omega⟩) - f (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)) * (g (π.pts.get ⟨i.1 + 1, by omega⟩) - g (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩))| ≤ (young_control f g p q (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩) (π.pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q) := by
    intro i
    have h_term_bound : |f (π.pts.get ⟨i.1 + 1, by omega⟩) - f (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)| ≤ (pVariationPowOn f (Set.Icc (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩) (π.pts.get ⟨i.1 + 1, by omega⟩)) p).toReal ^ (1 / p) := by
      apply abs_sub_le_pVariationPowOn_toReal_rpow
      all_goals generalize_proofs at *;
      · linarith;
      · have := π.sorted; simp_all +decide [ List.isChain_iff_get ] ;
        linarith [ this i ];
      · simp +zetaDelta at *;
        have := π.sorted;
        have := List.isChain_iff_get.mp this;
        exact le_of_lt ( this ⟨ i, Nat.lt_pred_iff.mpr ‹_› ⟩ );
      · have := π.sorted;
        have := List.isChain_iff_get.mp this;
        exact le_of_lt ( this ⟨ i, Nat.lt_pred_iff.mpr ‹_› ⟩ );
      · apply_rules [ FinitePVariationOn.subinterval ];
        · have := π.get_mem_Icc ⟨ i, by linarith ⟩ ; aesop;
        · exact π.get_mem_Icc _ |>.2
    have h_term_bound_g : |g (π.pts.get ⟨i.1 + 1, by omega⟩) - g (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩)| ≤ (pVariationPowOn g (Set.Icc (π.pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩) (π.pts.get ⟨i.1 + 1, by omega⟩)) q).toReal ^ (1 / q) := by
      apply_rules [ abs_sub_le_pVariationPowOn_toReal_rpow ]
      generalize_proofs at *;
      · have h_sorted : ∀ i j : Fin π.pts.length, i ≤ j → π.pts.get i ≤ π.pts.get j := by
          exact fun i j hij => by simpa using π.get_strictMono.monotone hij;
        generalize_proofs at *; (
        exact ⟨ le_rfl, h_sorted _ _ ( Nat.le_succ _ ) ⟩);
      · exact ⟨ le_of_lt ( show π.pts.get ⟨ i, Nat.lt_of_lt_of_le i.2 ( Nat.sub_le _ _ ) ⟩ < π.pts.get ⟨ i + 1, by solve_by_elim ⟩ from by
                            have := π.sorted;
                            have := List.isChain_iff_getElem.mp this; aesop; ), le_rfl ⟩;
      · have := π.sorted;
        have := List.isChain_iff_get.mp this;
        exact le_of_lt ( this i );
      · refine' ne_of_lt ( lt_of_le_of_lt _ hgq.lt_top );
        apply_rules [ pVariationPowOn.mono ];
        exact Set.Icc_subset_Icc ( by exact le_trans ( by norm_num ) ( Partition.mem_Icc_of_mem_pts π ( by aesop ) |>.1 ) ) ( by exact le_trans ( Partition.mem_Icc_of_mem_pts π ( by aesop ) |>.2 ) ( by norm_num ) )
    generalize_proofs at *;
    rw [ abs_mul, Real.rpow_add' ] <;> try positivity
    generalize_proofs at *; (
    refine' mul_le_mul ( h_term_bound.trans _ ) ( h_term_bound_g.trans _ ) _ _ <;> norm_num [ young_control ] at * <;> try positivity;
    · exact Real.rpow_le_rpow ( ENNReal.toReal_nonneg ) ( le_add_of_nonneg_right <| ENNReal.toReal_nonneg ) <| by positivity;
    · exact Real.rpow_le_rpow ( by exact ENNReal.toReal_nonneg ) ( le_add_of_nonneg_left <| by positivity ) <| by positivity;);
    exact add_nonneg ( ENNReal.toReal_nonneg ) ( ENNReal.toReal_nonneg );
  convert Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun i _ => h_term_bound i using 1;
  any_goals exact Finset.univ;
  · unfold Partition.crossTermFin; aesop;
  · exact?

/-
PROBLEM
The cross term tends to 0 as the mesh vanishes.

PROVIDED SOLUTION
Step 1: Rewrite crossTerm as crossTermFin using crossTerm_eq_crossTermFin.

Step 2: Bound |crossTermFin| using abs_crossTermFin_le:
|crossTermFin(π_n)| ≤ Σᵢ young_control(pts[i], pts[i+1])^(1/p+1/q)

Step 3: Apply sum_rpow_le_max_rpow_mul_sum with θ = 1/p + 1/q (which is > 1 by hpq):
Σᵢ yc(i)^θ ≤ max(yc(i)^(θ-1)) * Σᵢ yc(i)

But wait, sum_rpow_le_max_rpow_mul_sum bounds (l.map (· ^ θ)).sum ≤ (l.map (· ^ (θ - 1))).foldr max 0 * l.sum, where θ > 1 and l consists of the young_control values.

Step 4: Σᵢ yc(i) ≤ young_control(a,b) by sum_young_control_le.

Step 5: max(yc(i)^(θ-1)) = max(yc(i)^(1/p+1/q-1)) which is exactly the term in omegamax_tendsto_zero, which → 0.

So: |crossTerm(π_n)| ≤ max^(θ-1) * yc(a,b), which → 0 * yc(a,b) = 0.

For the squeeze argument: use squeeze_zero_norm (or squeeze_zero with abs) with the bound from steps 2-5.

The key lemma chain is:
1. crossTerm_eq_crossTermFin converts crossTerm to crossTermFin
2. abs_crossTermFin_le bounds |crossTermFin| by sum of yc^(1/p+1/q)
3. sum_rpow_le_max_rpow_mul_sum converts sum of yc^θ to max^(θ-1) * sum of yc
4. sum_young_control_le bounds sum of yc by yc(a,b)
5. omegamax_tendsto_zero (or raw_young_control_max_tendsto_zero + rpow) gives max^(θ-1) → 0

Actually, sum_rpow_le_max_rpow_mul_sum uses List.sum and List.map and List.foldr max 0. The bound from abs_crossTermFin_le also uses List.sum. So I need to connect them.

Let me be more precise: let l = (List.finRange (m-1)).map (fun i => yc(pts[i], pts[i+1])).
Then abs_crossTermFin_le gives |crossTermFin| ≤ (l.map (· ^ (1/p+1/q))).sum.
sum_rpow_le_max_rpow_mul_sum gives (l.map (· ^ (1/p+1/q))).sum ≤ (l.map (· ^ (1/p+1/q-1))).foldr max 0 * l.sum, using θ = 1/p+1/q > 1.
sum_young_control_le gives l.sum ≤ yc(a,b).
And (l.map (· ^ (1/p+1/q-1))).foldr max 0 is exactly omegamax from omegamax_tendsto_zero, which → 0.

So the final bound: |crossTerm(π_n)| ≤ omegamax(n) * yc(a,b), and omegamax(n) → 0, so use tendsto_nhds_zero_iff or squeeze_zero_norm.

Actually, omegamax_tendsto_zero shows that the foldr max 0 of yc^(1/p+1/q-1) tends to 0. So let me use:
|crossTerm(π_n)| ≤ omegamax(n) * yc(a,b)
and omegamax(n) * yc(a,b) → 0 * yc(a,b) = 0.

For the squeeze: use squeeze_zero_norm with the bound, where the upper tends to 0 using Tendsto.mul_const or Tendsto.const_mul.
-/
set_option linter.style.longLine false in
set_option linter.style.multiGoal false in
lemma crossTerm_tendsto_zero {a b p q : ℝ} (f g : ℝ → ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (π : ℕ → Partition a b) (hπ : Partition.HasVanishingMeshSize π) :
    Tendsto (fun n => (π n).crossTerm f g) atTop (𝓝 0) := by
  -- Apply the squeeze theorem with the bound and the fact that the upper bound tends to 0.
  have h_squeeze : Filter.Tendsto (fun n => |(π n).crossTermFin f g|) Filter.atTop (nhds 0) := by
    have h_squeeze : ∀ n, |(π n).crossTermFin f g| ≤ ((List.finRange ((π n).pts.length - 1)).map fun i => (young_control f g p q ((π n).pts.get ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩) ((π n).pts.get ⟨i.1 + 1, by omega⟩)) ^ (1 / p + 1 / q - 1)).foldr max 0 * (young_control f g p q a b) := by
      intro n; have := Partition.abs_crossTermFin_le ( π n ) f g hp hq hf hg hfp hgq; simp_all +decide [ List.finRange ] ;
      refine le_trans this ?_;
      have h_sum_rpow_le_max_rpow_mul_sum : ∀ {l : List ℝ}, (∀ x ∈ l, 0 ≤ x) → (l.map (· ^ (p⁻¹ + q⁻¹))).sum ≤ (l.map (· ^ (p⁻¹ + q⁻¹ - 1))).foldr max 0 * l.sum := by
        exact?
      generalize_proofs at *; (
      convert h_sum_rpow_le_max_rpow_mul_sum _ |> le_trans <| mul_le_mul_of_nonneg_left ( Partition.sum_young_control_le ( π n ) f g p q hp hq hf hg hfp hgq ) <| ?_ using 1 <;> norm_num [ List.sum_ofFn ] ; ring_nf ; aesop;
      · exact Or.inl ( by rw [ List.ofFn_eq_map ] ; rfl ) ;
      · exact fun i => by apply_rules [ Partition.young_control_nonneg ] ;
      · induction ( List.finRange ( ( π n |> Partition.pts |> List.length ) - 1 ) ) <;> aesop);
    exact squeeze_zero ( fun _ => abs_nonneg _ ) h_squeeze ( by simpa using Filter.Tendsto.mul ( Partition.omegamax_tendsto_zero f g hp hq hpq hf hg hfp hgq π hπ ) tendsto_const_nhds );
  exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa only [ Partition.crossTerm_eq_crossTermFin ] using h_squeeze )

/-- Integration by parts for the Young integral: ∫ₐᵇ fdg + ∫ₐᵇ gdf = (f(b) - f(a))(g(b) - g(a)) . -/
theorem youngIntegral_integration_by_parts {a b p q : ℝ} (f g : ℝ → ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p) (hgq : FinitePVariationOn g (Set.Icc a b) q)
    (hab : a ≤ b) :
    youngIntegral f g a b p q hp hq hpq hf hg hfp hgq hab +
      youngIntegral g f a b q p hq hp (by simpa [add_comm] using hpq) hg hf hgq hfp hab =
        f b * g b - f a * g a := by
  -- Pick a vanishing-mesh sequence
  obtain ⟨π, hπ⟩ := Partition.exists_vanishing_mesh_sequence a b hab
  -- The RS sums converge to the Young integrals
  have hfg :=
    tendsto_rsSum_nhds_youngIntegral_of_vanishing_mesh f g hp hq hpq hf hg hfp hgq hab π hπ
  have hgf := tendsto_rsSum_nhds_youngIntegral_of_vanishing_mesh g f hq hp
    (by simpa [add_comm] using hpq) hg hf hgq hfp hab π hπ
  -- The cross term tends to 0
  have hcross := crossTerm_tendsto_zero f g hp hq hpq hf hg hfp hgq π hπ
  -- By the discrete identity, for each n:
  -- rsSum(π_n,f,g) + rsSum(π_n,g,f) + crossTerm(π_n) = f(b)*g(b) - f(a)*g(a)
  have hdiscrete : ∀ n, (π n).rsSum f g + (π n).rsSum g f + (π n).crossTerm f g =
      f b * g b - f a * g a :=
    fun n => Partition.rsSum_add_rsSum_add_cross (π n) f g
  -- Take the limit: the sum of the first two terms converges to the sum of the Young integrals,
  -- and the third term converges to 0.
  have hlim : Tendsto (fun n => (π n).rsSum f g + (π n).rsSum g f + (π n).crossTerm f g)
      atTop (𝓝 (youngIntegral f g a b p q hp hq hpq hf hg hfp hgq hab +
        youngIntegral g f a b q p hq hp (by simpa [add_comm] using hpq) hg hf hgq hfp hab + 0)) :=
    (hfg.add hgf).add hcross
  rw [add_zero] at hlim
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun n => (hdiscrete n).symm))

/-- Compatibility with Stieltjes integral: if `g` is monotone, then the Young integral against `g`
agrees with the Stieltjes integral against the measure associated to `g`, defined in
Mathlib.MeasureTheory.Measure.Stieltjes. -/
theorem youngIntegral_eq_integral_stieltjes_of_monotone {a b p : ℝ} (f g : ℝ → ℝ)
    (hp : 1 ≤ p) (hp1 : 1 / p + 1 / (1 : ℝ) > 1)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfp : FinitePVariationOn f (Set.Icc a b) p)
    (hg1 : FinitePVariationOn g (Set.Icc a b) 1) (hmono : Monotone g) (hab : a ≤ b) :
    youngIntegral f g a b p 1 hp le_rfl hp1 hf hg hfp hg1 hab =
      ∫ x in Set.Ioc a b, f x ∂(hmono.stieltjesFunction.measure) := by
  sorry
