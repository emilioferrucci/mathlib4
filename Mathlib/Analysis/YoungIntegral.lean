/-
Copyright (c) 2025 Emilio Ferrucci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilio Ferrucci
-/
import Mathlib.Topology.EMetricSpace.PVariation

open Filter
open scoped Topology

/-!
# Young Integral

We define Riemann-Stieltjes sums and prove the Young-Loève estimate, bounding the difference
between a Riemann-Stieltjes sum and the trivial partition approximation in terms of the
$p$-variation of $f$ and the $q$-variation of $g$, when $1/p + 1/q > 1$.

### Main definitions

* `IsSuperadditiveOn a b ω`: interval superadditivity on the simplex over `[a, b]`.
* `IsControlOn a b ω`: a control on `[a, b]`, i.e. a superadditive interval function that is zero
  on the diagonal and tends to `0` on collapsing intervals.
* `Partition a b`: a partition of the interval `[a, b]`.
* `Partition.rsSum`: Riemann-Stieltjes sum of `f dg` over a partition.

### Main statements

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

theorem isControlOn_pVariationPowOn {E : Type*} [PseudoEMetricSpace E] (f : ℝ → E) {a b p : ℝ}
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

theorem isControlOn_add {a b : ℝ} {ω₁ ω₂ : ℝ → ℝ → ℝ}
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
        ω (u ⟨1, by omega⟩) (u ⟨2 * n + 1, by exact lt_of_le_of_lt hnm (Nat.lt_succ_self m)⟩) := by
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

namespace Partition

variable {a b : ℝ}

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
theorem rsSum_go_append (f g : ℝ → ℝ) (x y : ℝ) (l₁ l₂ : List ℝ) :
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

end Partition
