import PowerLambert.Series

open scoped BigOperators Topology
open Filter Finset

namespace PowerLambert

noncomputable def orbitTrunc (b r U n : ℕ) : ℝ :=
  ∑ m ∈ range U, residueTerm b ((m + 1) ^ r) n

noncomputable def orbitTail (b r U n : ℕ) : ℝ :=
  ∑' m : ℕ, residueTerm b ((m + U + 1) ^ r) n

noncomputable def reciprocalTail (r U : ℕ) : ℝ :=
  ∑' m : ℕ, (((m + U + 1 : ℕ) : ℝ) ^ r)⁻¹

lemma orbitTail_summable {b r U n : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    Summable (fun m : ℕ => residueTerm b ((m + U + 1) ^ r) n) := by
  exact (summable_nat_add_iff U).mpr (orbitSeries_summable hb hr)

lemma reciprocalTail_summable {r U : ℕ} (hr : 2 ≤ r) :
    Summable (fun m : ℕ => (((m + U + 1 : ℕ) : ℝ) ^ r)⁻¹) := by
  exact (summable_nat_add_iff U).mpr (summable_power_reciprocals hr)

lemma orbitTail_nonneg {b r U n : ℕ} (hb : 2 ≤ b) :
    0 ≤ orbitTail b r U n := by
  exact tsum_nonneg (fun m => residueTerm_nonneg hb (by positivity))

lemma reciprocalTail_nonneg (r U : ℕ) : 0 ≤ reciprocalTail r U := by
  exact tsum_nonneg (fun m => by positivity)

lemma orbitTrunc_add_orbitTail {b r U n : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    orbitTrunc b r U n + orbitTail b r U n = orbitSeries b r n := by
  exact (orbitSeries_summable hb hr).sum_add_tsum_nat_add U

lemma abs_orbitSeries_sub_trunc {b r U n : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    |orbitSeries b r n - orbitTrunc b r U n| = orbitTail b r U n := by
  rw [← orbitTrunc_add_orbitTail hb hr, add_sub_cancel_left,
    abs_of_nonneg (orbitTail_nonneg hb)]

lemma reciprocalTail_tendsto_zero (r : ℕ) :
    Tendsto (reciprocalTail r) atTop (𝓝 0) := by
  exact tendsto_sum_nat_add (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ r)⁻¹)

lemma sum_orbitTail_le {b r U N : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    (∑ n ∈ range N, orbitTail b r U n) ≤
      (N : ℝ) * reciprocalTail r U / (b - 1 : ℝ) := by
  have hs : ∀ n ∈ range N,
      Summable (fun m : ℕ => residueTerm b ((m + U + 1) ^ r) n) :=
    fun _ _ => orbitTail_summable hb hr
  have hp : Summable (fun m : ℕ =>
      (N : ℝ) / ((m + U + 1 : ℕ) : ℝ) ^ r / (b - 1 : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      ((reciprocalTail_summable hr).mul_left (N : ℝ)).mul_right ((b - 1 : ℝ)⁻¹)
  calc
    (∑ n ∈ range N, orbitTail b r U n) =
        ∑' m : ℕ, ∑ n ∈ range N, residueTerm b ((m + U + 1) ^ r) n := by
      exact (Summable.tsum_finsetSum hs).symm
    _ ≤ ∑' m : ℕ, (N : ℝ) / ((m + U + 1 : ℕ) : ℝ) ^ r / (b - 1 : ℝ) := by
      apply Summable.tsum_le_tsum
      · intro m
        simpa only [Nat.cast_pow] using sum_residueTerm_le (N := N) hb (by positivity : 0 < (m + U + 1) ^ r)
      · exact summable_sum hs
      · exact hp
    _ = (N : ℝ) * reciprocalTail r U / (b - 1 : ℝ) := by
      simp only [div_eq_mul_inv, reciprocalTail, ← tsum_mul_left, ← tsum_mul_right]

theorem mean_abs_orbitSeries_sub_trunc_le {b r U N : ℕ}
    (hb : 2 ≤ b) (hr : 2 ≤ r) (hN : 0 < N) :
    (∑ n ∈ range N, |orbitSeries b r n - orbitTrunc b r U n|) / (N : ℝ) ≤
      reciprocalTail r U / (b - 1 : ℝ) := by
  simp_rw [abs_orbitSeries_sub_trunc hb hr]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ hN').mpr
  calc
    _ ≤ (N : ℝ) * reciprocalTail r U / (b - 1 : ℝ) := sum_orbitTail_le hb hr
    _ = _ := by ring

theorem orbitTrunc_periodic (b r U : ℕ) :
    Function.Periodic (orbitTrunc b r U) (U.factorial ^ r) := by
  intro n
  unfold orbitTrunc
  apply sum_congr rfl
  intro m hm
  have hdiv : (m + 1) ^ r ∣ U.factorial ^ r :=
    pow_dvd_pow_of_dvd (Nat.dvd_factorial (by omega) (by have := mem_range.mp hm; omega)) r
  simp [residueTerm, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv]

theorem exists_periodic_orbit_approximation {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ℕ) (u : ℕ → ℝ), 0 < P ∧ Function.Periodic u P ∧
      ∀ N : ℕ, 0 < N →
        (∑ n ∈ range N, |orbitSeries b r n - u n|) / (N : ℝ) < ε := by
  have hb' : (0 : ℝ) < b - 1 := by exact_mod_cast (show 0 < (b : ℤ) - 1 by omega)
  have he : 0 < ε * (b - 1 : ℝ) := mul_pos hε hb'
  have hev : ∀ᶠ U in atTop, reciprocalTail r U < ε * (b - 1 : ℝ) :=
    (reciprocalTail_tendsto_zero r).eventually (eventually_lt_nhds he)
  obtain ⟨U, hU⟩ := hev.exists
  refine ⟨U.factorial ^ r, orbitTrunc b r U, by positivity, orbitTrunc_periodic b r U, ?_⟩
  intro N hN
  exact (mean_abs_orbitSeries_sub_trunc_le hb hr hN).trans_lt ((div_lt_iff₀ hb').mpr hU)

end PowerLambert
