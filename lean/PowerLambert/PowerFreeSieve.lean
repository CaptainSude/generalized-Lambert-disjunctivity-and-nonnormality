import PowerLambert.ArithmeticProgression
import PowerLambert.Progression
import PowerLambert.Sieve
import PowerLambert.Density
import Mathlib.Data.Nat.Sqrt

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped BigOperators Topology Classical

namespace PowerLambert

theorem prime_power_progression_count_le (r p u v N : ℕ)
    (hr : 2 ≤ r) (hp : p.Prime) (hv : 0 < v) (huv : Nat.Coprime u v) :
    (((Finset.range N).filter (fun n => p ^ r ∣ u + v * n)).card : ℝ) ≤
      (N : ℝ) / (p : ℝ)^r + 1 := by
  by_cases hpv : p ∣ v
  · have he : (Finset.range N).filter (fun n => p ^ r ∣ u + v * n) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro n _
      exact prime_pow_not_dvd_coprime_progression (by omega) hp huv hpv
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hg : Nat.gcd (p ^ r) v = 1 :=
      ((hp.coprime_iff_not_dvd.mpr hpv).pow_left r).gcd_eq_one
    have hd : 0 < p ^ r := pow_pos hp.pos r
    obtain ⟨a, ha⟩ := exists_progression_divisibility_residue hd hv
      (show Nat.gcd (p ^ r) v ∣ u by simp [hg])
    simp only [hg, Nat.div_one] at ha
    have he : (Finset.range N).filter (fun n => p ^ r ∣ u + v * n) =
        (Finset.range N).filter (fun n => Nat.ModEq (p ^ r) n a) := by
      ext n
      simp only [Finset.mem_filter, ha]
    rw [he]
    simpa only [Nat.cast_pow] using (residue_count_bounds (p ^ r) a N hd).2

/-- Uniform power-free lower count with an explicit square-root error. -/
theorem powerFree_progression_card_lower (r u v N : ℕ)
    (hr : 2 ≤ r) (hu : 0 < u) (hv : 0 < v) (huv : Nat.Coprime u v) :
    (1 / 4 : ℝ) * N - (Nat.sqrt (u + v * N) + 1 : ℕ) ≤
      (((Finset.range N).filter (fun n => PowerFree r (u + v * n))).card : ℝ) := by
  let T := (Finset.range (Nat.sqrt (u + v * N) + 1)).filter Nat.Prime
  have hcover : ∀ n ∈ Finset.range N, ¬ PowerFree r (u + v * n) →
      ∃ p ∈ T, p ^ r ∣ u + v * n := by
    intro n hn hnot
    simp only [PowerFree, not_forall, not_imp, not_not] at hnot
    obtain ⟨p, hp, hpd⟩ := hnot
    have hpow : p ^ 2 ≤ p ^ r := pow_le_pow_right₀ hp.one_lt.le hr
    have hle : p ^ r ≤ u + v * n := Nat.le_of_dvd (by omega) hpd
    have hmul : v * n ≤ v * N := Nat.mul_le_mul_left v (Finset.mem_range.mp hn).le
    have hsqrt : p ≤ Nat.sqrt (u + v * N) := Nat.le_sqrt'.mpr (by omega)
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩, hpd⟩
  have hcount : ∀ p ∈ T,
      (((Finset.range N).filter (fun n => p ^ r ∣ u + v * n)).card : ℝ) ≤
      (Finset.range N).card * ((p : ℝ)^r)⁻¹ + 1 := by
    intro p hp
    simpa [div_eq_mul_inv] using
      prime_power_progression_count_le r p u v N hr (Finset.mem_filter.mp hp).2 hv huv
  have hweight : (∑ p ∈ T, ((p : ℝ)^r)⁻¹) ≤ (3 / 4 : ℝ) :=
    sum_inv_pow_finset_le r hr T (fun p hp => (Finset.mem_filter.mp hp).2.two_le)
  have hs := sieve_card_lower (Finset.range N) T (fun n => PowerFree r (u + v * n))
    (fun p n => p ^ r ∣ u + v * n) (fun p => ((p : ℝ)^r)⁻¹) (3 / 4) hcover
    (fun p hp => by
      convert hcount p hp using 1
      congr 2
      ext n
      simp) hweight
  have hc : T.card ≤ Nat.sqrt (u + v * N) + 1 :=
    (Finset.card_filter_le _ _).trans (by simp)
  have hc' : (T.card : ℝ) ≤ (Nat.sqrt (u + v * N) + 1 : ℕ) := by exact_mod_cast hc
  simp only [Finset.card_range] at hs
  linarith

theorem sqrt_linear_div_tendsto_zero (u v : ℕ) :
    Tendsto (fun N : ℕ => (Nat.sqrt (u + v * N) : ℝ) / N) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N => lt_of_lt_of_le ha (by positivity))
  · intro ε hε
    have hs : (0 : ℝ) < ε ^ 2 := sq_pos_of_pos hε
    have hlarge : ∀ᶠ N : ℕ in atTop, ((u : ℝ) + v + 1) / ε ^ 2 < N :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
    filter_upwards [hlarge, eventually_ge_atTop 1] with N hN hN1
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hbig := (div_lt_iff₀ hs).mp hN
    have hbig' := mul_lt_mul_of_pos_right hbig hNr
    have hroot : (Nat.sqrt (u + v * N) : ℝ)^2 ≤ (u : ℝ) + v * N := by
      exact_mod_cast Nat.sqrt_le' (u + v * N)
    have huN : (u : ℝ) ≤ u * (N : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) u]
    have hroot0 : (0 : ℝ) ≤ Nat.sqrt (u + v * N) := Nat.cast_nonneg _
    have htarget : (Nat.sqrt (u + v * N) : ℝ) < ε * N := by
      nlinarith [mul_pos hε hNr]
    exact (div_lt_iff₀ hNr).mpr htarget

/-- Every coprime positive progression has power-free lower density at least 1/4. -/
theorem powerFree_progression_positive_density (r u v : ℕ)
    (hr : 2 ≤ r) (hu : 0 < u) (hv : 0 < v) (huv : Nat.Coprime u v)
    (δ : ℝ) (hδ : δ < 1 / 4) :
    ∀ᶠ N in atTop, δ < prefixDensity (fun n => PowerFree r (u + v * n)) N := by
  apply eventually_density_lower_of_count_bound
    (fun n => PowerFree r (u + v * n))
    (fun N => (Nat.sqrt (u + v * N) + 1 : ℕ)) (1 / 4) δ
  · intro N
    exact powerFree_progression_card_lower r u v N hr hu hv huv
  · have h := (sqrt_linear_div_tendsto_zero u v).add
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    simpa [Nat.cast_add, Nat.cast_one, add_div, one_div] using h
  · exact hδ

end PowerLambert
