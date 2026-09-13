import PowerLambert.ArithmeticMeansLocal
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import PowerLambert.Sieve

open Filter Finset
open scoped BigOperators Topology

namespace PowerLambert

/-- Mean of the `d`th divisor indicator on a progression of step `Q`, offset `a`. -/
noncomputable def progressionDivisorWeight (r Q a d : ℕ) : ℝ :=
  if Nat.gcd (d ^ r) Q ∣ a then (Nat.gcd (d ^ r) Q : ℝ) / (d : ℝ) ^ r else 0

theorem progressionDivisorWeight_nonneg (r Q a d : ℕ) :
    0 ≤ progressionDivisorWeight r Q a d := by
  unfold progressionDivisorWeight
  split_ifs <;> positivity

theorem progressionDivisorWeight_le (r Q a d : ℕ) (hQ : 0 < Q) :
    progressionDivisorWeight r Q a d ≤ (Q : ℝ) * (1 / (d : ℝ) ^ r) := by
  unfold progressionDivisorWeight
  split_ifs
  · rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
    exact_mod_cast Nat.gcd_le_right (d ^ r) hQ
  · positivity

theorem summable_progressionDivisorWeight {r Q a : ℕ} (hr : 2 ≤ r) (hQ : 0 < Q) :
    Summable (progressionDivisorWeight r Q a) := by
  exact Summable.of_nonneg_of_le (progressionDivisorWeight_nonneg r Q a)
    (fun d => progressionDivisorWeight_le r Q a d hQ)
    ((Real.summable_one_div_nat_pow.mpr (by omega : 1 < r)).mul_left (Q : ℝ))

theorem progressionDivisorWeight_zero {r Q a : ℕ} (hr : r ≠ 0) :
    progressionDivisorWeight r Q a 0 = 0 := by
  simp [progressionDivisorWeight, hr]

theorem progressionDivisorWeight_one (r Q a : ℕ) :
    progressionDivisorWeight r Q a 1 = 1 := by
  simp [progressionDivisorWeight]

theorem progressionDivisorWeight_mul {r Q a m n : ℕ} (hc : Nat.Coprime m n) :
    progressionDivisorWeight r Q a (m * n) =
      progressionDivisorWeight r Q a m * progressionDivisorWeight r Q a n := by
  have hpow := hc.pow r r
  have hg : Nat.gcd ((m * n) ^ r) Q = Nat.gcd (m ^ r) Q * Nat.gcd (n ^ r) Q := by
    simpa only [mul_pow, Nat.gcd_comm] using hpow.gcd_mul Q
  have hgc : Nat.Coprime (Nat.gcd (m ^ r) Q) (Nat.gcd (n ^ r) Q) :=
    hpow.of_dvd (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  have hdvd : Nat.gcd (m ^ r) Q * Nat.gcd (n ^ r) Q ∣ a ↔
      Nat.gcd (m ^ r) Q ∣ a ∧ Nat.gcd (n ^ r) Q ∣ a := by
    exact ⟨fun h => ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩,
      fun h => hgc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  simp only [progressionDivisorWeight]
  simp only [hg, hdvd]
  simp only [Nat.cast_mul, mul_pow]
  split_ifs <;> simp_all [div_mul_div_comm]

theorem gcd_prime_pow_eq {p k Q : ℕ} (hp : p.Prime) (hQ : Q ≠ 0) :
    Nat.gcd (p ^ k) Q = p ^ min k (Q.factorization p) := by
  apply Nat.eq_of_factorization_eq
    (Nat.ne_of_gt (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hQ)))
    (pow_ne_zero _ hp.ne_zero)
  intro q
  rw [Nat.factorization_gcd (pow_ne_zero _ hp.ne_zero) hQ,
    hp.factorization_pow, hp.factorization_pow]
  by_cases h : q = p
  · subst q
    simp
  · simp [h]

theorem progressionDivisorWeight_prime_pow {p r Q a k : ℕ} (hp : p.Prime) (hQ : Q ≠ 0) :
    progressionDivisorWeight r Q a (p ^ k) =
      if p ^ min (r * k) (Q.factorization p) ∣ a then
        primeLocalTerm p r (Q.factorization p) k else 0 := by
  simp only [progressionDivisorWeight, ← pow_mul, Nat.mul_comm k r, gcd_prime_pow_eq hp hQ]
  simp only [primeLocalTerm, Nat.cast_pow, ← pow_mul, Nat.mul_comm k r]

/-- The complete Euler product for the concrete progression weights. -/
theorem progressionDivisorWeight_eulerProduct {r Q a : ℕ} (hr : 2 ≤ r) (hQ : 0 < Q) :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow,
      ∑' k, progressionDivisorWeight r Q a (p ^ k)) atTop
      (𝓝 (∑' d, progressionDivisorWeight r Q a d)) := by
  apply EulerProduct.eulerProduct (progressionDivisorWeight_one r Q a)
    (fun h => progressionDivisorWeight_mul h) _ (progressionDivisorWeight_zero (by omega))
  simpa only [Real.norm_of_nonneg (progressionDivisorWeight_nonneg r Q a _)] using
    summable_progressionDivisorWeight hr hQ

theorem tsum_reciprocal_nat_pow_le_two {r : ℕ} (hr : 2 ≤ r) :
    (∑' d : ℕ, (1 : ℝ) / (d : ℝ) ^ r) ≤ 2 := by
  have hs : Summable (fun d : ℕ => ((d : ℝ) ^ r)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by omega)
  have htail : (∑' d : ℕ, (((d + 2 : ℕ) : ℝ) ^ r)⁻¹) ≤ (3 / 4 : ℝ) := by
    apply le_of_tendsto ((summable_nat_add_iff 2).mpr hs).hasSum.tendsto_sum_nat
    apply Filter.Eventually.of_forall
    intro N
    simpa only [Nat.cast_add, Nat.cast_ofNat] using sum_inv_pow_from_two_le r N hr
  simp_rw [one_div]
  rw [← hs.sum_add_tsum_nat_add 2]
  have hhead : (∑ d ∈ range 2, ((d : ℝ) ^ r)⁻¹) = 1 := by
    simp [Finset.sum_range_succ, show r ≠ 0 by omega]
  rw [hhead]
  linarith

theorem progressionDivisorWeight_base_local_ge_one {r p : ℕ} (hr : 2 ≤ r)
    (hp : p.Prime) : 1 ≤ ∑' k, progressionDivisorWeight r 1 0 (p ^ k) := by
  have hs := (summable_progressionDivisorWeight (a := 0) hr (by decide : 0 < 1)).comp_injective
    (Nat.pow_right_injective hp.one_lt)
  have h := hs.sum_le_tsum ({0} : Finset ℕ)
    (fun k _ => progressionDivisorWeight_nonneg r 1 0 (p ^ k))
  simpa [progressionDivisorWeight] using h

/-- A finite collection of constrained primes gives only the product of its local
costs; this estimate is independent of the numerical sizes of the primes. -/
theorem tsum_progressionDivisorWeight_le_product {r Q a : ℕ}
    (hr : 2 ≤ r) (hQ : 0 < Q) (C : ℕ → ℝ)
    (hC : ∀ p ∈ Q.primeFactors, 1 ≤ C p)
    (hlocal : ∀ p ∈ Q.primeFactors,
      (∑' k, progressionDivisorWeight r Q a (p ^ k)) ≤ C p) :
    (∑' d, progressionDivisorWeight r Q a d) ≤ 2 * ∏ p ∈ Q.primeFactors, C p := by
  classical
  let F : ℕ → ℝ := fun p => ∑' k, progressionDivisorWeight r Q a (p ^ k)
  let G : ℕ → ℝ := fun p => ∑' k, progressionDivisorWeight r 1 0 (p ^ k)
  let D : ℕ → ℝ := fun p => if p ∈ Q.primeFactors then C p else 1
  have hG : ∀ p, 0 ≤ G p := fun p => tsum_nonneg (fun k => progressionDivisorWeight_nonneg r 1 0 _)
  have hFD : ∀ p : ℕ, p.Prime → F p ≤ D p * G p := by
    intro p hp
    by_cases hps : p ∈ Q.primeFactors
    · dsimp [D]
      rw [if_pos hps]
      exact (hlocal p hps).trans (le_mul_of_one_le_right (by linarith [hC p hps])
        (progressionDivisorWeight_base_local_ge_one hr hp))
    · have hnot : ¬ p ∣ Q := by
        intro h
        exact hps (hp.mem_primeFactors h (Nat.ne_of_gt hQ))
      have hz : Q.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnot
      have heq : F p = G p := by
        apply tsum_congr
        intro k
        rw [progressionDivisorWeight_prime_pow hp (Nat.ne_of_gt hQ), hz]
        simp [progressionDivisorWeight, primeLocalTerm, Nat.cast_pow, ← pow_mul, Nat.mul_comm k r]
      dsimp only [D]
      rw [if_neg hps, one_mul, heq]
  have hprod : ∀ N : ℕ, (∏ p ∈ N.primesBelow, F p) ≤
      (∏ p ∈ Q.primeFactors, C p) * ∏ p ∈ N.primesBelow, G p := by
    intro N
    calc
      _ ≤ ∏ p ∈ N.primesBelow, D p * G p :=
        Finset.prod_le_prod₀ (fun p _ => tsum_nonneg (fun k => progressionDivisorWeight_nonneg r Q a _))
          (fun p hp => hFD p (Nat.prime_of_mem_primesBelow hp))
      _ = (∏ p ∈ N.primesBelow, D p) * ∏ p ∈ N.primesBelow, G p := Finset.prod_mul_distrib
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun p _ => hG p))
        dsimp [D]
        rw [← Finset.prod_filter]
        apply Finset.prod_le_prod_of_subset_of_one_le₀
        · intro p hp
          exact (Finset.mem_filter.mp hp).2
        · intro p hp
          linarith [hC p (Finset.mem_filter.mp hp).2]
        · intro p hp _
          exact hC p hp
  have hlimit : (∑' d, progressionDivisorWeight r Q a d) ≤
      (∏ p ∈ Q.primeFactors, C p) * ∑' d, progressionDivisorWeight r 1 0 d := by
    apply le_of_tendsto_of_tendsto
      (progressionDivisorWeight_eulerProduct hr hQ)
      ((progressionDivisorWeight_eulerProduct (a := 0) hr (by decide : 0 < 1)).const_mul _)
    exact Filter.Eventually.of_forall hprod
  have hzeta : (∑' d, progressionDivisorWeight r 1 0 d) ≤ 2 := by
    simpa [progressionDivisorWeight] using tsum_reciprocal_nat_pow_le_two hr
  have hC0 : 0 ≤ ∏ p ∈ Q.primeFactors, C p :=
    Finset.prod_nonneg (fun p hp => (by linarith [hC p hp]))
  exact hlimit.trans (by nlinarith)

end PowerLambert
