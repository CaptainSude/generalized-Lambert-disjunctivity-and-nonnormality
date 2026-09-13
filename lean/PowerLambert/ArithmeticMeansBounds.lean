import PowerLambert.ArithmeticMeansEuler

open Finset
open scoped BigOperators

namespace PowerLambert

theorem progression_prime_factor_le {r Q a p B : ℕ} (hr : 2 ≤ r) (hQ : 0 < Q)
    (hp : p.Prime) (hB : 1 ≤ B) (hv : Q.factorization p = r * (B - 1) + 1) :
    (∑' k, progressionDivisorWeight r Q a (p ^ k)) ≤ (B : ℝ) + 1 := by
  have heq : (∑' k, progressionDivisorWeight r Q a (p ^ k)) =
      ∑' k, if p ^ min (r * k) (Q.factorization p) ∣ a then
        primeLocalTerm p r (Q.factorization p) k else 0 :=
    tsum_congr (fun k => progressionDivisorWeight_prime_pow (r := r) (a := a)
      (k := k) hp (Nat.ne_of_gt hQ))
  rw [heq, hv]
  exact tsum_primeLocalTerm_residue_le hp.two_le hr hB

theorem progression_prime_factor_eq_one {r Q a p : ℕ} (hr : r ≠ 0) (hQ : 0 < Q)
    (hp : p ∈ Q.primeFactors) (ha : ¬ p ∣ a) :
    (∑' k, progressionDivisorWeight r Q a (p ^ k)) = 1 := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hs : Q.factorization p ≠ 0 := by
    exact Finsupp.mem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
  rw [tsum_congr (fun k => progressionDivisorWeight_prime_pow (r := r) (a := a)
    (k := k) hprime (Nat.ne_of_gt hQ))]
  exact tsum_primeLocalTerm_residue_eq_one hr hs ha

theorem prime_mem_of_factorization_prescribed {r Q p A : ℕ}
    (hv : Q.factorization p = r * (A - 1) + 1) : p ∈ Q.primeFactors := by
  rw [← Nat.support_factorization]
  apply Finsupp.mem_support_iff.mpr
  rw [hv]
  omega

/-- Intermediate shifts have only the retained prime's local cost. -/
theorem progression_mean_bound_nondividing_controls {r Q a p A : ℕ}
    (hr : 2 ≤ r) (hQ : 0 < Q) (hA : 1 ≤ A)
    (hv : Q.factorization p = r * (A - 1) + 1)
    (hcontrols : ∀ q ∈ Q.primeFactors, q ≠ p → ¬ q ∣ a) :
    (∑' d, progressionDivisorWeight r Q a d) ≤ 2 * ((A : ℝ) + 1) := by
  classical
  have hp := prime_mem_of_factorization_prescribed hv
  let C : ℕ → ℝ := fun q => if q = p then (A : ℝ) + 1 else 1
  have hcost : ∀ q ∈ Q.primeFactors, 1 ≤ C q := by
    intro q hq
    dsimp [C]
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) A]
  have hlocal : ∀ q ∈ Q.primeFactors,
      (∑' k, progressionDivisorWeight r Q a (q ^ k)) ≤ C q := by
    intro q hq
    by_cases heq : q = p
    · subst q
      simpa only [C, ite_true] using
        progression_prime_factor_le hr hQ (Nat.prime_of_mem_primeFactors hp) hA hv
    · rw [progression_prime_factor_eq_one (by omega) hQ hq (hcontrols q hq heq)]
      simp [C, heq]
  have hprod : (∏ q ∈ Q.primeFactors, C q) = (A : ℝ) + 1 := by
    rw [Finset.prod_eq_single_of_mem p hp]
    · simp [C]
    · intro q hq hqp
      simp [C, hqp]
  simpa only [hprod] using tsum_progressionDivisorWeight_le_product hr hQ C hcost hlocal

/-- The complete mean estimate includes every recurrence of every control prime. -/
theorem progression_mean_bound_all_shifts {r Q a p A b : ℕ}
    (hr : 2 ≤ r) (hQ : 0 < Q) (hA : 1 ≤ A) (hb : 2 ≤ b)
    (hv : Q.factorization p = r * (A - 1) + 1)
    (hcontrols : ∀ q ∈ Q.primeFactors, q ≠ p → Q.factorization q = r * (b - 1) + 1) :
    (∑' d, progressionDivisorWeight r Q a d) ≤
      2 * ((A : ℝ) + 1) * ((b : ℝ) + 1) ^ (Q.primeFactors.card - 1) := by
  classical
  have hp := prime_mem_of_factorization_prescribed hv
  let C : ℕ → ℝ := fun q => if q = p then (A : ℝ) + 1 else (b : ℝ) + 1
  have hcost : ∀ q ∈ Q.primeFactors, 1 ≤ C q := by
    intro q hq
    dsimp [C]
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) A, Nat.cast_nonneg (α := ℝ) b]
  have hlocal : ∀ q ∈ Q.primeFactors,
      (∑' k, progressionDivisorWeight r Q a (q ^ k)) ≤ C q := by
    intro q hq
    by_cases heq : q = p
    · subst q
      simpa only [C, ite_true] using
        progression_prime_factor_le hr hQ (Nat.prime_of_mem_primeFactors hp) hA hv
    · simpa only [C, if_neg heq] using
        progression_prime_factor_le hr hQ (Nat.prime_of_mem_primeFactors hq) (by omega)
          (hcontrols q hq heq)
  have hprod : (∏ q ∈ Q.primeFactors, C q) =
      ((A : ℝ) + 1) * ((b : ℝ) + 1) ^ (Q.primeFactors.card - 1) := by
    rw [← Finset.mul_prod_erase Q.primeFactors C hp]
    simp only [C, ite_true]
    congr 1
    calc
      _ = ∏ _q ∈ Q.primeFactors.erase p, ((b : ℝ) + 1) := by
        apply Finset.prod_congr rfl
        intro q hq
        exact if_neg (Finset.ne_of_mem_erase hq)
      _ = _ := by simp only [Finset.prod_const, Finset.card_erase_of_mem hp]
  have h := tsum_progressionDivisorWeight_le_product hr hQ C hcost hlocal
  rw [hprod] at h
  simpa only [mul_assoc] using h

end PowerLambert
