import PowerLambert.ArithmeticMeansBounds
import PowerLambert.Parameters

open Finset
open scoped BigOperators

namespace PowerLambert

theorem factorization_prod_distinct_prime_powers {ι : Type*} (S : Finset ι)
    (p e : ι → ℕ) (hp : ∀ i ∈ S, (p i).Prime) (hdist : Set.InjOn p S)
    {i : ι} (hi : i ∈ S) :
    (∏ k ∈ S, p k ^ (e k + 1)).factorization (p i) = e i + 1 := by
  classical
  rw [Nat.factorization_prod (fun k hk => pow_ne_zero _ (hp k hk).ne_zero)]
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single i]
  · exact Nat.factorization_pow_self (hp i hi)
  · intro k hk hki
    rw [(hp k hk).factorization_pow]
    exact Finsupp.single_eq_of_ne (fun heq => hki (hdist hk hi heq.symm))
  · exact fun h => (h hi).elim

theorem mem_primeFactors_prod_prime_powers {ι : Type*} (S : Finset ι)
    (p e : ι → ℕ) (hp : ∀ i ∈ S, (p i).Prime) {q : ℕ} :
    q ∈ (∏ k ∈ S, p k ^ (e k + 1)).primeFactors ↔ ∃ i ∈ S, q = p i := by
  classical
  have hn : (∏ k ∈ S, p k ^ (e k + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k hk => pow_ne_zero _ (hp k hk).ne_zero)
  constructor
  · intro h
    have hq := Nat.prime_of_mem_primeFactors h
    obtain ⟨i, hi, hdi⟩ := (hq.prime.dvd_finsetProd_iff _).mp (Nat.dvd_of_mem_primeFactors h)
    exact ⟨i, hi, (Nat.prime_dvd_prime_iff_eq hq (hp i hi)).mp (hq.dvd_of_dvd_pow hdi)⟩
  · rintro ⟨i, hi, rfl⟩
    exact (hp i hi).mem_primeFactors
      ((dvd_pow_self _ (Nat.succ_ne_zero _)).trans (Finset.dvd_prod_of_mem _ hi)) hn

theorem card_primeFactors_prod_distinct_prime_powers {ι : Type*} (S : Finset ι)
    (p e : ι → ℕ) (hp : ∀ i ∈ S, (p i).Prime) (hdist : Set.InjOn p S) :
    (∏ k ∈ S, p k ^ (e k + 1)).primeFactors.card = S.card := by
  classical
  have heq : (∏ k ∈ S, p k ^ (e k + 1)).primeFactors = S.image p := by
    ext q
    simp only [mem_primeFactors_prod_prime_powers S p e hp, Finset.mem_image]
    constructor <;> rintro ⟨i, hi, heq⟩ <;> exact ⟨i, hi, heq.symm⟩
  rw [heq]
  exact Finset.card_image_of_injOn hdist

theorem prime_not_dvd_exact_valuation_quotient {n p e : ℕ}
    (hp : p.Prime) (hn : n ≠ 0) (he : n.factorization p = e) : ¬ p ∣ n / p ^ e := by
  intro hd
  have hpow : p ^ e ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr (by omega)
  have hd' : p ^ (e + 1) ∣ n := by
    rw [pow_succ]
    have h := Nat.mul_dvd_mul_left (p ^ e) hd
    rwa [Nat.mul_div_cancel' hpow] at h
  have := (hp.pow_dvd_iff_le_factorization hn).mp hd'
  omega

theorem shifts_equal_of_prime_dvd {n p j t : ℕ} (hj : j < p) (ht : t < p)
    (hdj : p ∣ n + j) (hdt : p ∣ n + t) : j = t := by
  have heq : n + j ≡ n + t [MOD p] := hdj.modEq_zero_nat.trans hdt.zero_modEq_nat
  exact (heq.add_left_cancel' n).eq_of_lt_of_lt hj ht

abbrev ControlIndex (H : ℕ) := Option (Fin (H + 1) × Fin H)

def controlIndices (H t : ℕ) : Finset (ControlIndex H) :=
  insert none ((Finset.univ.filter fun x : Fin (H + 1) × Fin H => (x.1 : ℕ) ≠ t).image some)

noncomputable def controlPrime (H : ℕ) : ControlIndex H → ℕ
  | none => 2
  | some x => largePrime (H ^ 3 + H + 2) (Nat.pair x.1 x.2)

def controlShift {H : ℕ} (t : ℕ) : ControlIndex H → ℕ
  | none => t
  | some x => x.1

def controlExponent {H : ℕ} (r b A : ℕ) : ControlIndex H → ℕ
  | none => r * (A - 1)
  | some _ => r * (b - 1)

theorem controlPrime_prime (H : ℕ) (i : ControlIndex H) : (controlPrime H i).Prime := by
  cases i with
  | none => exact Nat.prime_two
  | some i => exact largePrime_prime _ _

theorem controlPrime_some_large {H : ℕ} (i : Fin (H + 1) × Fin H) :
    H ^ 3 + H + 2 < controlPrime H (some i) := largePrime_gt _ _

theorem controlPrime_injective (H : ℕ) : Function.Injective (controlPrime H) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      have hj := controlPrime_some_large j
      change 2 = controlPrime H (some j) at h
      omega
  | some i =>
    cases j with
    | none =>
      have hi := controlPrime_some_large i
      change controlPrime H (some i) = 2 at h
      omega
    | some j =>
      have hpair := Nat.pair_eq_pair.mp (largePrime_injective _ h)
      congr 1
      exact Prod.ext (Fin.ext hpair.1) (Fin.ext hpair.2)

theorem none_mem_controlIndices (H t : ℕ) : none ∈ controlIndices H t := by
  simp [controlIndices]

theorem some_mem_controlIndices_iff {H t : ℕ} (i : Fin (H + 1) × Fin H) :
    some i ∈ controlIndices H t ↔ (i.1 : ℕ) ≠ t := by
  simp [controlIndices]

theorem card_controlIndices_le (H t : ℕ) : (controlIndices H t).card ≤ H * (H + 1) + 1 := by
  classical
  calc
    (controlIndices H t).card ≤
        (((Finset.univ.filter fun x : Fin (H + 1) × Fin H => (x.1 : ℕ) ≠ t).image some).card + 1) :=
      Finset.card_insert_le _ _
    _ ≤ (Finset.univ : Finset (Fin (H + 1) × Fin H)).card + 1 :=
      Nat.add_le_add_right ((Finset.card_image_le).trans (Finset.card_filter_le _ _)) _
    _ = _ := by simp [Nat.mul_comm]

/-- All arithmetic input needed to turn the carry estimate into digit occurrences. -/
structure ControlProgression (b r H t A : ℕ) where
  n0 : ℕ
  Q : ℕ
  u0 : ℕ
  v : ℕ
  n0_pos : 0 < n0
  Q_pos : 0 < Q
  u0_pos : 0 < u0
  v_pos : 0 < v
  cofactor_coprime : Nat.Coprime u0 v
  cofactor_eq : ∀ m : ℕ, n0 + Q * m + t = 2 ^ (r * (A - 1)) * (u0 + v * m)
  cofactor_odd : ∀ m : ℕ, ¬ 2 ∣ u0 + v * m
  coeff_divisible : ∀ m j : ℕ, 1 ≤ j → j ≤ H → j ≠ t →
    b ^ j ∣ powerDivisorCoeff r (n0 + Q * m + j)
  mean_near : ∀ j : ℕ, H < j → j ≤ H ^ 3 →
    (∑' d, progressionDivisorWeight r Q (n0 + j) d) ≤ 2 * ((A : ℝ) + 1)
  mean_all : ∀ j : ℕ,
    (∑' d, progressionDivisorWeight r Q (n0 + j) d) ≤
      2 * ((A : ℝ) + 1) * ((b : ℝ) + 1) ^ (H * (H + 1))

theorem ControlProgression.target_coeff {b r H t A : ℕ}
    (c : ControlProgression b r H t A) (hr : r ≠ 0) (hA : 1 ≤ A) (m : ℕ)
    (hfree : PowerFree r (c.u0 + c.v * m)) :
    powerDivisorCoeff r (c.n0 + c.Q * m + t) = A := by
  rw [c.cofactor_eq m]
  exact powerDivisorCoeff_prime_pow_mul_powerFree hr Nat.prime_two hA
    (by have := c.u0_pos; omega) (c.cofactor_odd m) hfree

end PowerLambert
