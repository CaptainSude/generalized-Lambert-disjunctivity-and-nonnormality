import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite arithmetic for the power-exponent Lambert series.
The coefficient counts positive integers whose `r`th powers divide `n`.
-/

namespace PowerLambert

open Finset

def powerDivisorCoeff (r n : ℕ) : ℕ :=
  (Nat.floorRoot r n).divisors.card

def PowerFree (r n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ^ r ∣ n

theorem mem_powerDivisors {r n d : ℕ} (hr : r ≠ 0) (hn : n ≠ 0) :
    d ∈ (Nat.floorRoot r n).divisors ↔ d ^ r ∣ n := by
  rw [Nat.mem_divisors]
  exact ⟨fun h => Nat.pow_dvd_iff_dvd_floorRoot.mpr h.1,
    fun h => ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp h, Nat.floorRoot_ne_zero.mpr ⟨hr, hn⟩⟩⟩

theorem powerDivisorCoeff_eq_card_filter {r n : ℕ} (hr : r ≠ 0) (hn : n ≠ 0) :
    powerDivisorCoeff r n = ((Finset.Icc 1 n).filter fun d => d ^ r ∣ n).card := by
  unfold powerDivisorCoeff
  apply congrArg Finset.card
  ext d
  rw [mem_powerDivisors hr hn, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hd
    have hd0 : d ≠ 0 := by
      intro h
      simpa [h, hr, hn] using hd
    have hdle : d ≤ n := (Nat.le_self_pow hr d).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0, hdle⟩, hd⟩
  · exact fun h => h.2

theorem powerDivisorCoeff_le {r n : ℕ} (hr : r ≠ 0) (hn : n ≠ 0) :
    powerDivisorCoeff r n ≤ n := by
  rw [powerDivisorCoeff_eq_card_filter hr hn]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem powerDivisorCoeff_eq_prod {r n : ℕ} (hr : r ≠ 0) (hn : n ≠ 0) :
    powerDivisorCoeff r n = ∏ p ∈ n.primeFactors, (n.factorization p / r + 1) := by
  rw [powerDivisorCoeff, Nat.card_divisors (Nat.floorRoot_ne_zero.mpr ⟨hr, hn⟩)]
  simp only [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]
  apply Finset.prod_subset
  · apply Nat.primeFactors_mono _ hn
    exact (dvd_pow_self _ hr).trans Nat.floorRoot_pow_dvd
  · intro p hp hnot
    have hz : (Nat.floorRoot r n).factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hnot)
    simpa [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.floorDiv_eq_div] using
      congrArg (fun k : ℕ => k + 1) hz

/-- Distinct prime valuations independently contribute copies of `b` to the coefficient. -/
theorem pow_card_dvd_powerDivisorCoeff {r n b : ℕ} (hr : r ≠ 0) (hn : n ≠ 0)
    (hb : 2 ≤ b) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime)
    (hval : ∀ p ∈ S, n.factorization p = r * (b - 1)) :
    b ^ S.card ∣ powerDivisorCoeff r n := by
  have hsub : S ⊆ n.primeFactors := by
    intro p hps
    apply (hp p hps).mem_primeFactors _ hn
    apply Nat.dvd_of_factorization_pos
    rw [hval p hps]
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.pos_of_ne_zero hr) (by omega))
  rw [powerDivisorCoeff_eq_prod hr hn]
  have hd := Finset.prod_dvd_prod_of_subset S n.primeFactors
    (fun p => n.factorization p / r + 1) hsub
  have heq : (∏ p ∈ S, (n.factorization p / r + 1)) = b ^ S.card := by
    calc
      _ = ∏ _p ∈ S, b := by
        apply Finset.prod_congr rfl
        intro p hps
        rw [hval p hps, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr)]
        omega
      _ = _ := by simp
  rwa [heq] at hd

theorem powerFree_iff_factorization_lt {r n : ℕ} (hn : n ≠ 0) :
    PowerFree r n ↔ ∀ p : ℕ, p.Prime → n.factorization p < r := by
  constructor
  · intro h p hp
    exact Nat.lt_of_not_ge (fun hle => h p hp ((hp.pow_dvd_iff_le_factorization hn).mpr hle))
  · intro h p hp hd
    exact Nat.not_le_of_lt (h p hp) ((hp.pow_dvd_iff_le_factorization hn).mp hd)

theorem floorRoot_eq_one_of_powerFree {r n : ℕ} (hr : r ≠ 0) (hn : n ≠ 0)
    (hfree : PowerFree r n) : Nat.floorRoot r n = 1 := by
  apply Nat.factorization_inj (Nat.floorRoot_ne_zero.mpr ⟨hr, hn⟩) (by decide)
  ext p
  rw [Nat.factorization_floorRoot]
  by_cases hp : p.Prime
  · simp [Finsupp.floorDiv_def, Nat.div_eq_of_lt ((powerFree_iff_factorization_lt hn).mp hfree p hp)]
  · simp [Finsupp.floorDiv_def, Nat.factorization_eq_zero_of_not_prime n hp]

theorem powerDivisorCoeff_eq_one_of_powerFree {r n : ℕ} (hr : r ≠ 0) (hn : n ≠ 0)
    (hfree : PowerFree r n) : powerDivisorCoeff r n = 1 := by
  simp [powerDivisorCoeff, floorRoot_eq_one_of_powerFree hr hn hfree]

theorem floorRoot_prime_pow_mul_powerFree {r p k u : ℕ} (hr : r ≠ 0)
    (hp : p.Prime) (hu : u ≠ 0) (hpu : ¬ p ∣ u) (hfree : PowerFree r u) :
    Nat.floorRoot r (p ^ (r * k) * u) = p ^ k := by
  apply Nat.eq_of_factorization_eq
    (Nat.floorRoot_ne_zero.mpr ⟨hr, mul_ne_zero (pow_ne_zero _ hp.ne_zero) hu⟩)
    (pow_ne_zero _ hp.ne_zero)
  intro q
  rw [Nat.factorization_floorRoot, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hu,
    hp.factorization_pow, hp.factorization_pow]
  by_cases hqp : q = p
  · subst q
    simp [Finsupp.floorDiv_def, Nat.factorization_eq_zero_of_not_dvd hpu,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr)]
  · by_cases hq : q.Prime
    · simp [Finsupp.floorDiv_def, hqp,
        Nat.div_eq_of_lt ((powerFree_iff_factorization_lt hu).mp hfree q hq)]
    · simp [Finsupp.floorDiv_def, hqp,
        Nat.factorization_eq_zero_of_not_prime u hq]

theorem powerDivisorCoeff_prime_pow_mul_powerFree {r p A u : ℕ} (hr : r ≠ 0)
    (hp : p.Prime) (hA : 1 ≤ A) (hu : u ≠ 0) (hpu : ¬ p ∣ u)
    (hfree : PowerFree r u) :
    powerDivisorCoeff r (p ^ (r * (A - 1)) * u) = A := by
  rw [powerDivisorCoeff, floorRoot_prime_pow_mul_powerFree hr hp hu hpu hfree]
  rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  exact Nat.sub_add_cancel hA

/-- The congruence modulo one extra prime power fixes the valuation exactly. -/
theorem factorization_eq_of_modEq_prime_pow {n p e : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : n ≡ p ^ e [MOD p ^ (e + 1)]) : n.factorization p = e := by
  have hlow : p ^ e ∣ n := (h.dvd_iff (pow_dvd_pow p (Nat.le_succ e))).mpr dvd_rfl
  have hhigh : ¬ p ^ (e + 1) ∣ n := by
    rw [h.dvd_iff dvd_rfl]
    rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt]
    omega
  have hle := (hp.pow_dvd_iff_le_factorization hn).mp hlow
  have hlt : n.factorization p < e + 1 := by
    simpa only [hp.pow_dvd_iff_le_factorization hn, not_le] using hhigh
  omega

/-- A finite family of distinct primes can impose exact valuations at arbitrary
assigned shifts, simultaneously on one progression. -/
theorem exists_progression_prescribed_prime_valuations {ι : Type*} (S : Finset ι)
    (p e j : ι → ℕ) (hp : ∀ i ∈ S, (p i).Prime)
    (hdist : Set.InjOn p S) :
    ∃ a Q : ℕ, 0 < Q ∧ a < Q ∧
      Q = ∏ i ∈ S, p i ^ (e i + 1) ∧
      (∀ i ∈ S, p i ^ (e i + 1) ∣ Q) ∧
      ∀ m : ℕ, 0 < m → ∀ i ∈ S,
        (a + Q * m + j i).factorization (p i) = e i := by
  classical
  let q : ι → ℕ := fun i => p i ^ (e i + 1)
  let z : ι → ℕ := fun i => p i ^ e i + q i - j i % q i
  have hq : ∀ i ∈ S, q i ≠ 0 := fun i hi => pow_ne_zero _ (hp i hi).ne_zero
  have hpair : Set.Pairwise (↑S : Set ι) (fun i k => Nat.Coprime (q i) (q k)) := by
    intro i hi k hk hik
    exact ((Nat.coprime_primes (hp i hi) (hp k hk)).mpr
      (fun h => hik (hdist hi hk h))).pow _ _
  let a := Nat.chineseRemainderOfFinset z q S hq hpair
  let Q := ∏ i ∈ S, q i
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr hq
  have hdiv : ∀ i ∈ S, q i ∣ Q := fun i hi => Finset.dvd_prod_of_mem q hi
  refine ⟨a, Q, Nat.pos_of_ne_zero hQ,
    Nat.chineseRemainderOfFinset_lt_prod z q hq hpair, rfl, hdiv, ?_⟩
  intro m hm i hi
  have hn : (a : ℕ) + Q * m + j i ≠ 0 := by
    have := Nat.mul_pos (Nat.pos_of_ne_zero hQ) hm
    omega
  apply factorization_eq_of_modEq_prime_pow (hp i hi) hn
  have hqm : Q * m ≡ 0 [MOD q i] := ((hdiv i hi).trans (dvd_mul_right Q m)).modEq_zero_nat
  have hprog : (a : ℕ) + Q * m ≡ z i [MOD q i] := by
    simpa only [Nat.add_zero] using ((Nat.ModEq.refl (a : ℕ)).add hqm).trans (a.prop i hi)
  have hj : j i % q i ≤ p i ^ e i + q i :=
    (Nat.mod_lt _ (Nat.pos_of_ne_zero (hq i hi))).le.trans (Nat.le_add_left _ _)
  calc
    (a : ℕ) + Q * m + j i ≡ z i + j i % q i [MOD q i] :=
      hprog.add (Nat.mod_modEq _ _).symm
    _ = p i ^ e i + q i := Nat.sub_add_cancel hj
    _ ≡ p i ^ e i [MOD q i] := by simp [Nat.ModEq]

end PowerLambert
