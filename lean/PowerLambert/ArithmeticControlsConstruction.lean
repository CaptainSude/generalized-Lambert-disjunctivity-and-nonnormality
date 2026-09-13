import PowerLambert.ArithmeticControls

open Finset
open scoped BigOperators

namespace PowerLambert

theorem exists_controlProgression (b r H t A : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r)
    (hA : 1 ≤ A) (ht : t ≤ H) : Nonempty (ControlProgression b r H t A) := by
  classical
  let S := controlIndices H t
  let p := controlPrime H
  let e := controlExponent (H := H) r b A
  let j := controlShift (H := H) t
  have hprime : ∀ i ∈ S, (p i).Prime := fun i _ => controlPrime_prime H i
  have hinj : Set.InjOn p S := (controlPrime_injective H).injOn
  have hnone : none ∈ S := none_mem_controlIndices H t
  obtain ⟨a, Q, hQ, ha, hQeq, hdiv, hvals⟩ :=
    exists_progression_prescribed_prime_valuations S p e j hprime hinj
  let n0 := a + Q
  have hn0 : 0 < n0 := by dsimp [n0]; omega
  have hval : ∀ m : ℕ, ∀ i ∈ S,
      (n0 + Q * m + j i).factorization (p i) = e i := by
    intro m i hi
    simpa only [n0, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hvals (m + 1) (by omega) i hi
  have htwo : Q.factorization 2 = r * (A - 1) + 1 := by
    rw [hQeq]
    simpa only [p, e, controlPrime, controlExponent] using
      factorization_prod_distinct_prime_powers S p e hprime hinj hnone
  have htwon : ∀ m : ℕ, (n0 + Q * m + t).factorization 2 = r * (A - 1) := by
    intro m
    simpa only [p, e, j, controlPrime, controlExponent, controlShift] using hval m none hnone
  have hQmembers : ∀ q : ℕ, q ∈ Q.primeFactors ↔ ∃ i ∈ S, q = p i := by
    intro q
    rw [hQeq]
    exact mem_primeFactors_prod_prime_powers S p e hprime
  have hQfacts : ∀ i ∈ S, Q.factorization (p i) = e i + 1 := by
    intro i hi
    rw [hQeq]
    exact factorization_prod_distinct_prime_powers S p e hprime hinj hi
  have hotherfacts : ∀ q ∈ Q.primeFactors, q ≠ 2 →
      Q.factorization q = r * (b - 1) + 1 := by
    intro q hq hq2
    obtain ⟨i, hi, rfl⟩ := (hQmembers q).mp hq
    cases i with
    | none => exact (hq2 rfl).elim
    | some i => exact hQfacts (some i) hi
  have hcard : Q.primeFactors.card - 1 ≤ H * (H + 1) := by
    have heq : Q.primeFactors.card = S.card := by
      rw [hQeq]
      exact card_primeFactors_prod_distinct_prime_powers S p e hprime hinj
    rw [heq]
    have h := card_controlIndices_le H t
    dsimp [S]
    omega
  have hcontrolDiv : ∀ m : ℕ, ∀ i : Fin (H + 1) × Fin H,
      some i ∈ S → p (some i) ∣ n0 + Q * m + (i.1 : ℕ) := by
    intro m i hi
    apply Nat.dvd_of_factorization_pos
    change (n0 + Q * m + j (some i)).factorization (p (some i)) ≠ 0
    rw [hval m (some i) hi]
    dsimp [e, controlExponent]
    exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
  let P := 2 ^ (r * (A - 1))
  have hP : 0 < P := pow_pos (by decide) _
  have hPn : P ∣ n0 + t := by
    apply (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : n0 + t ≠ 0)).mpr
    simpa using (htwon 0).ge
  have hPQ : P ∣ Q := by
    apply (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.ne_of_gt hQ)).mpr
    rw [htwo]
    omega
  let u0 := (n0 + t) / P
  let v := Q / P
  have hu0 : 0 < u0 := Nat.div_pos (Nat.le_of_dvd (by omega : 0 < n0 + t) hPn) hP
  have hv : 0 < v := Nat.div_pos (Nat.le_of_dvd hQ hPQ) hP
  have hPu : P * u0 = n0 + t := Nat.mul_div_cancel' hPn
  have hPv : P * v = Q := Nat.mul_div_cancel' hPQ
  have hcofactor : ∀ m : ℕ, n0 + Q * m + t = P * (u0 + v * m) := by
    intro m
    calc
      _ = (n0 + t) + Q * m := by ring
      _ = P * u0 + (P * v) * m := by rw [hPu, hPv]
      _ = _ := by ring
  have hodd : ∀ m : ℕ, ¬ 2 ∣ u0 + v * m := by
    intro m hm
    have hd : 2 ^ (r * (A - 1) + 1) ∣ n0 + Q * m + t := by
      rw [hcofactor m, pow_succ]
      exact Nat.mul_dvd_mul_left P hm
    have hh := (Nat.prime_two.pow_dvd_iff_le_factorization
      (by omega : n0 + Q * m + t ≠ 0)).mp hd
    rw [htwon m] at hh
    omega
  have hcop : Nat.Coprime u0 v := by
    by_contra hc
    obtain ⟨q, hqp, hqu, hqv⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hqQ : q ∣ Q := by
      rw [← hPv]
      exact hqv.trans (dvd_mul_left v P)
    obtain ⟨i, hi, rfl⟩ := (hQmembers q).mp (hqp.mem_primeFactors hqQ (Nat.ne_of_gt hQ))
    cases i with
    | none => exact hodd 0 (by simpa only [p, controlPrime, Nat.mul_zero, Nat.add_zero] using hqu)
    | some i =>
      have hneq : (i.1 : ℕ) ≠ t := (some_mem_controlIndices_iff i).mp hi
      have hlarge := controlPrime_some_large i
      have hjlt : (i.1 : ℕ) < p (some i) := by
        have hiH := i.1.isLt
        dsimp [p]
        omega
      have htlt : t < p (some i) := by dsimp [p]; omega
      have hdt : p (some i) ∣ n0 + t := by
        rw [← hPu]
        exact hqu.trans (dvd_mul_left u0 P)
      have hdj : p (some i) ∣ n0 + (i.1 : ℕ) := by
        simpa only [Nat.mul_zero, Nat.add_zero] using hcontrolDiv 0 i hi
      exact hneq (shifts_equal_of_prime_dvd hjlt htlt hdj hdt)
  have hcoeff : ∀ m k : ℕ, 1 ≤ k → k ≤ H → k ≠ t →
      b ^ k ∣ powerDivisorCoeff r (n0 + Q * m + k) := by
    intro m k hk1 hkH hkt
    let kf : Fin (H + 1) := ⟨k, by omega⟩
    let f : Fin H → ℕ := fun i => p (some (kf, i))
    let T : Finset ℕ := Finset.univ.image f
    have hf : Function.Injective f := by
      intro i i' h
      have h' := controlPrime_injective H h
      exact (Prod.mk.inj (Option.some.inj h')).2
    have hTcard : T.card = H := by
      rw [Finset.card_image_of_injective _ hf]
      simp
    have hTp : ∀ q ∈ T, q.Prime := by
      intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact hprime (some (kf, i)) (by simpa only [S, some_mem_controlIndices_iff] using hkt)
    have hTv : ∀ q ∈ T, (n0 + Q * m + k).factorization q = r * (b - 1) := by
      intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact hval m (some (kf, i)) (by simpa only [S, some_mem_controlIndices_iff] using hkt)
    have hd := pow_card_dvd_powerDivisorCoeff (by omega : r ≠ 0)
      (by omega : n0 + Q * m + k ≠ 0) hb T hTp hTv
    rw [hTcard] at hd
    exact (pow_dvd_pow b hkH).trans hd
  have hnear : ∀ k : ℕ, H < k → k ≤ H ^ 3 →
      (∑' d, progressionDivisorWeight r Q (n0 + k) d) ≤ 2 * ((A : ℝ) + 1) := by
    intro k hkH hkJ
    apply progression_mean_bound_nondividing_controls hr hQ hA htwo
    intro q hq hq2 hdq
    obtain ⟨i, hi, rfl⟩ := (hQmembers q).mp hq
    cases i with
    | none => exact hq2 rfl
    | some i =>
      have hlarge := controlPrime_some_large i
      have hiH := i.1.isLt
      have hilt : (i.1 : ℕ) < p (some i) := by dsimp [p]; omega
      have hklt : k < p (some i) := by dsimp [p]; omega
      have hdj : p (some i) ∣ n0 + (i.1 : ℕ) := by
        simpa only [Nat.mul_zero, Nat.add_zero] using hcontrolDiv 0 i hi
      have := shifts_equal_of_prime_dvd hilt hklt hdj hdq
      omega
  have hfar : ∀ k : ℕ, (∑' d, progressionDivisorWeight r Q (n0 + k) d) ≤
      2 * ((A : ℝ) + 1) * ((b : ℝ) + 1) ^ (H * (H + 1)) := by
    intro k
    apply (progression_mean_bound_all_shifts hr hQ hA hb htwo hotherfacts).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) b]) hcard
  exact ⟨⟨n0, Q, u0, v, hn0, hQ, hu0, hv, hcop, hcofactor, hodd, hcoeff, hnear, hfar⟩⟩

end PowerLambert
