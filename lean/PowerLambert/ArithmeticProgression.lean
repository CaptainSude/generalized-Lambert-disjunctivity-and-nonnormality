import PowerLambert.Arithmetic

namespace PowerLambert

/-- A common divisor of the step and divisor must divide the offset. -/
theorem gcd_dvd_offset_of_dvd_progression {d Q a m : ℕ} (h : d ∣ a + Q * m) :
    Nat.gcd d Q ∣ a := by
  apply (Nat.dvd_add_iff_left ((Nat.gcd_dvd_right d Q).trans (dvd_mul_right Q m))).mpr
  exact (Nat.gcd_dvd_left d Q).trans h

theorem not_dvd_progression_of_not_gcd_dvd {d Q a : ℕ} (h : ¬ Nat.gcd d Q ∣ a)
    (m : ℕ) : ¬ d ∣ a + Q * m := fun hm => h (gcd_dvd_offset_of_dvd_progression hm)

/-- Solvability of a linear congruence in nonnegative progression coordinates. -/
theorem exists_dvd_progression {d Q a : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (ha : Nat.gcd d Q ∣ a) : ∃ v : ℕ, d ∣ a + Q * v := by
  let z := Nat.chineseRemainder' (n := d) (m := Q) (a := 0) (b := a) ha.zero_modEq_nat
  let N : ℕ := z + Q * d * a
  have haN : a ≤ N := by
    have hprod : 1 ≤ Q * d := Nat.mul_pos hQ hd
    have hm := Nat.mul_le_mul_right a hprod
    dsimp [N]
    omega
  have hmod : a ≡ N [MOD Q] := by
    have hx : Q * d * a ≡ 0 [MOD Q] :=
      ((dvd_mul_right Q d).trans (dvd_mul_right (Q * d) a)).modEq_zero_nat
    simpa only [Nat.add_zero] using (z.prop.2.add hx).symm
  obtain ⟨v, hv⟩ := (Nat.modEq_iff_exists_eq_add haN).mp hmod
  refine ⟨v, ?_⟩
  rw [← hv]
  apply dvd_add (Nat.modEq_zero_iff_dvd.mp z.prop.1)
  exact (dvd_mul_left d Q).trans (dvd_mul_right (Q * d) a)

theorem mul_modEq_of_modEq_div_gcd {d Q m v : ℕ}
    (h : m ≡ v [MOD d / Nat.gcd d Q]) : Q * m ≡ Q * v [MOD d] := by
  have hd : d ∣ Q * (d / Nat.gcd d Q) := by
    refine ⟨Q / Nat.gcd d Q, ?_⟩
    have h1 := Nat.div_mul_cancel (Nat.gcd_dvd_left d Q)
    have h2 := Nat.div_mul_cancel (Nat.gcd_dvd_right d Q)
    calc
      Q * (d / Nat.gcd d Q) =
          (Q / Nat.gcd d Q * Nat.gcd d Q) * (d / Nat.gcd d Q) := by rw [h2]
      _ = (d / Nat.gcd d Q * Nat.gcd d Q) * (Q / Nat.gcd d Q) := by ring
      _ = d * (Q / Nat.gcd d Q) := by rw [h1]
  exact (h.mul_left' Q).of_dvd hd

/-- Every solvable divisibility condition on a fixed progression is precisely one
residue class, with modulus `d / gcd d Q`. -/
theorem exists_progression_divisibility_residue {d Q a : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (ha : Nat.gcd d Q ∣ a) :
    ∃ v : ℕ, ∀ m : ℕ, d ∣ a + Q * m ↔ m ≡ v [MOD d / Nat.gcd d Q] := by
  obtain ⟨v, hv⟩ := exists_dvd_progression hd hQ ha
  refine ⟨v, fun m => ?_⟩
  constructor
  · intro hm
    have h : a + Q * m ≡ a + Q * v [MOD d] := hm.modEq_zero_nat.trans hv.zero_modEq_nat
    exact (h.add_left_cancel' a).cancel_left_div_gcd hd
  · intro hm
    have h := (mul_modEq_of_modEq_div_gcd hm).add_left a
    exact Nat.modEq_zero_iff_dvd.mp (h.trans hv.modEq_zero_nat)

theorem prime_not_dvd_coprime_progression {p u v m : ℕ} (hp : p.Prime)
    (huv : Nat.Coprime u v) (hpv : p ∣ v) : ¬ p ∣ u + v * m := by
  intro h
  have hpu : p ∣ u := (Nat.dvd_add_iff_left (hpv.trans (dvd_mul_right v m))).mpr h
  have : p ∣ 1 := by simpa [huv.gcd_eq_one] using Nat.dvd_gcd hpu hpv
  exact hp.not_dvd_one this

theorem prime_pow_not_dvd_coprime_progression {p r u v m : ℕ} (hr : r ≠ 0)
    (hp : p.Prime) (huv : Nat.Coprime u v) (hpv : p ∣ v) : ¬ p ^ r ∣ u + v * m := by
  intro h
  exact prime_not_dvd_coprime_progression hp huv hpv ((dvd_pow_self p hr).trans h)

end PowerLambert
