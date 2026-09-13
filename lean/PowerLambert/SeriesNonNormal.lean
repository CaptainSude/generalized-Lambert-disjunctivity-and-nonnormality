import PowerLambert.SeriesOrbit
import PowerLambert.SeriesTail
import PowerLambert.Dynamics
import PowerLambert.DynamicsFrequencies
import Mathlib.Analysis.Normed.Group.AddCircle

noncomputable section
open scoped BigOperators Topology Classical
open Filter Finset Set

namespace PowerLambert

lemma circleRadixOrbit_eq_coe_radixOrbit (b : ℕ) (x : ℝ) (n : ℕ) :
    circleRadixOrbit b x n = (radixOrbit b x n : UnitAddCircle) := by
  simp only [circleRadixOrbit, radixOrbit, AddCircle.coe_fract]

lemma circleRadixOrbit_add (b : ℕ) (x : ℝ) (n P : ℕ) :
    circleRadixOrbit b x (n + P) = (b ^ P) • circleRadixOrbit b x n := by
  simp only [circleRadixOrbit, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_pow, pow_add]
  congr 1
  ring

lemma circle_coe_sub_nat (x : ℝ) (k : ℕ) :
    ((x - k : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [AddCircle.coe_sub]
  have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨(k : ℤ), by simp⟩
  rw [hk, sub_zero]

lemma circle_dist_le_abs (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

lemma circle_dist_ge_of_sub {x y δ : ℝ} (hδ : 0 < δ)
    (hlo : δ ≤ y - x) (hhi : y - x ≤ 1 - δ) :
    δ ≤ dist (x : UnitAddCircle) (y : UnitAddCircle) := by
  rw [dist_comm, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq,
    abs_sub_round_eq_min, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact le_min hlo (by linarith)

def separatedWord (b k : ℕ) : ℕ := b + b ^ 2 * k

lemma separatedWord_add_one_le {b P k : ℕ} (hb : 2 ≤ b) (hP : 2 ≤ P)
    (hk : k < b ^ (P - 2)) : separatedWord b k + 1 ≤ b ^ P := by
  have hsmall : b + 1 ≤ b ^ 2 := by nlinarith [sq_nonneg (b - 1 : ℤ)]
  have hpower : b ^ P = b ^ 2 * b ^ (P - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpower, separatedWord]
  have hm := Nat.mul_le_mul_left (b ^ 2) (show k + 1 ≤ b ^ (P - 2) by omega)
  nlinarith

lemma separatedWord_valid {b P k : ℕ} (hb : 2 ≤ b) (hP : 2 ≤ P)
    (hk : k < b ^ (P - 2)) : separatedWord b k < b ^ (P + 2) := by
  have h := separatedWord_add_one_le hb hP hk
  exact (show separatedWord b k < b ^ P by omega).trans_le
    (pow_le_pow_right₀ (by omega : 1 ≤ b) (by omega : P ≤ P + 2))

lemma cylinder_unique {b l u v : ℕ} (hb : 2 ≤ b) {z : ℝ}
    (hu : z ∈ cylinder b l u) (hv : z ∈ cylinder b l v) : u = v := by
  have hpow : (0 : ℝ) < (b : ℝ) ^ l := by positivity
  have hul := (div_le_iff₀ hpow).mp hu.1
  have huh := (lt_div_iff₀ hpow).mp hu.2
  have hvl := (div_le_iff₀ hpow).mp hv.1
  have hvh := (lt_div_iff₀ hpow).mp hv.2
  have h₁ : (u : ℝ) < v + 1 := by linarith
  have h₂ : (v : ℝ) < u + 1 := by linarith
  have h₁' : u < v + 1 := by exact_mod_cast h₁
  have h₂' : v < u + 1 := by exact_mod_cast h₂
  omega

lemma separatedWord_lag_distance {b P k n : ℕ} {x : ℝ}
    (hb : 2 ≤ b) (hP : 2 ≤ P) (hk : k < b ^ (P - 2))
    (hword : radixOrbit b x n ∈ cylinder b (P + 2) (separatedWord b k)) :
    (1 : ℝ) / (b : ℝ) ^ 2 ≤
      dist (circleRadixOrbit b x n) (circleRadixOrbit b x (n + P)) := by
  let z := radixOrbit b x n
  let y := (b : ℝ) ^ P * z - k
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hpow : (0 : ℝ) < (b : ℝ) ^ (P + 2) := pow_pos hb0 _
  have hsq : (0 : ℝ) < (b : ℝ) ^ 2 := pow_pos hb0 _
  have hz0 : 0 ≤ z := Int.fract_nonneg _
  have hzend : z ≤ 1 / (b : ℝ) ^ 2 := by
    have hw : ((separatedWord b k : ℕ) : ℝ) + 1 ≤ (b : ℝ) ^ P := by
      exact_mod_cast separatedWord_add_one_le hb hP hk
    calc
      z ≤ ((separatedWord b k : ℝ) + 1) / (b : ℝ) ^ (P + 2) := hword.2.le
      _ ≤ (b : ℝ) ^ P / (b : ℝ) ^ (P + 2) := div_le_div_of_nonneg_right hw hpow.le
      _ = _ := by rw [pow_add]; field_simp
  have hzsq : z * (b : ℝ) ^ 2 ≤ 1 := (le_div_iff₀ hsq).mp hzend
  have hlo := (div_le_iff₀ hpow).mp hword.1
  have hhi := (lt_div_iff₀ hpow).mp hword.2
  simp only [separatedWord, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, pow_add] at hlo hhi
  have hylo : (b : ℝ) ≤ y * (b : ℝ) ^ 2 := by dsimp [y, z]; nlinarith [hlo]
  have hyhi : y * (b : ℝ) ^ 2 ≤ (b : ℝ) + 1 := by dsimp [y, z]; nlinarith [hhi]
  have hl : (1 : ℝ) / (b : ℝ) ^ 2 ≤ y - z := by
    apply (div_le_iff₀ hsq).mpr
    nlinarith
  have hh : y - z ≤ 1 - 1 / (b : ℝ) ^ 2 := by
    have hsquare : (b : ℝ) + 2 ≤ (b : ℝ) ^ 2 := by nlinarith
    have hnonneg : 0 ≤ z * (b : ℝ) ^ 2 := mul_nonneg hz0 hsq.le
    calc
      y - z ≤ ((b : ℝ) ^ 2 - 1) / (b : ℝ) ^ 2 := (le_div_iff₀ hsq).mpr (by nlinarith)
      _ = _ := by field_simp
  have hleft : circleRadixOrbit b x n = (z : UnitAddCircle) :=
    circleRadixOrbit_eq_coe_radixOrbit _ _ _
  have hright : circleRadixOrbit b x (n + P) = (y : UnitAddCircle) := by
    rw [circleRadixOrbit_add, hleft, ← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_pow]
    exact (circle_coe_sub_nat _ k).symm
  rw [hleft, hright]
  exact circle_dist_ge_of_sub (by positivity) hl hh

def lagWordMean (b : ℕ) (x : ℝ) (P N : ℕ) : ℝ :=
  (1 / (b : ℝ) ^ 2) *
    ∑ k ∈ range (b ^ (P - 2)), wordFrequency b x (P + 2) (separatedWord b k) N

lemma lagWordMean_le_lag_distance {b P : ℕ} {x : ℝ} (hb : 2 ≤ b) (hP : 2 ≤ P)
    (N : ℕ) :
    lagWordMean b x P N ≤
      sequenceMean (fun n => dist (circleRadixOrbit b x n) (circleRadixOrbit b x (n + P))) N := by
  let δ : ℝ := 1 / (b : ℝ) ^ 2
  let S := range (b ^ (P - 2))
  let f : ℕ → ℕ → ℝ := fun n k =>
    if radixOrbit b x n ∈ cylinder b (P + 2) (separatedWord b k) then δ else 0
  have hf : ∀ n, (∑ k ∈ S, f n k) ≤
      dist (circleRadixOrbit b x n) (circleRadixOrbit b x (n + P)) := by
    intro n
    by_cases hex : ∃ k ∈ S, radixOrbit b x n ∈ cylinder b (P + 2) (separatedWord b k)
    · obtain ⟨k, hk, hkw⟩ := hex
      have hsum : (∑ j ∈ S, f n j) = δ := by
        rw [sum_eq_single k]
        · simp [f, hkw]
        · intro j hj hjk
          have hn : ¬ radixOrbit b x n ∈ cylinder b (P + 2) (separatedWord b j) := by
            intro hjw
            have heq := cylinder_unique hb hjw hkw
            dsimp [separatedWord] at heq
            exact hjk (Nat.eq_of_mul_eq_mul_left (by positivity : 0 < b ^ 2) (Nat.add_left_cancel heq))
          simp [f, hn]
        · intro hnot
          exact (hnot hk).elim
      rw [hsum]
      exact separatedWord_lag_distance hb hP (mem_range.mp hk) hkw
    · have hn : ∀ k ∈ S, ¬ radixOrbit b x n ∈ cylinder b (P + 2) (separatedWord b k) := by
        intro k hk hw
        exact hex ⟨k, hk, hw⟩
      have hz : (∑ k ∈ S, f n k) = 0 := sum_eq_zero (fun k hk => by simp [f, hn k hk])
      rw [hz]
      exact dist_nonneg
  have hmean : sequenceMean (fun n => ∑ k ∈ S, f n k) N = lagWordMean b x P N := by
    unfold sequenceMean lagWordMean
    rw [sum_comm, sum_div, mul_sum]
    apply sum_congr rfl
    intro k hk
    have hsum : (∑ n ∈ range N, f n k) =
        δ * (((range N).filter fun n => radixOrbit b x n ∈ cylinder b (P + 2) (separatedWord b k)).card : ℝ) := by
      dsimp [f]
      rw [← sum_filter]
      simp [mul_comm]
    rw [hsum]
    unfold wordFrequency
    dsimp [δ]
    ring
  rw [← hmean]
  exact sequenceMean_mono hf N

lemma normal_lagWordMean_tendsto {b P : ℕ} {x : ℝ} (hnormal : NormalInBase b x)
    (hP : 2 ≤ P) :
    Tendsto (lagWordMean b x P) atTop (𝓝 (((b : ℝ) ^ 6)⁻¹)) := by
  have hb := hnormal.1
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hs : Tendsto (fun N : ℕ =>
      ∑ k ∈ range (b ^ (P - 2)), wordFrequency b x (P + 2) (separatedWord b k) N) atTop
      (𝓝 (∑ _k ∈ range (b ^ (P - 2)), ((b : ℝ) ^ (P + 2))⁻¹)) := by
    apply tendsto_finsetSum
    intro k hk
    exact hnormal.2 _ _ (separatedWord_valid hb hP (mem_range.mp hk))
  have hvalue : (1 / (b : ℝ) ^ 2) *
      (∑ _k ∈ range (b ^ (P - 2)), ((b : ℝ) ^ (P + 2))⁻¹) = ((b : ℝ) ^ 6)⁻¹ := by
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_pow]
    rw [show P + 2 = (P - 2) + 4 by omega, pow_add]
    field_simp
    <;> ring
  have hlim := hs.const_mul (1 / (b : ℝ) ^ 2)
  rw [hvalue] at hlim
  exact hlim

theorem not_normal_of_circle_periodic_approximation {b : ℕ} {x : ℝ}
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, 0 < P ∧ ∃ v : ℕ → UnitAddCircle,
      Function.Periodic v P ∧ ∀ N, 0 < N →
        sequenceMean (fun n => dist (circleRadixOrbit b x n) (v n)) N ≤ ε) :
    ¬ NormalInBase b x := by
  intro hnormal
  let c : ℝ := ((b : ℝ) ^ 6)⁻¹
  have hc : 0 < c := by
    dsimp [c]
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by have := hnormal.1; omega)
    positivity
  obtain ⟨P₀, hP₀, v, hv, herr⟩ := happrox (c / 4) (by positivity)
  let P := 2 * P₀
  have hP : 2 ≤ P := by dsimp [P]; omega
  have hvP : Function.Periodic v P := hv.nat_mul 2
  have hratio : Tendsto (fun N : ℕ => (((N + P : ℕ) : ℝ) / N)) atTop (𝓝 1) := by
    have hz : Tendsto (fun N : ℕ => (P : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have ho : Tendsto (fun N : ℕ => 1 + (P : ℝ) / N) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hz
    apply ho.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [Nat.cast_add, add_div, hn]
  have hup : Tendsto (fun N : ℕ => 2 * (c / 4) * (((N + P : ℕ) : ℝ) / N))
      atTop (𝓝 (2 * (c / 4))) := by simpa using hratio.const_mul (2 * (c / 4))
  have hle : c ≤ 2 * (c / 4) := by
    apply le_of_tendsto_of_tendsto (normal_lagWordMean_tendsto hnormal hP) hup
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (lagWordMean_le_lag_distance hnormal.1 hP N).trans
      (sequenceMean_periodic_lag_distance_le (circleRadixOrbit b x) v P N hvP
        (herr (N + P) (by omega)) hN)
  linarith

theorem circleRadixOrbit_lambert_periodic_approximation {b r : ℕ}
    (hb : 2 ≤ b) (hr : 2 ≤ r) :
    ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, 0 < P ∧ ∃ v : ℕ → UnitAddCircle,
      Function.Periodic v P ∧ ∀ N, 0 < N →
        sequenceMean (fun n => dist (circleRadixOrbit b (lambert b r) n) (v n)) N ≤ ε := by
  intro ε hε
  obtain ⟨P, u, hP, hu, herr⟩ := exists_periodic_orbit_approximation hb hr hε
  refine ⟨P, hP, (fun n => (u n : UnitAddCircle)), ?_, ?_⟩
  · intro n
    exact congrArg (fun z : ℝ => (z : UnitAddCircle)) (hu n)
  · intro N hN
    have hcircle : ∀ n, circleRadixOrbit b (lambert b r) n = (orbitSeries b r n : UnitAddCircle) := by
      intro n
      have h := congrArg (fun z : ℝ => (z : UnitAddCircle)) (fract_radix_eq_orbitSeries hb hr n)
      simpa only [AddCircle.coe_fract, circleRadixOrbit] using h
    have hmean : sequenceMean (fun n => dist (circleRadixOrbit b (lambert b r) n) (u n : UnitAddCircle)) N ≤
        sequenceMean (fun n => |orbitSeries b r n - u n|) N := by
      apply sequenceMean_mono
      intro n
      rw [hcircle]
      exact circle_dist_le_abs _ _
    exact hmean.trans (herr N hN).le

theorem lambert_not_normal {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    ¬ NormalInBase b (lambert b r) :=
  not_normal_of_circle_periodic_approximation (circleRadixOrbit_lambert_periodic_approximation hb hr)

end PowerLambert
