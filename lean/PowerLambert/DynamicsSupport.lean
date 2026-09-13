import PowerLambert.DynamicsFrequencies
import PowerLambert.WordVisits
import PowerLambert.DensityTransfer

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology Classical ENNReal
set_option backward.isDefEq.respectTransparency false

namespace PowerLambert

/-- A closed set visited with positive lower density has positive mass in every
weak empirical limit. The null-set case is a continuity set automatically. -/
theorem measure_closed_pos_of_positiveLowerDensity (u : ℕ → UnitAddCircle)
    (ν : ProbabilityMeasure UnitAddCircle)
    (hweak : Tendsto (empiricalCircle u) atTop (𝓝 ν))
    {K : Set UnitAddCircle} (hK : IsClosed K)
    (hvisits : HasPositiveLowerDensity (fun n => u n ∈ K)) :
    0 < (ν : Measure UnitAddCircle) K := by
  by_contra hpos
  have hzero : (ν : Measure UnitAddCircle) K = 0 := by
    exact le_antisymm (not_lt.mp hpos) bot_le
  have hf : (ν : Measure UnitAddCircle) (frontier K) = 0 :=
    measure_mono_null hK.frontier_subset hzero
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hf
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure UnitAddCircle) K)).comp hm
  have hden (N : ℕ) : ((N : ℝ≥0∞) + 1).toReal = (N : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  simp only [Function.comp_def, empiricalCircle_apply u _ hK.measurableSet,
    ENNReal.toReal_div, ENNReal.toReal_natCast, hden, hzero, ENNReal.toReal_zero] at hreal
  have hlim : Tendsto (prefixDensity (fun n => u n ∈ K)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp (by simpa [prefixDensity] using hreal)
  obtain ⟨δ, hδ, hdensity⟩ := hvisits
  obtain ⟨N, hN, hsmall⟩ := (hdensity.and (hlim.eventually (gt_mem_nhds hδ))).exists
  exact (not_lt_of_ge hN) hsmall

/-- Radix cells of sufficiently fine level fit inside any real neighborhood
of a point strictly between zero and one. -/
theorem exists_radix_cell_subset_ball {b : ℕ} (hb : 2 ≤ b) {x ε : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hε : 0 < ε) :
    ∃ l w : ℕ, w < b ^ l ∧
      Icc ((w : ℝ) / (b : ℝ) ^ l) (((w : ℝ) + 1) / (b : ℝ) ^ l) ⊆ Metric.ball x ε := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have ht : Tendsto (fun l : ℕ => (1 : ℝ) / (b : ℝ) ^ l) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hbR)
  obtain ⟨l, hl⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  let w := Nat.floor (x * (b : ℝ) ^ l)
  have hp : (0 : ℝ) < (b : ℝ) ^ l := pow_pos (by linarith) _
  have hxp : 0 ≤ x * (b : ℝ) ^ l := mul_nonneg hx0.le hp.le
  have hwle : (w : ℝ) ≤ x * (b : ℝ) ^ l := Nat.floor_le hxp
  have hwlt : x * (b : ℝ) ^ l < (w : ℝ) + 1 := Nat.lt_floor_add_one _
  have hw : w < b ^ l := by
    have hwr : (w : ℝ) < (b : ℝ) ^ l := by nlinarith
    exact_mod_cast hwr
  refine ⟨l, w, hw, ?_⟩
  intro y hy
  have hylo := (div_le_iff₀ hp).mp hy.1
  have hyhi := (le_div_iff₀ hp).mp hy.2
  have hinv : (1 / (b : ℝ) ^ l) * (b : ℝ) ^ l = 1 := div_mul_cancel₀ _ hp.ne'
  have hlo : x - 1 / (b : ℝ) ^ l < y := by
    apply (mul_lt_mul_iff_right₀ hp).mp
    nlinarith
  have hhi : y ≤ x + 1 / (b : ℝ) ^ l := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem nonempty_circle_open_has_interior_representative {O : Set UnitAddCircle}
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ (x : UnitAddCircle) ∈ O := by
  obtain ⟨y, hy⟩ := hne
  let x := circleRepresentative y
  have hx0 : 0 ≤ x := (AddCircle.equivIco (1 : ℝ) 0 y).property.1
  have hx1 : x < 1 := by
    simpa only [x, circleRepresentative, zero_add] using
      (AddCircle.equivIco (1 : ℝ) 0 y).property.2
  have hxO : (x : UnitAddCircle) ∈ O := by simpa only [x, coe_circleRepresentative] using hy
  by_cases hxpos : 0 < x
  · exact ⟨x, hxpos, hx1, hxO⟩
  · have hx : x = 0 := le_antisymm (not_lt.mp hxpos) hx0
    have hpre : IsOpen ((fun z : ℝ => (z : UnitAddCircle)) ⁻¹' O) :=
      hO.preimage (AddCircle.continuous_mk' (1 : ℝ))
    have hzero : (0 : ℝ) ∈ ((fun z : ℝ => (z : UnitAddCircle)) ⁻¹' O) := by
      simpa only [Set.mem_preimage, ← hx] using hxO
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hpre.mem_nhds hzero)
    let z : ℝ := min (ε / 2) (1 / 2)
    have hz0 : 0 < z := lt_min (by linarith) (by norm_num)
    have hz1 : z < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hzε : z < ε := (min_le_left _ _).trans_lt (by linarith)
    refine ⟨z, hz0, hz1, hball ?_⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hz0] using hzε

/-- Every nonempty circle open set contains one of the guarded closed word intervals. -/
theorem exists_guardedWordInterval_image_subset {b : ℕ} (hb : 2 ≤ b)
    {O : Set UnitAddCircle} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ l w : ℕ, w < b ^ l ∧
      (fun x : ℝ => (x : UnitAddCircle)) '' guardedWordInterval b l w ⊆ O := by
  obtain ⟨x, hx0, hx1, hxO⟩ := nonempty_circle_open_has_interior_representative hO hne
  have hpre := hO.preimage (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hpre.mem_nhds hxO)
  obtain ⟨l, w, hw, hcell⟩ := exists_radix_cell_subset_ball hb hx0 hx1 hε
  refine ⟨l, w, hw, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hc := guardedWordInterval_subset_cylinder hb hw hy
  exact hball (hcell ⟨hc.1, hc.2.le⟩)

/-- The arithmetic lower-density theorem supplies full support to the actual-orbit
limiting measure, without any assumption of atomlessness. -/
theorem isOpenPosMeasure_of_guarded_word_visits {b : ℕ} (hb : 2 ≤ b) (x : ℝ)
    (ν : ProbabilityMeasure UnitAddCircle)
    (hweak : Tendsto (empiricalCircle (circleRadixOrbit b x)) atTop (𝓝 ν))
    (hvisits : ∀ l w : ℕ, w < b ^ l →
      HasPositiveLowerDensity (fun n => radixOrbit b x n ∈ guardedWordInterval b l w)) :
    (ν : Measure UnitAddCircle).IsOpenPosMeasure := by
  constructor
  intro O hO hne
  obtain ⟨l, w, hw, hsub⟩ := exists_guardedWordInterval_image_subset hb hO hne
  let K : Set UnitAddCircle := (fun y : ℝ => (y : UnitAddCircle)) '' guardedWordInterval b l w
  have hK : IsClosed K :=
    ((isCompact_guardedWordInterval b l w).image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hKv : HasPositiveLowerDensity (fun n => circleRadixOrbit b x n ∈ K) := by
    apply (hvisits l w hw).mono
    intro n hn
    refine ⟨radixOrbit b x n, hn, ?_⟩
    have hrep := coe_circleRepresentative (circleRadixOrbit b x n)
    simpa only [circleRadixOrbit, circleRepresentative_coe, radixOrbit] using hrep
  have hpos := measure_closed_pos_of_positiveLowerDensity (circleRadixOrbit b x) ν hweak hK hKv
  exact (hpos.trans_le (measure_mono hsub)).ne'

end PowerLambert
