import PowerLambert.Basic
import PowerLambert.DynamicsMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
Weak convergence of the specified radix orbit implies convergence of word
frequencies whenever the limiting circle law is atomless. The elementary
circle representative and empirical-count arguments follow the previously
verified XiNormality/Cylinder.lean and XiNormality/Weyl.lean constructions.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology Classical ENNReal
set_option backward.isDefEq.respectTransparency false

namespace PowerLambert

def circleRepresentative (x : UnitAddCircle) : ℝ := AddCircle.equivIco 1 0 x

theorem circleRepresentative_coe (x : ℝ) :
    circleRepresentative (x : UnitAddCircle) = Int.fract x := by
  simp [circleRepresentative, AddCircle.coe_equivIco_mk_apply]

theorem coe_circleRepresentative (x : UnitAddCircle) :
    (circleRepresentative x : UnitAddCircle) = x := AddCircle.coe_equivIco

theorem measurable_circleRepresentative : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

theorem continuousAt_circleRepresentative {x : UnitAddCircle} (hx : x ≠ 0) :
    ContinuousAt circleRepresentative x :=
  continuousAt_subtype_val.comp (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hx)

private theorem mem_frontier_preimage_of_continuousAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set Y} {x : X} (hf : ContinuousAt f x)
    (hx : x ∈ frontier (f ⁻¹' s)) : f x ∈ frontier s := by
  rw [frontier_eq_closure_inter_closure] at hx ⊢
  exact ⟨closure_mono (image_preimage_subset f s) (mem_closure_image hf hx.1),
    closure_mono (image_preimage_subset f sᶜ) (mem_closure_image hf hx.2)⟩

def circleArc (a b : ℝ) : Set UnitAddCircle := circleRepresentative ⁻¹' Ico a b

theorem measurableSet_circleArc (a b : ℝ) : MeasurableSet (circleArc a b) :=
  measurable_circleRepresentative measurableSet_Ico

theorem frontier_circleArc_subset {a b : ℝ} (hab : a < b) :
    frontier (circleArc a b) ⊆ {0, (a : UnitAddCircle), (b : UnitAddCircle)} := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx' := mem_frontier_preimage_of_continuousAt
    (continuousAt_circleRepresentative hx0) hx
  rw [frontier_Ico hab, mem_insert_iff, mem_singleton_iff] at hx'
  rcases hx' with ha | hb
  · have : x = (a : UnitAddCircle) := by rw [← coe_circleRepresentative x, ha]
    simp [this]
  · have : x = (b : UnitAddCircle) := by rw [← coe_circleRepresentative x, hb]
    simp [this]

theorem circleArc_null_frontier (μ : Measure UnitAddCircle) [NullSingletonClass μ]
    {a b : ℝ} (hab : a < b) : μ (frontier (circleArc a b)) = 0 := by
  apply measure_mono_null (frontier_circleArc_subset hab)
  exact (((Set.finite_singleton (b : UnitAddCircle)).insert (a : UnitAddCircle)).insert 0).measure_zero μ

theorem circleArc_measure_pos (μ : Measure UnitAddCircle) [μ.IsOpenPosMeasure]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < μ (circleArc a b) := by
  let c : ℝ := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hc0 : 0 < c := ha.trans_lt hac
  have hc1 : c < 1 := hcb.trans_le hb
  have hrep : circleRepresentative (c : UnitAddCircle) = c := by
    rw [circleRepresentative_coe, Int.fract_eq_self.mpr ⟨hc0.le, hc1⟩]
  have hcircle : (c : UnitAddCircle) ≠ 0 := by
    intro heq
    have hzero : circleRepresentative (0 : UnitAddCircle) = 0 := by
      simpa using circleRepresentative_coe (0 : ℝ)
    rw [heq, hzero] at hrep
    exact hc0.ne' hrep.symm
  apply MeasureTheory.Measure.measure_pos_of_mem_nhds
  exact (continuousAt_circleRepresentative hcircle).preimage_mem_nhds
    (by rw [hrep]; exact Ico_mem_nhds hac hcb)

def empiricalCircle (u : ℕ → UnitAddCircle) (N : ℕ) : ProbabilityMeasure UnitAddCircle :=
  ProbabilityMeasure.map
    (⟨(PMF.uniformOfFintype (Fin (N + 1))).toMeasure, inferInstance⟩ :
      ProbabilityMeasure (Fin (N + 1))) (fun i => u i)

theorem empiricalCircle_apply (u : ℕ → UnitAddCircle) (N : ℕ)
    {s : Set UnitAddCircle} (hs : MeasurableSet s) :
    (empiricalCircle u N : Measure UnitAddCircle) s =
      (((Finset.range (N + 1)).filter (fun i => u i ∈ s)).card : ℝ≥0∞) / (N + 1) := by
  change (Measure.map (fun i : Fin (N + 1) => u i)
    (PMF.uniformOfFintype (Fin (N + 1))).toMeasure) s = _
  rw [Measure.map_apply (measurable_of_finite _) hs,
    PMF.toMeasure_uniformOfFintype_apply _ (measurable_of_finite _ hs)]
  simp only [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter,
    Nat.cast_add, Nat.cast_one, Set.mem_preimage]
  rw [Fin.sum_univ_eq_sum_range (fun i => if u i ∈ s then (1 : ℕ) else 0) (N + 1)]

/-- The all-prefix, overlapping word-frequency consequence of weak
convergence to any atomless law. -/
theorem circleArc_frequency_tendsto_of_weak_convergence
    (u : ℕ → UnitAddCircle) (ν : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (ν : Measure UnitAddCircle)]
    (h : Tendsto (empiricalCircle u) atTop (𝓝 ν))
    {a b : ℝ} (hab : a < b) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun i => u i ∈ circleArc a b)).card : ℝ) / N)
      atTop (𝓝 ((ν : Measure UnitAddCircle) (circleArc a b)).toReal) := by
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    h (circleArc_null_frontier (ν : Measure UnitAddCircle) hab)
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure UnitAddCircle) _)).comp hm
  have hden (N : ℕ) : ((N : ℝ≥0∞) + 1).toReal = (N : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  simp only [Function.comp_def, empiricalCircle_apply u _ (measurableSet_circleArc a b),
    ENNReal.toReal_div, ENNReal.toReal_natCast, hden] at hr
  exact (tendsto_add_atTop_iff_nat 1).mp (by simpa using hr)

def circleRadixOrbit (b : ℕ) (x : ℝ) (n : ℕ) : UnitAddCircle :=
  (((b : ℝ) ^ n * x : ℝ) : UnitAddCircle)

theorem wordFrequency_tendsto_of_weak_convergence
    {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (ν : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (ν : Measure UnitAddCircle)]
    (h : Tendsto (empiricalCircle (circleRadixOrbit b x)) atTop (𝓝 ν))
    (l w : ℕ) :
    Tendsto (wordFrequency b x l w) atTop
      (𝓝 ((ν : Measure UnitAddCircle)
        (circleArc ((w : ℝ) / (b : ℝ) ^ l) (((w : ℝ) + 1) / (b : ℝ) ^ l))).toReal) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hab : (w : ℝ) / (b : ℝ) ^ l < ((w : ℝ) + 1) / (b : ℝ) ^ l :=
    div_lt_div_of_pos_right (by linarith) (pow_pos hb' l)
  change Tendsto (fun N =>
    (((Finset.range N).filter (fun n => radixOrbit b x n ∈ cylinder b l w)).card : ℝ) / N)
    atTop _
  simpa only [wordFrequency, radixOrbit, cylinder, circleRadixOrbit, circleArc,
    Set.mem_preimage, circleRepresentative_coe] using
    circleArc_frequency_tendsto_of_weak_convergence (circleRadixOrbit b x) ν h hab

/-- Atomless full-support weak limits give positive limiting frequencies
for every finite word, in the exact predicates of the target theorem. -/
theorem positiveWordFrequencies_of_weak_convergence
    {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (ν : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (ν : Measure UnitAddCircle)]
    [(ν : Measure UnitAddCircle).IsOpenPosMeasure]
    (h : Tendsto (empiricalCircle (circleRadixOrbit b x)) atTop (𝓝 ν)) :
    PositiveWordFrequencies b x := by
  refine ⟨hb, fun l w hw => ?_⟩
  have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hp := pow_pos hb' l
  have ha : (0 : ℝ) ≤ w / (b : ℝ) ^ l := by positivity
  have hab : (w : ℝ) / (b : ℝ) ^ l < ((w : ℝ) + 1) / (b : ℝ) ^ l :=
    div_lt_div_of_pos_right (by linarith) hp
  have hbnd : ((w : ℝ) + 1) / (b : ℝ) ^ l ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    simpa using (show (w : ℝ) + 1 ≤ (b : ℝ) ^ l from
      by exact_mod_cast Nat.succ_le_of_lt hw)
  refine ⟨_, ?_, wordFrequency_tendsto_of_weak_convergence hb x ν h l w⟩
  exact ENNReal.toReal_pos (circleArc_measure_pos (ν : Measure UnitAddCircle) ha hab hbnd).ne'
    (measure_ne_top (ν : Measure UnitAddCircle) _)

end PowerLambert
