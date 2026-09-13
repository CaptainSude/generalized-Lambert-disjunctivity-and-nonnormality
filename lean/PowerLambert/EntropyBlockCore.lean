import PowerLambert.EntropyDefs
import Mathlib.Data.Nat.Periodic

noncomputable section
open Function Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical

namespace PowerLambert

lemma entropy_comp_measurePreserving {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {μ : Measure Ω}
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {X : Ω → S} (hX : Measurable X) :
    entropy (X ∘ T) μ = entropy X μ := by
  unfold entropy
  rw [← Measure.map_map hX hT.measurable, hT.map_eq]

lemma entropy_labelBlock_le_mul {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {X : Ω → S} (hX : Measurable X) (n : ℕ) :
    entropy (labelBlock T X n) μ ≤ (n : ℝ) * entropy X μ := by
  induction n with
  | zero =>
    have h := entropy_le_log_card (labelBlock T X 0) μ
    simpa using h
  | succ n ih =>
    let U : Ω → S × (Fin n → S) := fun ω => (X ω, labelBlock T X n (T ω))
    let R : S × (Fin n → S) → (Fin (n + 1) → S) := fun p => Fin.cons p.1 p.2
    have hblock := measurable_labelBlock hT.measurable hX n
    have hU : Measurable U := hX.prodMk (hblock.comp hT.measurable)
    have hrecover : labelBlock T X (n + 1) = R ∘ U := by
      funext ω i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [labelBlock, R, U]
      · simp [labelBlock, R, U, Function.iterate_succ_apply]
    calc
      _ = entropy (R ∘ U) μ := by rw [hrecover]
      _ ≤ entropy U μ := entropy_comp_le μ hU R
      _ ≤ entropy X μ + entropy ((labelBlock T X n) ∘ T) μ :=
        entropy_pair_le_add hX (hblock.comp hT.measurable) μ
      _ = entropy X μ + entropy (labelBlock T X n) μ := by
        rw [entropy_comp_measurePreserving hT hblock]
      _ ≤ (n + 1 : ℕ) * entropy X μ := by push_cast; linarith

lemma entropy_labelBlock_periodic_le {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : Measurable T)
    {Y : Ω → S} (hY : Measurable Y) {P : ℕ} (hP : 0 < P)
    (hperiod : ∀ ω, Y (T^[P] ω) = Y ω) (n : ℕ) :
    entropy (labelBlock T Y n) μ ≤ Real.log (Fintype.card (Fin P → S)) := by
  let R : (Fin P → S) → (Fin n → S) := fun w i => w ⟨i.val % P, Nat.mod_lt _ hP⟩
  have hrecover : labelBlock T Y n = R ∘ labelBlock T Y P := by
    funext ω i
    have hseq : Function.Periodic (fun j : ℕ => Y (T^[j] ω)) P := by
      intro j
      change Y (T^[j + P] ω) = Y (T^[j] ω)
      rw [Nat.add_comm, Function.iterate_add_apply]
      exact hperiod _
    exact (hseq.map_mod_nat i.val).symm
  rw [hrecover]
  exact (entropy_comp_le μ (measurable_labelBlock hT hY P) R).trans
    (entropy_le_log_card _ μ)


end PowerLambert

