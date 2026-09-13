import PowerLambert.DynamicsFactor

noncomputable section
open Filter Set MeasureTheory
open scoped Topology

namespace PowerLambert

theorem ae_semiconj_iterates {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {T : X → X} {S : Y → Y} {φ : X → Y}
    (hT : MeasurePreserving T μ μ)
    (hcomm : ∀ᵐ x ∂μ, φ (T x) = S (φ x)) (n : ℕ) :
    ∀ᵐ x ∂μ, φ (T^[n] x) = S^[n] (φ x) := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun x => rfl
  | succ n ih =>
    filter_upwards [hT.quasiMeasurePreserving.ae ih,hcomm] with x hx hc
    rw [Function.iterate_succ_apply, hx, hc, Function.iterate_succ_apply]

theorem ae_all_semiconj_iterates {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {T : X → X} {S : Y → Y} {φ : X → Y}
    (hT : MeasurePreserving T μ μ)
    (hcomm : ∀ᵐ x ∂μ, φ (T x) = S (φ x)) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, φ (T^[n] x) = S^[n] (φ x) :=
  ae_all_iff.mpr (ae_semiconj_iterates hT hcomm)

theorem modelRotation_iterate (r P : ℕ) (x : OrbitGroup r) :
    (modelRotation r)^[P] x = x + P • orbitGenerator r := by
  exact (add_left_iterate_apply (orbitGenerator r) x).trans (add_comm _ _)

end PowerLambert
