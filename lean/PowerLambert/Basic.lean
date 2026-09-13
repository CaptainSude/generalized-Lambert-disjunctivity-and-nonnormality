import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical

namespace PowerLambert

/-- The usual base-b radix orbit, indexed by overlapping starting positions. -/
def radixOrbit (b : ℕ) (x : ℝ) (n : ℕ) : ℝ := Int.fract ((b : ℝ) ^ n * x)

/-- The cylinder for the word of length l whose base-b value is w. -/
def cylinder (b l w : ℕ) : Set ℝ :=
  Ico ((w : ℝ) / (b : ℝ) ^ l) (((w : ℝ) + 1) / (b : ℝ) ^ l)

/-- Frequencies count all starting positions below N, including overlapping words. -/
def wordFrequency (b : ℕ) (x : ℝ) (l w N : ℕ) : ℝ :=
  ((Finset.range N).filter (fun n => radixOrbit b x n ∈ cylinder b l w)).card / (N : ℝ)

def NormalInBase (b : ℕ) (x : ℝ) : Prop :=
  2 ≤ b ∧ ∀ l w : ℕ, w < b ^ l →
    Tendsto (wordFrequency b x l w) atTop (𝓝 ((b : ℝ) ^ l)⁻¹)

def DisjunctiveInBase (b : ℕ) (x : ℝ) : Prop :=
  2 ≤ b ∧ ∀ l w : ℕ, w < b ^ l →
    ∃ n : ℕ, radixOrbit b x n ∈ cylinder b l w

def PositiveWordFrequencies (b : ℕ) (x : ℝ) : Prop :=
  2 ≤ b ∧ ∀ l w : ℕ, w < b ^ l →
    ∃ f : ℝ, 0 < f ∧ Tendsto (wordFrequency b x l w) atTop (𝓝 f)

theorem wordFrequency_nonneg (b : ℕ) (x : ℝ) (l w N : ℕ) :
    0 ≤ wordFrequency b x l w N := by
  unfold wordFrequency
  positivity

theorem PositiveWordFrequencies.disjunctive {b : ℕ} {x : ℝ}
    (h : PositiveWordFrequencies b x) : DisjunctiveInBase b x := by
  refine ⟨h.1, ?_⟩
  intro l w hw
  obtain ⟨f, hf, hlim⟩ := h.2 l w hw
  obtain ⟨N, hN⟩ := (hlim.eventually (lt_mem_nhds hf)).exists
  have hc : 0 < ((Finset.range N).filter
      (fun n => radixOrbit b x n ∈ cylinder b l w)).card := by
    by_contra hcard
    have hz : ((Finset.range N).filter
        (fun n => radixOrbit b x n ∈ cylinder b l w)).card = 0 := by omega
    simp only [wordFrequency, hz, Nat.cast_zero, zero_div] at hN
    exact (lt_irrefl 0) hN
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hc
  exact ⟨n, (Finset.mem_filter.mp hn).2⟩

end PowerLambert
