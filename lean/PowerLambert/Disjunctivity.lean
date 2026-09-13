import PowerLambert.ArithmeticControlsConstruction
import PowerLambert.WordDensity
import PowerLambert.Irrationality

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical

namespace PowerLambert

/-- Every word is visited with positive lower density, with room to spare
from both endpoints of its cylinder. -/
theorem lambert_positiveLowerDensity_guardedWord {b r : ℕ}
    (hb : 2 ≤ b) (hr : 2 ≤ r) (l w : ℕ) (hw : w < b^l) :
    HasPositiveLowerDensity (fun n =>
      radixOrbit b (lambert b r) n ∈ guardedWordInterval b l w) := by
  have hb0 : (0 : ℝ)<b := by exact_mod_cast (show 0<b by omega)
  obtain ⟨H,ht,hH,hsmall⟩ := exists_small_control_tail b (l+1) hb
    (2*((((b*w+1 : ℕ) : ℝ))+1)) ((1/(2*(b : ℝ)^(l+1)))/16)
    (by positivity) (by positivity)
  obtain ⟨P⟩ := exists_controlProgression b r H (l+1) (b*w+1) hb hr (by omega) ht
  exact P.positiveLowerDensity_guardedWord hb hr hw ht hsmall

theorem HasPositiveLowerDensity.exists {P : ℕ → Prop}
    (h : HasPositiveLowerDensity P) : ∃ n, P n := by
  obtain ⟨δ,hδ,hN⟩ := h
  obtain ⟨N,hN⟩ := hN.exists
  have hpos : 0 < ((Finset.range N).filter P).card := by
    by_contra hn
    have hz : ((Finset.range N).filter P).card = 0 := by omega
    simp only [prefixDensity,hz,Nat.cast_zero,zero_div] at hN
    linarith
  obtain ⟨n,hn⟩ := Finset.card_pos.mp hpos
  exact ⟨n,(Finset.mem_filter.mp hn).2⟩

/-- Disjunctivity of every power-exponent Lambert sum in its defining base. -/
theorem lambert_disjunctive {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    DisjunctiveInBase b (lambert b r) := by
  refine ⟨hb,fun l w hw => ?_⟩
  obtain ⟨n,hn⟩ := (lambert_positiveLowerDensity_guardedWord hb hr l w hw).exists
  exact ⟨n,guardedWordInterval_subset_cylinder hb hw hn⟩

theorem lambert_irrational {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    Irrational (lambert b r) := (lambert_disjunctive hb hr).irrational

end PowerLambert
