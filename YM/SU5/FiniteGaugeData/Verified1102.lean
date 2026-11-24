import YM.SU5.FiniteGaugeData.Audit1102.Election
import YM.SU5.FiniteGaugeData.Audit1102.Loom
import YM.SU5.FiniteGaugeData.LocalLimit.GaugeOffer
import YM.SU5.FiniteGaugeData.LocalLimit.Physical
import YM.CF.Buffered.Theater
import YM.CF.Buffered.Prize

set_option autoImplicit false
noncomputable section
namespace YM.CF.Py.Rate.Audit1102
open MeasureTheory
open YM.SU5.FiniteGaugeData.Audit1102

/-- One fixed-pivot FiniteGaugeData course, with the Buffered spatial law at all its levels
and a common pair of subsequences for its gauge readings. -/
theorem elected_buffered_course (ε : ℝ) :
    ∃ (P : LocalLimit.Preparation) (l : ℕ), ε < P.x ∧
      ∃ Y : LocalLimit.Preparation.Course P (VolumeCape.Dream.Nimbus l),
        (∀ i j : ℕ, Buffered.Advance.LoomLaw ((Y.voyage i).CapeT j)
          (lawRadius (VolumeCape.Dream.plot l).C)) ∧
        ∃ u k : ℕ → ℕ, StrictMono u ∧ StrictMono k ∧ Nonempty (Y.Query u k) := by
  obtain ⟨P,l,hx,⟨Y⟩⟩ := fixed_pivot_with_law ε
  refine ⟨P,l,hx,Y,?_,?_⟩
  · intro i j
    apply nimbusLaw l _ ((Y.voyage i).craft j)
    intro V
    exact ((Y.voyage i).ownership j).paid.bill.comp (measurable_const.prodMk measurable_id)
  · exact Y.corners id id strictMono_id strictMono_id

end YM.CF.Py.Rate.Audit1102
