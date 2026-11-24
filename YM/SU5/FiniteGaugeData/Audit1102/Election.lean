import YM.SU5.FiniteGaugeData.LocalLimit.Voyage
import YM.CF.Vp929.Roof.Fit

set_option autoImplicit false
noncomputable section
namespace YM.CF.Py.Rate.Audit1102
open YM.CF.Vale.Grace

/-- Instantiate the earlier election interface with the new finite-range law
from the final fixed-pivot replay, using the same regulated auxiliary map. -/
theorem available : AvailableΛ VolumeCape.Dream.Nimbus := by
  intro b d hb hd
  obtain ⟨N,l,k,u,hu,hub,G⟩ := VolumeCape.Dream.arch hb hd
  refine ⟨N,fun B hB => ⟨k,u,l,hu,hub,fun m _ => ?_⟩⟩
  exact G _ (hB.trans (show B.val ≤ m.val * 2 * B.val from
    Nat.le_mul_of_pos_left _ (Nat.mul_pos m.property two_pos)))

theorem fixed_pivot_with_law (ε : ℝ) :
    ∃ (P : LocalLimit.Preparation) (l : ℕ), ε < P.x ∧
      Nonempty (LocalLimit.Preparation.Course P (VolumeCape.Dream.Nimbus l)) := by
  obtain ⟨P,l,hx,h⟩ := LocalLimit.Preparation.elect ε available
  exact ⟨P,l,hx,LocalLimit.Preparation.enroll h⟩

end YM.CF.Py.Rate.Audit1102
