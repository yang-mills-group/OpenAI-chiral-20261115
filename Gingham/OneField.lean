import Velour.Organza.Larva
import YM.SU5.Registration.Unpad

/-! # A passport fields-to-pockets comparison
Works on any of M8's `WPermit` instructions in a given orientation. No
stronger costs on the appointment. All field products on common vectors
(e.g. vacuum hereafter) then have their usual Velour determination, core etc.
Like M4, not calling these pockets spacelike yet. -/
set_option autoImplicit false
set_option maxRecDepth 2000

noncomputable section
namespace YM.OS.Semigroup.Gingham
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal Topology InnerProductSpace ComplexOrder

open SatinRegistration Boundary Probe CF.Buffered.Afterglow.Hierarchy.Seld

variable {H : Hilbert} {a : Axis} (S : Semigroup H a) (Q : ℝ≥0 → H.Op)

lemma credited (h : Sound S Q) (p : PadPaid Q) : S.Cashable Q := by
  obtain ⟨k,C,c,u⟩ := p
  let t : ℕ → ℝ≥0 := fun n=>((2^n:ℝ≥0))⁻¹
  refine ⟨h,t,C+1,2^k,by linarith,one_le_pow₀ (by norm_num),?_,?_,?_⟩
  · intro n; unfold t; positivity
  · intro n; unfold t; push_cast; rw [pow_succ,mul_inv]
    exact le_of_eq (div_eq_mul_inv .. |>.symm)
  · intro n
    have hp : 0<t n := by unfold t; positivity
    have hi := u _ hp (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
    change ((t n:ℝ))^k * ‖_‖ ≤ _ at hi
    have ht : (t n:ℝ)= (2^n:ℝ)⁻¹ := by unfold t; push_cast; rfl
    rw [ht, inv_pow, inv_mul_eq_div, ←pow_mul, mul_comm n, pow_mul] at hi
    exact (div_le_iff₀ (by positivity)).mp (hi.trans (by linarith : C ≤ C+1))

lemma same_R (X : H.Op) (f : Test4) :
    S.rasp X f = valise S X f := rfl
variable {S Q}

/-- Identification anywhere both prescriptions ask the price. Thus
applies recursively (e.g. to anything starting on the vacuum); and supplies
the actual fields on the full common support-graded domain in either prescription.
No spectral comparison beyond supplied translation rep. -/
theorem concord {T : S.Detector} (h : S.Instates Q T)
    (w : Sound S Q) (u : PadPaid Q)
    (f : Test4) (x : S.muslin) (y : radial S) (e : x.val=y.val) :
    (T f x).val = (SatinRegistration.field S Q w u f y).val := by
  let G := bands S
  have k : G.Approaches (𝓝[>] (0:ℝ≥0)) (fun _=>y) y := by
    intro k; simp only [sub_self,Grading.budget,Grading.due,map_zero,norm_zero,mul_zero,tsum_zero]
    exact tendsto_const_nhds
  refine tendsto_nhds_unique_of_eventuallyEq (h.meet f x)
    ((passes_lim S Q w u (𝓝[>] 0) f id id tendsto_id tendsto_id k).hilbert G) ?_
  refine Eventually.of_forall fun t=>?_
  dsimp only
  rw [same_R,warm_actual,e]
  have a : bothPads S Q t t = Q t := by
    simp only [bothPads, min_self, tsub_self, S.eZero, ← ContinuousLinearMap.one_def,one_mul,mul_one]
  simp only [id_eq,a]

end YM.OS.Semigroup.Gingham
