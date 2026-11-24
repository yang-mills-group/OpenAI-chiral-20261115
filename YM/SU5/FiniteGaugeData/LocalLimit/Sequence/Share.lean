import YM.SU5.FiniteGaugeData.LocalLimit.Local.Card
set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox.BoxGauge
open RG Lattice Wilson Filter MeasureTheory Function
open scoped Topology BigOperators Classical BoundedContinuousFunction
variable {G:Gauge}{c f:Side}(S:StepData c f)(r:ℕ)(v:ℝ)(A: ↥(paper G r)) (T:Record G r)
local notation "η" => (weight r A:ℂ)
def markTicket (A:paper G r):Ticket G r:=
 ⟨((weight r A:ℂ))⁻¹ • A,(by rw [weight_scale,norm_inv,Complex.norm_real,Real.norm_of_nonneg (weight_pos r A)]; by_cases h:weight r A=0; simp [h]; rw [inv_mul_cancel₀ h])⟩
def share := η * T (markTicket r A)
lemma share_one(F : ↥(paper G r)→ℂ)(l:ℝ)(p:Used r S v F l)(h:0≤l): share r A (p.bank r S v F h) = F A:= by
 unfold share; change η * F (η⁻¹ • A)= _; rw [p.scalar]; by_cases t:weight r A=0; rw [t,Complex.ofReal_zero,zero_mul]; exact (p.zero_reads _ _ _ A t).symm; rw [←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr t),one_mul]
lemma share_cont : Continuous (share (G:=G) r A) := continuous_const.mul (by fun_prop)
end YM.Push.GridApprox.BoxGauge
