import YM.SU5.Reconstruction.Seams.Hole
/-! # analytic perpendicular check -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice
namespace Sail
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup CF.Floral
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder Classical
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a) (P : Forward S)
variable (x : Cross a) (hx : ‖x‖ ≤ 1)
variable (t:ℝ≥0)(p:0<t)(U V:H.Op)(L R:H)
local notation "ζ"=> transverse S P x hx t p
noncomputable def screen (z:ℂ) := inner ℂ L (U (transverse S P x hx t p z (V (transverse S P x hx t p (-z) R))))
lemma slack {b:ℝ} (h:t = Real.toNNReal b) (u:0<b) : (t:ℝ)=b:=by rw [h,Real.coe_toNNReal _ u.le]
lemma reversed {z:ℂ} (h : z∈ slit t) : -z∈ slit t:=by simpa [slit] using h
lemma slit_opens : Hol (slit t) (screen S P x hx t p U V L R):= by
  intro i h
  let H₁:= (transverse_anal S P x hx t p i h).differentiableAt; let H₂:= (transverse_anal S P x hx t p (-i) (reversed t h)).differentiableAt
  exact (((innerSL ℂ L).differentiableAt).comp i (U.differentiableAt.comp i (H₁.clm_apply (V.differentiableAt.comp _ ((H₂.comp i differentiableAt_id.neg).clm_apply (differentiableAt_const R)))))).differentiableWithinAt

lemma anchored_cost {v w:ℝ} (e:‖U‖≤v) (c:‖V‖≤w){z:ℂ}(p':z∈ slit (t:ℝ)): ‖screen S P x hx t p U V L R z‖ ≤ ‖L‖*v*4*w*4*‖R‖:= by
  apply (norm_inner_le_norm ..).trans; repeat rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  let α:= transverse S P x hx t p
  change ‖U (α z (V (α (-z) R)))‖ ≤ _
  have hb : ‖V (α (-z) R)‖ ≤ w*(4*‖R‖):= (V.le_opNorm _).trans (mul_le_mul c (((α (-z)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (cost_strip _ _ _ _ _ _ _ (reversed t p')) (norm_nonneg _))) (norm_nonneg _) ((norm_nonneg _).trans c))
  apply (U.le_opNorm _).trans (mul_le_mul e _ (norm_nonneg _) ((norm_nonneg _).trans e))
  exact ((α z).le_opNorm _).trans (mul_le_mul (cost_strip _ _ _ _ _ _ _ p') hb (norm_nonneg _) (by norm_num))
end Sail
end YM.ConePrice
