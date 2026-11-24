import YM.SU5.Reconstruction.Trap.Lantern
/-!
# Moves calibrated heat too. -/
set_option autoImplicit false
noncomputable section
namespace YM.Picket
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe
variable {H D K:Hilbert} {a b : Axis} (r:b≠a) (S:OS.Semigroup H a) (Q:OS.Semigroup D b) (C:Clasp K H D)
local notation "V" => (C.look.toContinuousLinearEquiv.toContinuousLinearMap)
variable (p:Paces b S) (q:Paces a Q)(h:Beam r S Q C)
local notation "U" => column S b
open Complex
noncomputable def maker (z:ℂ)(x:ℝ):= exp (-z*(max 0 x:ℝ))
private lemma contr (z:ℂ)(e:0≤z.re): Tag (maker z):= by
 refine ⟨by unfold maker; fun_prop,1,zero_le_one,fun x=>?_⟩; simp only [maker,norm_exp,mul_re,neg_re,Real.exp_le_one_iff,ofReal_im,ofReal_re,mul_zero,sub_zero]; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr e) (le_max_left ..)
private lemma make_column(b:Axis)(e:ℝ)(z:ℂ): order S.ℚmeasure (maker z ∘ (ticket a b e))=column S b e z:= by
 unfold column; congr 1; funext x; unfold comp maker slopeRay; rw [max_eq_right (positive ..)]; simp
include p q h
lemma ξshift (e:ℝ)(c:e=1∨e=-1)(z:ℂ)(a':0≤z.re): (V).comp (column S b e z)=(column Q a (-e) z).comp V:=by rw [← make_column,← make_column]; exact C.frameInterlaces (ticket a b e) (ticket_cont ..|>.measurable) (positive b e) _ (ticket_cont ..|>.measurable) (positive a (-e)) e c _ _ (crosses_at r S Q C e c p q h) _ (contr z a')
lemma looksHeat (u:ℝ≥0): (V).comp (S.E u)=(Q.E u).comp V:=by
 let z:ℂ:=((u:ℝ):ℂ)/2; have ht(e:ℝ): stroke e (u:ℝ) (↑(0:ℝ))=z:=by simp [stroke,z]
 let S₁:= (U 1 z); let S₂:= (U (-1) z); let Q₁:= column Q a (-1) z; let Q₂:=column Q a 1 z
 have hS:= eu_exp b 1 0 S p u r (by simp); have hQ:=eu_exp a (-1) 0 Q q u r.symm (by simp)
 rw [zero_smul,S.uZero,ht,ht] at hS; rw [zero_smul,Q.uZero,ht,ht,neg_neg] at hQ
 rw [show S.E u=S₁*S₂ from hS,show Q.E u=Q₁*Q₂ from hQ]
 have hv:0≤z.re:=by unfold z; simp only [Complex.div_ofNat_re,ofReal_re]; positivity -- tune
 have he:(V).comp S₁=Q₁.comp V:= ξshift r S Q C p q h _ (by simp) _ hv
 have k:(V).comp S₂=Q₂.comp V:=by
    have he:= ξshift r S Q C p q h (-1) (by simp) z hv; rw [neg_neg] at he; exact he
 change (V).comp (S₁.comp S₂)=(Q₁.comp Q₂).comp V; rw [←ContinuousLinearMap.comp_assoc, he, ContinuousLinearMap.comp_assoc,k, ←ContinuousLinearMap.comp_assoc]
end YM.Picket
